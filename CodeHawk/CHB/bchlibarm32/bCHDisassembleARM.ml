(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs, LLC

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:
 
   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.
  
   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
   ============================================================================= *)

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDataBlock
open BCHDoubleword
open BCHFloc
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummaryLibrary
open BCHJumpTable
open BCHLibTypes
open BCHLocation
open BCHMakeCallTargetInfo
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities

(* bchlibelf *)
open BCHELFHeader
open BCHELFTypes

(* bchlibarm32 *)
open BCHARMAssemblyBlock
open BCHARMAssemblyFunction
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMPseudocode
open BCHARMOpcodeRecords
open BCHARMTypes
open BCHDisassembleARMInstruction
open BCHDisassembleThumbInstruction

module H = Hashtbl


module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)

let x2p = xpr_formatter#pr_expr

let disassemble (base:doubleword_int) (displacement:int) (x:string) =
  let size = String.length x in  
  (* let opcode_monitor = new opcode_monitor_t base size in *)
  let mode = ref "arm" in

  let add_instruction position opcode bytes =
    let index = position + displacement in 
    let addr = base#add_int position in
    let instr = make_arm_assembly_instruction addr (!mode="arm") opcode bytes in
    begin
      !arm_assembly_instructions#set index instr;
      (* opcode_monitor#check_instruction instr *)
    end in
  let ch = system_info#get_string_stream x in

  let not_code_length nc =
    match nc with
    | JumpTable jt -> jt#get_length
    | DataBlock db -> db#get_length in

  let not_code_set_string nc s =
    match nc with
    | DataBlock db -> db#set_data_string s
    | _ -> () in

  let is_data_block (pos:int) =
    (!arm_assembly_instructions#at_index (displacement+pos))#is_non_code_block in

  let find_instr (testf: arm_assembly_instruction_int -> bool) offsets addr =
    List.fold_left
      (fun acc offset ->
        match acc with
        | Some _ -> acc
        | _ ->
           let caddr = addr#add_int offset in
           let cinstr = !arm_assembly_instructions#at_address caddr in
           if testf cinstr then
             Some cinstr
           else
             None) None offsets in

  (* format of LDR-based jumptable (in Thumb2):

     [2 bytes] CMP indexreg, maxcase
     [4 bytes] BHI.W default_address
     [2 bytes] ADR basereg, start_address
     [4 bytes] LDR.W PC, [basereg, indexreg, LSL #2]
   *)
  let cmptest reg instr =
    match instr#get_opcode with
    | Compare (_, rn, imm, _) ->
       rn#is_register && rn#get_register = reg && imm#is_immediate
    | _ -> false in

  let adrtest reg instr =
    match instr#get_opcode with
    | Adr (_, rd, _) -> rd#is_register && rd#get_register = reg
    | _ -> false in

  let is_ldr_jumptable (pos: int) (opcode: arm_opcode_t) =
    match opcode with
    | LoadRegister (_, dst, basereg, index, _, true)
         when dst#get_register = ARPC && index#is_register ->
       let addr = base#add_int pos in
       let cmpinstr = find_instr (cmptest index#get_register) [(-8)] addr in
       (match cmpinstr with
        | Some _ ->
           let adrinstr =
             find_instr (adrtest basereg#get_register) [(-2)] addr in
           (match adrinstr with
            | Some _ -> true
            | _ -> false)
        | _ -> false)
    | _ -> false in

  let create_ldr_jumptable ch (pos: int) (opcode: arm_opcode_t) =
    match opcode with
    | LoadRegister(_, dst, basereg, index, _, true)
         when dst#get_register = ARPC && index#is_register ->
       let addr = base#add_int pos in
       let cmpinstr = find_instr (cmptest index#get_register) [(-8)] addr in
       (match cmpinstr with
        | Some instr ->
           (match instr#get_opcode with
            | Compare (_, _, imm, _) when imm#is_immediate ->
               let size = imm#to_numerical#toInt in
               let adrinstr =
                 find_instr (adrtest basereg#get_register) [(-2)] addr in
               (match adrinstr with
                | Some ainstr ->
                   (match ainstr#get_opcode with
                    | Adr (_, _, imm) when imm#is_absolute_address ->
                       let jtaddr = imm#get_absolute_address in
                       let skips =
                         try
                           (jtaddr#subtract addr)#to_int - 4
                         with
                         | Invalid_argument s ->
                            raise
                              (BCH_failure
                                 (LBLOCK [
                                      STR "Error in create_ldr_jumptable. ";
                                      STR "jtaddr: ";
                                      jtaddr#toPretty;
                                      STR "; addr: ";
                                      addr#toPretty;
                                      STR ": ";
                                      STR s])) in
                       let _ = if skips > 0 then ch#skip_bytes skips in
                       let targets = ref [] in
                       let _ =
                         for i = 0 to size do
                           let tgt = ch#read_doubleword in
                           targets := (align_dw tgt 2) :: !targets
                         done in
                       let jt:jumptable_int =
                         make_jumptable
                           ~end_address:None
                           ~start_address:jtaddr
                           ~targets:(List.rev !targets) in
                       begin
                         system_info#add_jumptable jt;
                         !arm_assembly_instructions#set_jumptables [jt]
                       end
                    | _ -> ())
                | _ -> ())
            | _ -> ())
        | _ -> ())
    | _ -> () in

  let is_table_branch (pos: int) (opcode: arm_opcode_t) =
    let cmptest instr =
      match instr#get_opcode with Compare _ -> true | _ -> false in
    match opcode with
    | TableBranchByte (_, basereg, indexop, _)
      |TableBranchHalfword (_, basereg, indexop, _)
         when basereg#get_register = ARPC ->
       let addr = base#add_int pos in
       let cmpinstr = find_instr cmptest [(-4); (-6)] addr in
       let indexreg =
         if indexop#is_register then
           indexop#get_register
         else
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Register not recognized in table branch: ";
                     indexop#toPretty])) in
       (match cmpinstr with
        | Some instr ->
           (match instr#get_opcode with
            | Compare (_, rn, imm, _) when rn#is_register && imm#is_immediate ->
               rn#get_register = indexreg
            | _ -> false)
        | _ -> false)
    | _ -> false in

  let create_table_branch ch (pos: int) (opcode: arm_opcode_t) =
    let cmptest instr =
      match instr#get_opcode with Compare _ -> true | _ -> false in
    match opcode with
    | TableBranchByte (_, basereg, indexop, _)
      | TableBranchHalfword (_, basereg, indexop, _)
         when basereg#get_register = ARPC ->
       let addr = base#add_int pos in
       let cmpinstr = find_instr cmptest [(-4); (-6)] addr in
       (match cmpinstr with
        | Some instr ->
           (match instr#get_opcode with
            | Compare (_, _, imm, _) when imm#is_immediate ->
               let size = imm#to_numerical#toInt in
               let jtaddr = addr#add_int 4 in
               (match opcode with
                | TableBranchByte _ ->
                   let size = if size mod 2 = 0 then size + 1 else size in
                   let targets = ref [] in
                   let _ =
                     for i = 0 to size do
                       let byte = ch#read_byte in
                       let tgt = addr#add_int ((2 * byte) + 4) in
                       targets := tgt :: !targets
                     done in
                   let end_address = jtaddr#add_int (size + 1) in
                   let jt =
                     make_jumptable
                       ~end_address:(Some end_address)
                       ~start_address:jtaddr
                       ~targets:(List.rev !targets) in
                   begin
                     system_info#add_jumptable jt;
                     !arm_assembly_instructions#set_jumptables [jt]
                   end
                | TableBranchHalfword _ ->
                   let targets = ref [] in
                   let _ =
                     for i = 0 to size do
                       let hw = ch#read_ui16 in
                       let tgt = addr#add_int ((2 * hw) + 4) in
                       targets := tgt :: !targets
                     done in
                   let end_address = jtaddr#add_int (2 * (size + 1)) in
                   let jt =
                     make_jumptable
                       ~end_address:(Some end_address)
                       ~start_address:jtaddr
                       ~targets:(List.rev !targets) in
                   begin
                     system_info#add_jumptable jt;
                     !arm_assembly_instructions#set_jumptables[jt]
                   end
                | _ -> ())
            | _ -> ())
        | _ -> ())
    | _ -> () in

  let skip_data_block (pos:int) ch =
    let nonCodeBlock =
      (!arm_assembly_instructions#at_index (displacement+pos))#get_non_code_block in
    let len = not_code_length nonCodeBlock in
    let sdata = Bytes.make len ' ' in
    if pos + len <= String.length x then
      let _ = Bytes.blit (Bytes.of_string x) pos sdata 0 len in
      begin
        (if system_settings#collect_diagnostics then
           ch_diagnostics_log#add
             "skip data block"
             (LBLOCK [STR "pos: "; INT pos; STR "; length: "; INT len]));
        ch#skip_bytes len;
        not_code_set_string nonCodeBlock (Bytes.to_string sdata)
      end
    else
      ch_error_log#add
        "data block problem"
        (LBLOCK [
             STR "Data block at ";
             (base#add_int pos)#toPretty;
             STR " extends beyond end of section. Ignore"]) in
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "base: ";
           base#toPretty ;
           STR "; displacement: ";
           INT displacement;
           STR "; size: ";
           INT size]) in
  try
    let _ = pverbose [STR "disassemble thumb instructions"; NL] in
    begin
      while ch#pos + 2 < size do   (* <= causes problems at section end *)
        let prevPos = ch#pos in
        let iaddr = base#add_int ch#pos in
        let _ =
          let iaddrh = iaddr#to_hex_string in
          if system_settings#has_thumb then
            match system_info#get_arm_thumb_switch iaddrh with
            | Some "A" ->
               begin
                 mode := "arm";
                 chlog#add
                   "arm-thumb switch"
                   (LBLOCK [iaddr#toPretty; STR ": arm"])
               end
            | Some "T" ->
               begin
                 mode := "thumb";
                 chlog#add
                   "arm-thumb switch"
                   (LBLOCK [iaddr#toPretty; STR ": thumb"])
               end
            | _ -> () in
        try
          if is_data_block prevPos then
            skip_data_block prevPos ch
          else
            if system_settings#has_thumb && !mode = "thumb" then
              let instrbytes = ch#read_ui16 in
              let opcode =
                try
                  disassemble_thumb_instruction ch base instrbytes
                with
                | _ -> OpInvalid in
              let currentPos = ch#pos in
              let instrlen = currentPos - prevPos in
              let instrBytes = Bytes.make instrlen ' ' in
              let _ =
                try
                  Bytes.blit (Bytes.of_string x) prevPos instrBytes 0 instrlen
                with _ ->
                  raise
                    (BCH_failure
                       (LBLOCK [
                            STR "Error in Bytes.blit (Thumb): ";
                            STR "prevPos: ";
                            INT prevPos;
                            STR "; instrlen: ";
                            INT instrlen;
                            STR "; ch#pos: ";
                            INT ch#pos;
                            STR "; size: ";
                            INT size])) in
              let _ = add_instruction prevPos opcode (Bytes.to_string instrBytes) in
              let _ =
                pverbose [
                    (base#add_int prevPos)#toPretty;
                    STR "  ";
                    STR (arm_opcode_to_string opcode);
                    NL] in
              let _ =
                if is_table_branch prevPos opcode then
                  create_table_branch ch prevPos opcode in
              let _ =
                if is_ldr_jumptable prevPos opcode then
                  create_ldr_jumptable ch prevPos opcode in
              ()
            else
              let instrbytes = ch#read_doubleword in
              let opcode =
                  try
                    disassemble_arm_instruction ch base instrbytes
                  with
                  | BCH_failure p ->
                     begin
                       ch_error_log#add
                         "instruction disassembly error"
                         (LBLOCK [
                              (base#add_int ch#pos)#toPretty; STR ": "; p]);
                       NotRecognized ("error", instrbytes)
                     end
                  | _ -> OpInvalid in
              let currentPos = ch#pos in
              let instrLen = currentPos - prevPos in
              let instrBytes = Bytes.make instrLen ' ' in
              let _ =
                try
                  Bytes.blit (Bytes.of_string x) prevPos instrBytes 0 instrLen
                with _ ->
                  raise
                    (BCH_failure
                       (LBLOCK [
                            STR "Error in Bytes.blit (ARM): ";
                            STR "prevPos: ";
                            INT prevPos;
                            STR "; instrlen: ";
                            INT instrLen])) in
              let _ = add_instruction prevPos opcode (Bytes.to_string instrBytes) in
              ()
        with
        | BCH_failure p ->
           begin
             ch_error_log#add
               "disassembly"
               (LBLOCK [STR "failure in disassembling instruction at ";
                        (base#add_int prevPos)#toPretty;
                        STR " in mode ";
                        STR !mode]);
             raise (BCH_failure p)
           end
      done
    end
  with
  | BCH_failure p ->
     begin
       pr_debug [ STR "Error in disassembly: " ; p ] ;
       raise (BCH_failure p)
     end
  | IO.No_more_input ->
     begin
       pr_debug [ STR "Error in disassembly: No more input" ; NL ];
       raise IO.No_more_input
     end


let disassemble_arm_sections () =
  let xSections = elf_header#get_executable_sections in
  let (startOfCode,endOfCode) =
    if (List.length xSections) = 0 then
      raise (BCH_failure (STR "Executable does not have section headers"))
    else
      let headers =
        List.sort (fun (h1,_) (h2,_) -> h1#get_addr#compare h2#get_addr) xSections in
      let (lowest,_) = List.hd headers in
      let (highest,_) = List.hd (List.rev headers) in
      let _ =
        chlog#add
          "disassembly"
          (LBLOCK [
               pretty_print_list
                 headers
                 (fun (s,_) ->
                   LBLOCK [
                       STR s#get_section_name;
                       STR ":";
                       s#get_addr#toPretty;
                       STR " (";
                       s#get_size#toPretty;
                       STR ")"])
                 "[" " ; " "]" ]) in
      let startOfCode = lowest#get_addr in
      let endOfCode = highest#get_addr#add highest#get_size in
      (startOfCode, endOfCode) in
  let sizeOfCode =
    try
      endOfCode#subtract startOfCode
    with
    | Invalid_argument s ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in disassemble_arm_sections: sizeOfCode ";
                 STR "endOfCode: ";
                 endOfCode#toPretty;
                 STR "; startOfCode: ";
                 startOfCode#toPretty;
                 STR ": ";
                 STR s])) in
  let datablocks = system_info#get_data_blocks in
  let _ = initialize_arm_instructions sizeOfCode#to_int in 
  let _ = pverbose 
            [ STR "Create space for " ; sizeOfCode#toPretty ; STR " (" ;
	      INT sizeOfCode#to_int ; STR ") instructions" ; NL ; NL ] in
  let _ =
    initialize_arm_assembly_instructions
      sizeOfCode#to_int startOfCode datablocks in
  let _ =
    List.iter
      (fun (h, x) ->
        let displacement =
          try
            (h#get_addr#subtract startOfCode)#to_int
          with
          | Invalid_argument s ->
             raise
               (BCH_failure
                  (LBLOCK [
                       STR "Error in disassemble_arm_sections: displacement ";
                       STR "header address: ";
                       h#get_addr#toPretty;
                       STR "; startOfCode: ";
                       startOfCode#toPretty;
                       STR ": ";
                       STR s])) in
        disassemble h#get_addr displacement x) xSections in
  sizeOfCode

(* recognizes patterns of library function calls

     F B 0x99bc  00 c6 8f e2       ADR      R12, 0x99c4
         0x99c0  3a ca 8c e2       ADD      R12, R12, #237568
         0x99c4  bc f8 bc e5       LDR      PC, [R12], #2236

     F B 0x89b0  00 c6 8f e2       ADR      R12, 0x89b8
         0x89b4  0a ca 8c e2       ADD      R12, R12, #40960
         0x89b8  a4 fb bc e5       LDR      PC, [R12], #2980

     F B 0x2d8a8  00 c6 8f e2       ADR      R12, 0x2d8b0
         0x2d8ac  e3 ca 8c e2       ADD      R12, R12, #0xe3000
         0x2d8b0  68 f7 bc e5       LDR      PC, [R12], #1896

     F B 0x1f2ec  05 c6 8f e2       ADR      R12, 0x51f2f4
         0x1f2f0  42 ca 8c e2       ADD      R12, R12, #0x42000
         0x1f2f4  18 fd bc e5       LDR      PC, [R12], #3352

     F B 0x38f1c  02 c6 8f e2       ADR      R12, 0x238f24
         0x38f20  0b ca 8c e2       ADD      R12, R12, #0xb000
         0x38f24  e8 f0 bc e5       LDR      PC, [R12], #232

     F B 0x674    00 c6 8f e2       ADR      R12, 0x67c
         0x678    11 ca 8c e2       ADD      R12, R12, #0x11000
         0x67c    98 f9 bc e5       LDR      PC, [R12, #2456]!


 *)
let is_library_stub faddr =
  if elf_header#is_program_address faddr
     && elf_header#has_xsubstring faddr 12 then
    let bytestring =
      byte_string_to_printed_string (elf_header#get_xsubstring faddr 12) in
    let instrsegs = [
        "\\(..\\)c68fe2\\(..\\)ca8ce2\\(....\\)bce5"
      ] in
    List.exists (fun s ->
        let regex = Str.regexp s in
        Str.string_match regex bytestring 0) instrsegs
  else
    false


let set_library_stub_name faddr =
  if elf_header#is_program_address faddr then
    let to_int h = Int64.to_int (Int64.of_string h) in
    let bytestring =
      byte_string_to_printed_string (elf_header#get_xsubstring faddr 12) in
    let regex = Str.regexp "\\(..\\)c68fe2\\(..\\)ca8ce2\\(..\\)f\\(.\\)bce5" in
    if Str.string_match regex bytestring 0 then
      let imm8 = "0x" ^ (Str.matched_group 1 bytestring) in
      let imm8 = to_int imm8 in
      let offset1 = faddr#add_int ((arm_expand_imm 0 imm8) + 8) in
      let imm8 = "0x" ^ (Str.matched_group 2 bytestring) in
      let imm8 = to_int imm8 in
      let offset2 = arm_expand_imm 10 imm8 in
      let imm8 = Str.matched_group 3 bytestring in
      let imm4 = "0x" ^ (Str.matched_group 4 bytestring) in
      let imm12 = imm4 ^ imm8 in
      let imm12 = to_int imm12 in
      let addr = offset1#add_int (offset2 + imm12) in
      if functions_data#has_function_name addr then
        let fndata = functions_data#add_function faddr in
        begin
          fndata#add_name (functions_data#get_function addr)#get_function_name;
          fndata#set_library_stub;
          chlog#add
            "ELF library stub relocated"
            (LBLOCK [faddr#toPretty; STR ": "; STR fndata#get_function_name])
        end
      else
        chlog#add
          "no stub name found"
          (LBLOCK [faddr#toPretty; STR " -> "; addr#toPretty])
    else
      chlog#add "no string match for stub" faddr#toPretty
  else
    chlog#add "presumed library stub not a program address" faddr#toPretty


let get_so_target (tgtaddr:doubleword_int) (instr:arm_assembly_instruction_int) =
  if functions_data#has_function_name tgtaddr then
    let fndata = functions_data#get_function tgtaddr in
    if fndata#is_library_stub then
      Some fndata#get_function_name
    else if function_summary_library#has_so_function fndata#get_function_name then
      Some fndata#get_function_name
    else
      None
  else
    None


(* The Load Literal instruction loads a value from a location specified
   relative to the PC. It is common for these locations to be interspersed
   between the functions, that is, in the text section. This function marks
   these locations as addresses, so they are not disassembled.
 *)
let collect_data_references () =
  let _ = pverbose [STR "Collect data references"; NL] in
  let table = H.create 11 in
  let add (a:doubleword_int) (instr: arm_assembly_instruction_int) =
    let hxa = a#to_hex_string in
    let _ =
      if system_settings#collect_diagnostics then
        ch_diagnostics_log#add
          "load literals"
          (LBLOCK [
               instr#get_address#toPretty;
               STR "  ";
               instr#toPretty;
               STR ": ";
               a#toPretty]) in
    let entry =
      if H.mem table hxa then
        H.find table hxa
      else
        [] in
    H.replace table hxa (instr::entry) in
  begin
    !arm_assembly_instructions#itera
      (fun va instr ->
        match instr#get_opcode with
        | LoadRegister (_, _, _, _, mem, _) when mem#is_pc_relative_address ->
           let pcoffset = if instr#is_arm32 then 8 else 4 in
           let a = mem#get_pc_relative_address va pcoffset in
           if elf_header#is_program_address a then
             add a instr
           else
             ch_error_log#add
               "LDR from non-code-address"
               (LBLOCK [va#toPretty; STR " refers to "; a#toPretty])
        | VLoadRegister (_, vd, _, mem) when mem#is_pc_relative_address ->
           let pcoffset = if instr#is_arm32 then 8 else 4 in
           let a = mem#get_pc_relative_address va pcoffset in
           if elf_header#is_program_address a then
             begin
               add a instr;
               if (vd#get_size = 8) then add (a#add_int 4) instr;
             end
           else
             ch_error_log#add
               "VLDR from non-code-address"
               (LBLOCK [va#toPretty; STR " refers to "; a#toPretty])
        | _ -> ());
    H.fold (fun k v a -> (k,v)::a) table []
  end

(* can be used before functions have been constructed *)
let is_nr_call_instruction (instr:arm_assembly_instruction_int) =
  match instr#get_opcode with
  | BranchLink (ACCAlways, tgt)
    | BranchLinkExchange (ACCAlways, tgt) when tgt#is_absolute_address ->
     let tgtaddr = tgt#get_absolute_address in
     ((functions_data#is_function_entry_point tgtaddr)
      && (functions_data#get_function tgtaddr)#is_non_returning)
  | _ -> false

let collect_function_entry_points () =
  let _ = pverbose [STR "Collect function entry points"; NL] in
  let addresses = new DoublewordCollections.set_t in
  begin
    !arm_assembly_instructions#itera
      (fun va instr ->
        match instr#get_opcode with
        | BranchLink (_,op)
          | BranchLinkExchange (_,op) when op#is_absolute_address ->
           (match get_so_target op#get_absolute_address instr with
            | Some sym ->
               (functions_data#add_function op#get_absolute_address)#add_name sym
            | _ -> addresses#add op#get_absolute_address)
        | _ -> ()) ;
    addresses#toList
  end

let set_block_boundaries () =
  let _ = pverbose [STR "Set block boundaries"; NL] in
  let set_block_entry a =
    try
      (!arm_assembly_instructions#at_address a)#set_block_entry
    with
    | BCH_failure p ->
       begin
         ch_error_log#add "set-block-entry" p;
         raise
           (BCH_failure
              (LBLOCK [STR "Error in set-block-entry: "; p]))
       end in
  let feps = functions_data#get_function_entry_points in
  let datablocks = system_info#get_data_blocks in
  begin
    (* -------------------------------- record function entry points -- *)
    List.iter
      (fun fe ->
        try
          set_block_entry fe
        with
        | BCH_failure _ ->
           chlog#add
             "disassembly"
             (LBLOCK [
                  STR "function entry point incorrect: ";
                  fe#toPretty])) feps;

    (* -------------------------------- record end of data blocks -- *)
    List.iter
      (fun db ->
        try
          set_block_entry db#get_end_address
        with
        | BCH_failure _ ->
           chlog#add
             "disassembly"
             (LBLOCK [
                  STR "data block end address incorrect: ";
                  db#get_end_address#toPretty])) datablocks;

    (* --------------------------------------- record jumptables -- *)
    List.iter
      (fun jt ->
        try
          List.iter set_block_entry jt#get_all_targets
        with
        | BCH_failure p ->
           ch_error_log#add
             "disassembly"
             (LBLOCK [
                  STR "jump table target address incorrect: ";
                  jt#toPretty
                    ~is_function_entry_point:(fun _ -> false)
                    ~get_opt_function_name:(fun _ -> None)]))
      system_info#get_jumptables;

    (* ------------------- record targets of unconditional jumps -- *)
    !arm_assembly_instructions#itera
      (fun va instr ->
        try
          (match instr#get_opcode with
           | Branch (_, op, _)
             | BranchExchange (_,op)
             | CompareBranchNonzero (_, op)
             | CompareBranchZero (_, op) ->
              if op#is_absolute_address then
                let jmpaddr = op#get_absolute_address in
                set_block_entry jmpaddr;
              else
                ()

           | BranchLink _ | BranchLinkExchange _
                when is_nr_call_instruction instr ->
              set_block_entry (va#add_int 4)

           | _ -> ())
        with
        | BCH_failure p ->
           chlog#add
             "disassembly"
             (LBLOCK [
                  STR "assembly instruction creates incorrect block entry: ";
                  instr#toPretty;
                  STR ": ";
                  p]));

    (* -------------------------- incorporate jump successors -- *)
    !arm_assembly_instructions#itera
      (fun va _ ->
        match system_info#get_successors va with
        | [] -> ()
        | l ->
           begin
             List.iter set_block_entry l;
             set_block_entry (va#add_int 4)
           end);

    (* --------------- add block entries due to previous block-ending -- *)
    !arm_assembly_instructions#itera
      (fun va instr ->
        let opcode = instr#get_opcode in
        let is_block_ending =
          match opcode with
          | Pop (_,_,rl,_) -> rl#includes_pc
          | Branch _ | BranchExchange _ -> true
          | CompareBranchZero _ | CompareBranchNonzero _ -> true
          | LoadRegister (_, dst, _, _, _, _)
               when dst#is_register && dst#get_register = ARPC -> true
          | LoadMultipleDecrementBefore (_,_,_,rl,_) when rl#includes_pc -> true
          | _ -> false in
        if is_block_ending
           && !arm_assembly_instructions#has_next_valid_instruction va then
          set_block_entry
            (!arm_assembly_instructions#get_next_valid_instruction_address va)
        else
          ())
  end

let get_successors (faddr:doubleword_int) (iaddr:doubleword_int) =
  if system_info#is_nonreturning_call faddr iaddr then
    []
  else
    let instr =
      try
        !arm_assembly_instructions#at_address iaddr
      with
      | BCH_failure p ->
         begin
           ch_error_log#add "get-successors" p;
           raise
             (BCH_failure
                (LBLOCK [STR "Error in get-successors: "; p]))
         end in
    let opcode = instr#get_opcode in
    let next () =
      if !arm_assembly_instructions#has_next_valid_instruction iaddr then
        [!arm_assembly_instructions#get_next_valid_instruction_address iaddr]
      else
        begin
          (if system_settings#collect_diagnostics then
             ch_diagnostics_log#add
               "disassembly"
               (LBLOCK [
                    STR "Next instruction for ";
                    iaddr#toPretty ;
                    STR " ";
                    instr#toPretty;
                    STR " was not found"]));
          []
        end in
    let successors =
      match system_info#get_successors iaddr with
      | [] ->
         (match opcode with
          | Pop (ACCAlways,_,rl,tw) when rl#includes_pc -> []
          | Branch (ACCAlways, op, _)
            | BranchExchange (ACCAlways,op)
               when op#is_register && op#get_register == ARLR ->
             []
          | Branch (ACCAlways, op, _)
            | BranchExchange (ACCAlways,op) when op#is_absolute_address ->
             [op#get_absolute_address]
          | Branch (_,op, _)
            | BranchExchange (_, op)
               when op#is_register && op#get_register == ARLR ->
             (next ())
          | Branch (_,op, _)
            | BranchExchange (_, op)
            | CompareBranchZero (_, op)
            | CompareBranchNonzero (_, op) when op#is_absolute_address ->
             (next ()) @ [op#get_absolute_address]
          | TableBranchByte _
            | TableBranchHalfword _
               when system_info#has_jumptable (iaddr#add_int 4) ->
             (system_info#get_jumptable (iaddr#add_int 4))#get_all_targets
          | LoadRegister _
               when system_info#has_jumptable (iaddr#add_int 4) ->
             (system_info#get_jumptable (iaddr#add_int 4))#get_all_targets
          | _ -> (next ()))
      | l -> l in
    List.map
      (fun va -> (make_location {loc_faddr = faddr; loc_iaddr = va})#ci)
      (List.filter
         (fun va ->
           if !arm_assembly_instructions#is_code_address va then
             true
           else
             begin
               (if system_settings#collect_diagnostics then
                  ch_diagnostics_log#add
                    "disassembly"
                    (LBLOCK [
                         STR "Successor of ";
                         va#toPretty;
                         STR " is not a valid code address"]));
               false
             end) successors)

let trace_block (faddr:doubleword_int) (baddr:doubleword_int) =
  let get_instr a =
    try
      !arm_assembly_instructions#at_address a
    with
    | BCH_failure p ->
       begin
         ch_error_log#add "trace-block" p;
         raise
           (BCH_failure
              (LBLOCK [STR "Error in trace-block: "; p]))
       end in
  let get_next_instr_address =
    !arm_assembly_instructions#get_next_valid_instruction_address in

  let is_tail_call floc va =
    let instr = get_instr va in
    match instr#get_opcode with
    | Branch (ACCAlways, tgt, _) ->
       tgt#is_absolute_address
          && functions_data#is_function_entry_point tgt#get_absolute_address
    | _ -> false in

  let rec find_last_instruction (va:doubleword_int) (prev:doubleword_int) =
    let instr = get_instr va in
    let floc = get_floc (make_location { loc_faddr = faddr; loc_iaddr = va }) in
    let _ = floc#set_instruction_bytes instr#get_instruction_bytes in
    if va#equal wordzero then
      (Some [],prev,[])
    else if instr#is_block_entry then
      (None,prev,[])
    else if is_nr_call_instruction instr then
      let _ =
        chlog#add
          "non-returning call" (LBLOCK [faddr#toPretty; STR " "; va#toPretty]) in
      (Some [], va, [])
    else if is_tail_call floc va then
      let _ =
        if system_settings#collect_diagnostics then
          ch_diagnostics_log#add
            "tail call"
            (LBLOCK [
                 faddr#toPretty;
                 STR " ";
                 va#toPretty;
                 STR "  ";
                 instr#toPretty]) in
      (Some [], va, [])
    else if
      (match instr#get_opcode with
       | PermanentlyUndefined _ -> true | _ -> false) then
      let _ =
        chlog#add
          "permanently undefined instruction"
          (LBLOCK [faddr#toPretty; STR "  "; va#toPretty]) in
      (Some [], va, [])
    else if floc#has_call_target && floc#get_call_target#is_nonreturning then
      let _ = chlog#add "non-returning" floc#l#toPretty in
      (Some [],va,[])
    else if !arm_assembly_instructions#has_next_valid_instruction va then
      find_last_instruction (get_next_instr_address va) va
    else (None,va,[]) in

  let (succ, lastaddr, inlinedblocks) =
    if is_nr_call_instruction (get_instr baddr) then
      (Some [] ,baddr, [])
    else if
      (match (get_instr baddr)#get_opcode with
       | PermanentlyUndefined _ -> true | _ -> false) then
      (Some [], baddr, [])
    else if !arm_assembly_instructions#has_next_valid_instruction baddr then
      let floc = get_floc (make_location {loc_faddr = faddr; loc_iaddr = baddr }) in
      let _ = floc#set_instruction_bytes (get_instr baddr)#get_instruction_bytes in
      find_last_instruction (get_next_instr_address baddr) baddr
    else (None,baddr,[]) in
  let successors = match succ with
    | Some s -> s
    | _ -> get_successors faddr lastaddr in
  (inlinedblocks, make_arm_assembly_block faddr baddr lastaddr successors)

let trace_function (faddr:doubleword_int) =
  let _ = pverbose [STR "Trace function "; faddr#toPretty; NL] in
  let workset = new DoublewordCollections.set_t in
  let doneset = new DoublewordCollections.set_t in
  let set_block_entry a =
    (!arm_assembly_instructions#at_address a)#set_block_entry in
  let get_iaddr s = (ctxt_string_to_location faddr s)#i in
  let add_to_workset l =
    List.iter (fun a -> if doneset#has a then () else workset#add a) l in
  let blocks = ref [] in
  let rec add_block (blockentry:doubleword_int) =
    let (inlinedblocks,block) = trace_block faddr blockentry in
    let blocksuccessors = block#get_successors in
    begin
      set_block_entry blockentry;
      workset#remove blockentry;
      doneset#add blockentry;
      blocks := (block :: inlinedblocks) @ !blocks;
      add_to_workset (List.map get_iaddr blocksuccessors);
      match workset#choose with Some a -> add_block a | _ -> ()
    end in
  let _ = add_block faddr in
  let blocklist =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_context_string b2#get_context_string) !blocks in
  let successors =
    List.fold_left
      (fun acc b ->
        let src = b#get_context_string in
        (List.map (fun tgt -> (src,tgt)) b#get_successors) @ acc) [] blocklist in
  make_arm_assembly_function faddr blocklist successors

let construct_assembly_function (count:int) (faddr:doubleword_int) =
      try
        if !arm_assembly_instructions#is_code_address faddr then
          let fn = trace_function faddr in
          arm_assembly_functions#add_function fn
      with
      | BCH_failure p ->
         begin
           ch_error_log#add
             "construct assembly function"
             (LBLOCK [ faddr#toPretty ; STR ": " ; p ]);
           raise
             (BCH_failure
                (LBLOCK [ STR "Error in constructing function " ;
                          faddr#toPretty ; STR ": " ; p ]))
         end


let record_call_targets_arm () =
  let _ = pverbose [STR "Record call targets"; NL] in
  arm_assembly_functions#itera
    (fun faddr f ->
      let finfo = get_function_info faddr in
      begin
        f#iteri
          (fun _ ctxtiaddr instr ->
            match instr#get_opcode with
            | BranchLink (_, op)
              | BranchLinkExchange (_, op) ->
               if finfo#has_call_target ctxtiaddr
                  && not (finfo#get_call_target ctxtiaddr)#is_unknown then
                 let loc = ctxt_string_to_location faddr ctxtiaddr in
                 let floc = get_floc loc in
                 floc#update_call_target
               else if op#is_absolute_address then
                 begin
                   match get_so_target op#get_absolute_address instr with
                   | Some tgt ->
                      finfo#set_call_target ctxtiaddr (mk_so_target tgt)
                   | _ ->
                      finfo#set_call_target
                        ctxtiaddr (mk_app_target op#get_absolute_address)
                 end
               else
                 ()
            | Branch (_, tgt, _) when
                   tgt#is_absolute_address
                   && functions_data#is_function_entry_point
                        tgt#get_absolute_address ->
               if finfo#has_call_target ctxtiaddr
                  && not (finfo#get_call_target ctxtiaddr)#is_unknown then
                 let loc = ctxt_string_to_location faddr ctxtiaddr in
                 let floc = get_floc loc in
                 floc#update_call_target
               else
                 begin
                   match get_so_target tgt#get_absolute_address instr with
                   | Some tgt ->
                      finfo#set_call_target ctxtiaddr (mk_so_target tgt)
                   | _ ->
                      finfo#set_call_target
                        ctxtiaddr (mk_app_target tgt#get_absolute_address)
                 end
            | _ -> ())
      end)

(* ---------------------------------------------------------------------
   associate conditional jump instructions with the closest instruction
   (within the same basic block) that sets the flags
   ---------------------------------------------------------------------- *)
let associate_condition_code_users () =
  let _ = pverbose [STR "Associate condition code users"; NL] in
  let set_condition
        (flags_used: arm_cc_flag_t list)
        (faddr: doubleword_int)
        (ctxtiaddr:ctxt_iaddress_t)
        (block: arm_assembly_block_int) =
    let finfo = get_function_info faddr in
    let loc = ctxt_string_to_location faddr ctxtiaddr in
    let revInstrs: arm_assembly_instruction_int list =
      block#get_instructions_rev ~high:loc#i () in

    (* remove the conditional instruction itself *)
    let revInstrs: arm_assembly_instruction_int list =
      match revInstrs with
      | h::tl -> tl
      | [] -> [] in
    let rec set l =
      match l with
      | [] ->
	  disassembly_log#add "cc user without setter"
	    (LBLOCK [loc#toPretty ; STR ": " ;
		     (!arm_assembly_instructions#at_address loc#i)#toPretty ])
      | instr :: tl ->
	match get_arm_flags_set instr#get_opcode with
	| [] -> set tl
	| flags_set ->
	  if List.for_all (fun fUsed -> List.mem fUsed flags_set) flags_used then
             let iloc = ctxt_string_to_location faddr ctxtiaddr in
             let instrctxt = (make_i_location iloc instr#get_address)#ci in
	    finfo#connect_cc_user ctxtiaddr instrctxt in
    set revInstrs in
  arm_assembly_functions#itera
    (fun faddr f ->
      f#iter
	(fun block ->
	  block#itera
	    (fun iaddr instr ->
	      match get_arm_flags_used instr#get_opcode with
	      | [] -> ()
	      | flags -> set_condition flags faddr iaddr block) ) )


(* Return true if the two instructions encode the assignment of a
   predicate to a variable.

   Pattern:
   ITE  c                                   ITE  c
   MOV  Rx, #0x0   ->  Rx := !c     or      MOV  Rx, #0x1   ->  Rx := c
   MOV  Rx, #0x1                            MOV  Rx, #0x0
 *)
let is_ite_predicate_assignment thenfloc theninstr elsefloc elseinstr =
  let iszero op floc =
    match op#to_expr floc with
    | XConst (IntConst n) -> n#equal numerical_zero
    | _ -> false in
  let isone op floc =
    match op#to_expr floc with
    | XConst (IntConst n) -> n#equal numerical_one
    | _ -> false in
  match (theninstr#get_opcode, elseinstr#get_opcode) with
  | (Move (_, _, tr, thenop, _, _), Move (_, _, er, elseop, _, _)) ->
     if tr#is_register && er#is_register then
       if tr#get_register = er#get_register then
         isone thenop thenfloc && iszero elseop elsefloc
       else
         false
     else
       false
  | _ -> false


(* Return the lhs to which the predicate expression should be assigned *)
let get_ite_predicate_dstop thenfloc theninstr elsefloc elseinstr =
  if is_ite_predicate_assignment thenfloc theninstr elsefloc elseinstr then
    match theninstr#get_opcode with
    | Move(_, _, r, _, _, _) -> r
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Internal error in get_ite_predicate_dst"]))
  else
    raise
      (BCH_failure
         (LBLOCK [STR "Internal error in get_ite_predicate_dst"]))


let aggregate_ite () =
  let _ = pverbose [STR "Aggregate ITE conditions"; NL] in
  arm_assembly_functions#itera
    (fun faddr f ->
      f#iter
        (fun block ->
          block#itera
            (fun ciaddr instr ->
              let loc = ctxt_string_to_location faddr ciaddr in
              let iaddr = loc#i in
              let itefloc = get_floc loc in
              match instr#get_opcode with
              | IfThen (c, xyz) when xyz = "E" ->
                 let thenaddr = iaddr#add_int 2 in
                 let elseaddr = iaddr#add_int 4 in
                 let theninstr = !arm_assembly_instructions#at_address thenaddr in
                 let elseinstr = !arm_assembly_instructions#at_address elseaddr in
                 let thenfloc = get_i_floc itefloc thenaddr in
                 let elsefloc = get_i_floc itefloc elseaddr in
                 if is_ite_predicate_assignment
                      thenfloc theninstr elsefloc elseinstr then
                   let dstop =
                     get_ite_predicate_dstop
                       thenfloc theninstr elsefloc elseinstr in
                   begin
                     (if system_settings#collect_diagnostics then
                        ch_diagnostics_log#add
                          "aggregate ite"
                          (LBLOCK [STR ciaddr; STR ": "; instr#toPretty]));
                     instr#set_aggregate dstop [thenaddr; elseaddr];
                     theninstr#set_subsumed_by iaddr;
                     elseinstr#set_subsumed_by iaddr
                   end
              | _ -> ())))

let construct_functions_arm () =
  let _ = pverbose [STR "Construction functions"; NL] in
  let _ =
    system_info#initialize_function_entry_points collect_function_entry_points in
  let dataAddrs = collect_data_references () in
  let addrs = List.map (fun (a,_) -> string_to_doubleword a) dataAddrs in
  let _ = set_data_references addrs in
  let _ = set_block_boundaries () in
  let fnentrypoints = functions_data#get_function_entry_points in
  let count = ref 0 in
  begin
    List.iter
      (fun faddr ->
        let default () =
          try
            begin
              count := !count + 1;
              construct_assembly_function !count faddr
            end
          with
          | BCH_failure p ->
             ch_error_log#add
               "construct functions"
               (LBLOCK [STR "Function "; faddr#toPretty; STR ": "; p]) in
        if functions_data#is_function_entry_point faddr then
          let fndata = functions_data#get_function faddr in
          if fndata#is_library_stub then
            ()
          else if fndata#has_name then
            if is_library_stub faddr then
              begin
                fndata#set_library_stub;
                chlog#add
                  "ELF library stub"
                  (LBLOCK [faddr#toPretty; STR ": "; STR fndata#get_function_name])
              end
            else
              default ()
          else if is_library_stub faddr then
            begin
              fndata#set_library_stub;
              set_library_stub_name faddr
            end
          else
            default ()
        else
          ch_error_log#add
            "no function found"
            (LBLOCK [STR "construct functions: "; faddr#toPretty])
      ) fnentrypoints ;
    List.iter (fun faddr ->
        begin
          count := !count + 1;
          construct_assembly_function !count faddr
        end) arm_assembly_functions#add_functions_by_preamble;
    record_call_targets_arm ();
    associate_condition_code_users ();
    aggregate_ite ()
  end

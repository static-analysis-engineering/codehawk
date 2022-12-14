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
open BCHARMInstructionAggregate
open BCHARMJumptable
open BCHARMPseudocode
open BCHARMOpcodeRecords
open BCHARMTypes
open BCHConstructARMFunction
open BCHDisassembleARMInstruction
open BCHDisassembleThumbInstruction

module H = Hashtbl
module TR = CHTraceResult


module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


let x2p = xpr_formatter#pr_expr


let disassemble_arm_section
      (sectionbase: doubleword_int) (sectionbytes: string) =
  let sectionsize = String.length sectionbytes in
  let mode = ref "arm" in

  let add_instruction
        (iaddr: doubleword_int) (opcode: arm_opcode_t) (bytes: string) =
    let instr =
      make_arm_assembly_instruction iaddr (!mode="arm") opcode bytes in
    begin
      set_arm_assembly_instruction instr;
      instr
    end in
  let ch = make_pushback_stream sectionbytes in

  let not_code_length nc =
    match nc with
    | JumpTable jt -> jt#get_length
    | DataBlock db -> db#get_length in

  let not_code_set_string nc s =
    match nc with
    | DataBlock db -> db#set_data_string s
    | _ -> () in

  let is_data_block (iaddr: doubleword_int) =
    TR.to_bool
      (fun instr -> instr#is_non_code_block)
      (get_arm_assembly_instruction iaddr) in

  let skip_data_block (pos: int) ch =
    let iaddr = sectionbase#add_int pos in
    log_titer
      (mk_tracelog_spec
         ~tag:"disassembly" ("skip_data_block:" ^ iaddr#to_hex_string))
      (fun instr ->
        let nonCodeBlock = instr#get_non_code_block in
        let dblen = not_code_length nonCodeBlock in
        if pos + dblen <= sectionsize then
          let blockbytes =
            try
              ch#sub pos dblen
            with
            | BCH_failure p ->
               begin
                 ch_error_log#add
                   "disassembly:skip data_block"
                   (LBLOCK [STR "pos: "; INT pos; STR "; dblen: "; INT dblen]);
                 ""
               end in
          begin
            (if collect_diagnostics () then
               ch_diagnostics_log#add
                 "skip data block"
                 (LBLOCK [STR "pos: "; INT pos; STR "; length: "; INT dblen]));
            ch#skip_bytes dblen;
            not_code_set_string nonCodeBlock blockbytes
          end
        else
          ch_error_log#add
            "data block problem"
            (LBLOCK [
                 STR "Data block at ";
                 (sectionbase#add_int pos)#toPretty;
                 STR " extends beyond end of section. Ignore"]))
      (get_arm_assembly_instruction iaddr) in

  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "sectionbase: ";
           sectionbase#toPretty ;
           STR "; size: ";
           INT sectionsize]) in
  try
    let _ = pverbose [STR "disassemble thumb instructions"; NL] in
    begin
      while ch#pos + 2 < sectionsize do   (* <= causes problems at section end *)
        let prevPos = ch#pos in
        let iaddr = sectionbase#add_int ch#pos in
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
          if is_data_block iaddr then
            skip_data_block prevPos ch
          else
            if system_settings#has_thumb && !mode = "thumb" then
              (* Thumb mode *)
              let instrbytes = ch#read_ui16 in
              let opcode =
                try
                  disassemble_thumb_instruction ch iaddr instrbytes
                with
                | _ -> OpInvalid in
              let currentPos = ch#pos in
              let instrlen = currentPos - prevPos in
              let instrbytes = ch#sub prevPos instrlen in
              let instr = add_instruction iaddr opcode instrbytes in
              let optagg = identify_arm_aggregate ch instr in
              match optagg with
              | Some agg -> set_aggregate iaddr agg
              | _ -> ()

            else
              (* ARM mode *)
              let instrbytes = ch#read_doubleword in
              let opcode =
                  try
                    disassemble_arm_instruction ch iaddr instrbytes
                  with
                  | BCH_failure p ->
                     begin
                       ch_error_log#add
                         "instruction disassembly error"
                         (LBLOCK [iaddr#toPretty; STR ": "; p]);
                       NotRecognized ("error", instrbytes)
                     end
                  | _ -> OpInvalid in
              let currentPos = ch#pos in
              let instrlen = currentPos - prevPos in
              let instrBytes = ch#sub prevPos instrlen in
              let _ = add_instruction iaddr opcode instrBytes in
              ()
        with
        | BCH_failure p ->
           begin
             ch_error_log#add
               "disassembly"
               (LBLOCK [
                    STR "failure in disassembling instruction at ";
                    iaddr#toPretty;
                    STR " in mode ";
                    STR !mode]);
             raise (BCH_failure p)
           end
      done
    end
  with
  | BCH_failure p ->
     begin
       pr_debug [STR "Error in disassembly: "; p];
       raise (BCH_failure p)
     end
  | IO.No_more_input ->
     begin
       pr_debug [STR "Error in disassembly: No more input"; NL];
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
    fail_tvalue
      (trerror_record
         (LBLOCK [
              STR "disassemble_arm_sections:sizeOfCode: ";
              startOfCode#toPretty;
              STR ", ";
              endOfCode#toPretty]))
      (endOfCode#subtract startOfCode) in
  let datablocks = system_info#get_data_blocks in
  let _ = initialize_arm_instructions sizeOfCode#to_int in 
  let _ =
    pverbose [
        STR "Create space for ";
        sizeOfCode#toPretty;
        STR " (";
	INT sizeOfCode#to_int;
        STR ") instructions";
        NL;
        NL] in
  let _ =
    initialize_arm_assembly_instructions
      sizeOfCode#to_int startOfCode datablocks in
  let _ =
    List.iter
      (fun (h, x) -> disassemble_arm_section h#get_addr x) xSections in
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
      if collect_diagnostics () then
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
  let set_inlined_call (a: doubleword_int) =
    log_titer
      (mk_tracelog_spec
         ~tag:"set_block_boundaries"
         ("set_inlined_call:" ^ a#to_hex_string))
      (fun instr -> instr#set_inlined_call)
      (get_arm_assembly_instruction a) in
  let set_block_entry a =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "set_block_boundaries:set_block_entry: "; a#toPretty]))
        (get_arm_assembly_instruction a) in
    instr#set_block_entry in
  let get_iftxf iaddr =   (* if then x follow *)
    let get_next_iaddr = get_next_valid_instruction_address in
    match TR.to_option (get_next_iaddr iaddr) with
    | None -> None
    | Some va1 ->
       (match TR.to_option (get_next_iaddr va1) with
        | None -> None
        | Some va2 ->
           (match TR.to_option (get_next_iaddr va2) with
            | None -> None
            | Some va3 -> Some (va1, va2, va3))) in

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

           (* Thumb-2 IfThen construct:
              va0: ITT c
              va1: if c .. .
              va2: if   c ...
              va3: next instruction (fall-through)
            *)
           | IfThen (c, xyz) when xyz = "T" ->
              (match get_iftxf va with
               | Some (va1, va2, va3) ->
                  log_titer
                    (mk_tracelog_spec
                       ~tag:"set_block_boundaries"
                       ("IfThen:" ^ va1#to_hex_string))
                    (fun instr1 ->
                      log_titer
                        (mk_tracelog_spec
                           ~tag:"set_block_boundaries"
                           ("IfThen:" ^ va2#to_hex_string))
                        (fun instr2 ->
                          begin
                            (if collect_diagnostics () then
                               ch_diagnostics_log#add
                                 "ITT block"
                                 (LBLOCK [va1#toPretty; STR ", "; va3#toPretty]));
                            set_block_entry va1;
                            set_block_entry va3;
                            instr#set_block_condition;
                            instr1#set_condition_covered_by va;
                            instr2#set_condition_covered_by va
                          end)
                        (get_arm_assembly_instruction va2))
                    (get_arm_assembly_instruction va1)
               | _ ->
                  ch_error_log#add
                    "set_block_boundaries:IfThen"
                    (LBLOCK [STR "Instructions not found at "; va#toPretty]))

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
          | Pop (_, _, rl, _) -> rl#includes_pc
          | Move (_, _, dst, _, _, _) ->
             dst#is_register && dst#get_register = ARPC
          | Branch _ | BranchExchange _ -> true
          | CompareBranchZero _ | CompareBranchNonzero _ -> true
          | LoadRegister (_, dst, _, _, _, _)
               when dst#is_register && dst#get_register = ARPC -> true
          | LoadMultipleDecrementBefore (_, _, _, rl, _)
            | LoadMultipleDecrementAfter (_, _, _, rl, _)
            | LoadMultipleIncrementBefore (_, _, _, rl, _)
            | LoadMultipleIncrementAfter (_, _, _, rl, _) when rl#includes_pc ->
             true
          | BranchLink (_, op) | BranchLinkExchange (_, op)
               when op#is_absolute_address
                    && system_info#is_inlined_function op#get_absolute_address ->
             begin
               chlog#add "add inlined call" va#toPretty;
               set_inlined_call va;
               true
             end
          | _ -> false in
        if is_block_ending && has_next_valid_instruction va then
          let nextva =
            fail_tvalue
              (trerror_record
                 (LBLOCK [STR "Internal error in set_block_boundaries"]))
              (get_next_valid_instruction_address va) in
          set_block_entry nextva
        else
          ())
  end


let construct_assembly_function (count:int) (faddr:doubleword_int) =
      try
        if !arm_assembly_instructions#is_code_address faddr then
          let fn = construct_arm_assembly_function faddr in
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
         log_titer
           (mk_tracelog_spec
              ~tag:"associate_condition_code_users"
              ("set:" ^ loc#i#to_hex_string))
           (fun instr ->
	     disassembly_log#add
               "cc user without setter"
	       (LBLOCK [loc#toPretty; STR ": " ; instr#toPretty]))
	   (get_arm_assembly_instruction loc#i)
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
	      | flags -> set_condition flags faddr iaddr block)))


let construct_functions_arm () =
  let _ = pverbose [STR "Construction functions"; NL] in
  let _ =
    system_info#initialize_function_entry_points collect_function_entry_points in
  let dataAddrs = collect_data_references () in
  let addrs =
    List.fold_left (fun acc (a, _) ->
        TR.tfold_default
          (fun a -> a::acc)
          acc
          (string_to_doubleword a)) [] dataAddrs in
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
    pverbose [STR "Construction functions: Done"; NL]
  end

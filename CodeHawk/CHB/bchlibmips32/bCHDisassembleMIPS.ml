(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open XprToPretty
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDataBlock
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation
open BCHMakeCallTargetInfo
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings

(* bchlibelf *)
open BCHELFHeader

(* bchlibmips32 *)
open BCHMIPSAssemblyBlock
open BCHMIPSAssemblyFunction
open BCHMIPSAssemblyFunctions
open BCHMIPSAssemblyInstruction
open BCHMIPSAssemblyInstructions

open BCHDisassembleMIPSInstruction
open BCHMIPSOperand
open BCHMIPSTypes
open BCHMIPSDisassemblyUtils

module TR = CHTraceResult

let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("DisassembleMIPS:" ^ tag) msg


(* Unsafe call to string_to_doubleword; may raise Invalid_argument *)
let constant_string_to_doubleword (s: string) =
  TR.tget_ok (string_to_doubleword s)


(* --------------------------------------------------------------------------
 * Constants used:
 * datablock_threshold:
 *       the minimum number of bad instructions to trigger creation
 *       of a data block (5)
 * -------------------------------------------------------------------------- *)

let datablock_threshold = 5

module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


let x2p = xpr_formatter#pr_expr


class opcode_monitor_t (base:doubleword_int) (size:int) =
object (self)

  val mutable datablocks = []
  val mutable statusvalid = true
  val mutable refaddress = wordzero

  method check_instruction (instr:mips_assembly_instruction_int) =
    match instr#get_opcode with
    | OpInvalid when statusvalid ->
       begin
         statusvalid <- false ;
         refaddress <- instr#get_address
       end
    | _ when (not statusvalid) ->
       let addr = instr#get_address in
       let badinstrcount = (TR.tget_ok (addr#subtract_to_int refaddress)) /  4 in
       let _ =
         if badinstrcount > datablock_threshold then self#add_data_block addr in
       statusvalid <- true
    | _ -> ()

  method private add_data_block addr =
    let db = TR.tget_ok (make_data_block refaddress addr "") in
    begin
      chlog#add
        "datablock"
        (LBLOCK [refaddress#toPretty; STR " - "; addr#toPretty]);
      system_info#add_data_block db;
      datablocks <- db :: datablocks
    end

  method get_data_blocks =
    let _ =
      if not statusvalid then
        self#add_data_block (base#add_int size) in
    datablocks

end


let disassemble (base:doubleword_int) (displacement:int) (x:string) =
  let size = String.length x in
  let opcode_monitor = new opcode_monitor_t base size in
  let add_instruction position opcode bytes =
    let addr = base#add_int position in
    let instr = make_mips_assembly_instruction addr opcode bytes in
    begin
      set_mips_assembly_instruction instr;
      opcode_monitor#check_instruction instr
    end in
  let ch =
    make_pushback_stream ~little_endian:system_info#is_little_endian x in
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "base: ";
           base#toPretty;
           STR "; displacement: ";
           INT displacement;
           STR "; size: ";
           INT size]) in
  try
    begin
      while ch#pos < size do
        let prevPos = ch#pos in
        let instraddr = base#add_int prevPos in
        let instrbytes = ch#read_doubleword in
        let opcode =
          try
            disassemble_mips_instruction instraddr instrbytes
          with
          | _ -> NotRecognized ("exception", instrbytes) in
        let currentPos = ch#pos in
        let instrLen = currentPos - prevPos in
        let instrBytes = ch#sub prevPos instrLen in
        let _ = add_instruction prevPos opcode instrBytes in
      ()
      done ;
      !mips_assembly_instructions#set_not_code opcode_monitor#get_data_blocks
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


let disassemble_mips_sections () =
  let xSections = elf_header#get_executable_sections in
  let (startOfCode, endOfCode) =
    if (List.length xSections) = 0 then
      raise (BCH_failure (STR "Executable does not have section headers"))
    else
      let headers =
        List.sort (fun (h1,_) (h2,_) ->
            h1#get_addr#compare h2#get_addr) xSections in
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
  let sizeOfCode = TR.tget_ok (endOfCode#subtract startOfCode) in
  (* only 4-byte aligned *)
  let _ = initialize_mips_instructions (sizeOfCode#to_int / 4) in
  let _ =
    pverbose [
        STR "Create space for ";
        sizeOfCode#toPretty;
        STR " (";
	INT sizeOfCode#to_int;
        STR ")";
        STR "instructions"] in
  let _ = initialize_mips_assembly_instructions sizeOfCode#to_int startOfCode in
  let _ =
    List.iter
      (fun (h, x) ->
        let _ =
          pverbose [
              STR "disassemble section:"; NL; h#toPretty; NL; NL] in
        let displacement =
          TR.tget_ok (h#get_addr#subtract_to_int startOfCode) in
        let _ =
          pverbose [
              STR "disassemble section at displacement: ";
              INT displacement;
              NL] in
        disassemble h#get_addr displacement x) xSections in
  let _ =
    pverbose [
        STR "Disassembled "; INT (List.length xSections); STR " sections"; NL] in
  sizeOfCode


(* recognizes patterns of library function calls
   strings:
     1080998f 2578e003 09f82003 0b001824
     1080998f 2578e003 09f82003 0c001824

     F B 0x46df90  10 80 99 8f       lw       $t9, -0x7ff0($gp)
         0x46df94  21 78 e0 03       move     $t7, $ra
         0x46df98  09 f8 20 03       jalr     $ra, $t9
         0x46df9c  b9 01 18 24       li       $t8, 441

     1080998f 2178e003 09f82003 b9011824

     F B 0x403810  8f 99 80 10       lw       $t9, -0x7ff0($gp)
         0x403814  03 e0 78 21       move     $t7, $ra
         0x403818  03 20 f8 09       jalr     $ra, $t9
         0x40381c  24 18 00 49       li       $t8, 73

     8f998010 03e07821 0320f809 241800xx

     3c0f00438df9f2d40320000825f8f2d4

    F B 0x402440  3c 0f 00 43       lui      $t7, 67
        0x402444  8d f9 f2 d4       lw       $t9, -0xd2c($t7)
        0x402448  03 20 00 08       jr       $t9
      D 0x40244c  25 f8 f2 d4       addiu    $t8, $t7, -3372

    3c0f0043 8df9f2d8 03200008 25f8f2d8

    F B 0x402450  3c 0f 00 43       lui      $t7, 67
        0x402454  8d f9 f2 d8       lw       $t9, -0xd28($t7)
        0x402458  03 20 00 08       jr       $t9
      D 0x40245c  25 f8 f2 d8       addiu    $t8, $t7, -3368

    3c0f0043 8df95a08 03200008 25f85a08

    F B 0x401ab0  3c 0f 00 43       lui      $t7, 67
        0x401ab4  8d f9 5a 08       lw       $t9, 0x5a08($t7)
        0x401ab8  03 20 00 08       jr       $t9
      D 0x401abc  25 f8 5a 08       addiu    $t8, $t7, 23048


    F D 0x402810  3c 0f 00 4b       lui      $t7, 75
      B 0x402814  8d f9 94 38       lw       $t9, -0x6bc8($t7)
        0x402818  25 f8 94 38       addiu    $t8, $t7, -27592
        0x40281c  03 20 00 08       jr       $t9
    F D 0x402810  3c 0f 00 4b       lui      $t7, 75

    F D 0x402820  3c 0f 00 4b       lui      $t7, 75
      B 0x402824  8d f9 94 3c       lw       $t9, -0x6bc4($t7)
        0x402828  25 f8 94 3c       addiu    $t8, $t7, -27588
        0x40282c  03 20 00 08       jr       $t9

    F D 0x402840  3c 0f 00 4b       lui      $t7, 75
      B 0x402844  8d f9 94 44       lw       $t9, -0x6bbc($t7)
        0x402848  25 f8 94 44       addiu    $t8, $t7, -27580
        0x40284c  03 20 00 08       jr       $t9
   *)

let is_library_stub faddr =
  if elf_header#is_program_address faddr
     && elf_header#has_xsubstring faddr 16 then
    let bytestring =
      byte_string_to_printed_string (elf_header#get_xsubstring faddr 16) in
    let instrseqs = [
        "1080998f2578e00309f82003\\(..\\)001824";
        "1080998f2178e00309f82003\\(..\\)001824";
        "1080998f2178e00309f82003\\(....\\)1824";
        "8f99801003e078210320f8092418\\(....\\)";
        "3c0f00438df9f\\(...\\)0320000825f8f\\(...\\)";
        "3c0f00438df95\\(...\\)0320000825f85\\(...\\)";
        "3c0f004b8df9\\(....\\)25f8\\(....\\)03200008"
      ] in
    let result =
      List.exists (fun s ->
          let regex = Str.regexp s in
          Str.string_match regex bytestring 0) instrseqs in
    result
  else
    false


(* used in case of JMPREL relocation *)
let set_library_stub_name faddr =
  if elf_header#is_program_address faddr then
    let bytestring =
      byte_string_to_printed_string (elf_header#get_xsubstring faddr 16) in
    let regex =  Str.regexp "3c0f00438df9f\\(...\\)0320000825f8f\\(...\\)" in
    if Str.string_match regex bytestring 0 then
      let offset =
        constant_string_to_doubleword ("0x" ^ Str.matched_group 1 bytestring) in
      let addr =
        (constant_string_to_doubleword "0x42f000")#add offset in
      if functions_data#has_function_name addr then
        let fndata = functions_data#add_function faddr in
        let fnname = (functions_data#get_function addr)#get_function_name in
        let has_summary = function_summary_library#has_so_function fnname in
        begin
          fndata#add_name fnname;
          fndata#set_library_stub;
          chlog#add
            "ELF library stub"
            (LBLOCK [
                 faddr#toPretty;
                 STR ": ";
                 STR fndata#get_function_name;
                 STR (if has_summary then "" else " (no summary)")])
        end
      else
        chlog#add "no stub name found" addr#toPretty
    else
      let regex =  Str.regexp "3c0f00438df9\\(....\\)0320000825f8\\(....\\)" in
      if Str.string_match regex bytestring 0 then
        let offset =
          constant_string_to_doubleword ("0x" ^ Str.matched_group 1 bytestring) in
        let addr =
          (constant_string_to_doubleword "0x430000")#add offset in
        if functions_data#has_function_name addr then
          let fndata = functions_data#add_function faddr in
          let fnname = (functions_data#get_function addr)#get_function_name in
          let has_summary = function_summary_library#has_so_function fnname in
          begin
            fndata#add_name fnname;
            fndata#set_library_stub;
            chlog#add
              "ELF library stub"
              (LBLOCK [
                   faddr#toPretty;
                   STR ": ";
                   STR fndata#get_function_name;
                   STR (if has_summary then "" else " (no summary)")])
          end
        else
          chlog#add "no stub name found" addr#toPretty
      else
        let regex = Str.regexp "3c0f004b8df9\\(....\\)25f8\\(....\\)03200008" in
        if Str.string_match regex bytestring 0 then
          let offset =
            constant_string_to_doubleword ("0x" ^ Str.matched_group 1 bytestring) in
          let addr =
            (constant_string_to_doubleword "0x4a0000")#add offset in
          if functions_data#has_function_name addr then
            let fndata = functions_data#add_function faddr in
            let fnname = (functions_data#get_function addr)#get_function_name in
            let has_summary = function_summary_library#has_so_function fnname in
            begin
              fndata#add_name fnname;
              fndata#set_library_stub;
              chlog#add
                "ELF library stub"
                (LBLOCK [
                     faddr#toPretty;
                     STR ": ";
                     STR fnname;
                     STR (if has_summary then "" else " (no summary)")])
            end
          else
            chlog#add "no stub name found" addr#toPretty
        else
          chlog#add
            "no string match for stub"
            (LBLOCK [faddr#toPretty; STR ": "; STR bytestring])
  else
    chlog#add "faddr is not a program address" faddr#toPretty


let extract_so_symbol (_opcodes:mips_opcode_t list) = None    (* TBD *)


let get_so_target
      (tgtaddr:doubleword_int) (_instr:mips_assembly_instruction_int) =
  if functions_data#has_function_name tgtaddr then
    let fndata = functions_data#get_function tgtaddr in
    if fndata#is_library_stub then
      Some fndata#get_function_name
    else
      None
  else
    None


(* can be used before functions have been constructed *)
let is_nr_call_instruction (instr:mips_assembly_instruction_int) =
  match instr#get_opcode with
  | JumpLink tgt
    | BranchLTZeroLink (_,tgt)
    | BranchGEZeroLink (_,tgt)
    | BranchLink tgt when tgt#is_absolute_address ->
     let tgtaddr = tgt#get_absolute_address in
     ((functions_data#is_function_entry_point tgtaddr)
      && (functions_data#get_function tgtaddr)#is_non_returning)
  | _ -> false


let collect_function_entry_points () =
  let addresses = new DoublewordCollections.set_t in
  begin
    addresses#addList functions_data#get_function_entry_points;
    !mips_assembly_instructions#itera
     (fun _va instr ->
       match instr#get_opcode with
       | BranchLTZeroLink (_,tgt)
         | BranchGEZeroLink (_,tgt)
         | BranchLink tgt
         | JumpLink tgt when tgt#is_absolute_address ->
          (match get_so_target tgt#get_absolute_address instr with
           | Some sym ->
              (functions_data#add_function tgt#get_absolute_address)#add_name sym
           | _ ->
              addresses#add tgt#get_absolute_address)
       | _ -> ()) ;
    addresses#toList
  end


let set_block_boundaries () =
  let set_block_entry (va: doubleword_int) =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "set_block_boundaries:set_block_entry: "; va#toPretty]))
        (get_mips_assembly_instruction va) in
    instr#set_block_entry in

  let set_delay_slot (va: doubleword_int) =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "set_block_boundaries:set_delay_slot: "; va#toPretty]))
        (get_mips_assembly_instruction va) in
    instr#set_delay_slot in

  let feps = functions_data#get_function_entry_points in
  begin
    (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ record function entry points *)
    List.iter
      (fun fe ->
        try
          set_block_entry fe
        with
	| BCH_failure _ ->
	  chlog#add "disassembly"
	    (LBLOCK [ STR "function entry point incorrect: " ; fe#toPretty ])
	| Invalid_argument s ->
	  ch_error_log#add "disassembly"
	    (LBLOCK [ STR "function entry point problem: " ; fe#toPretty ;
		      STR ": " ; STR s ])
      ) feps ;
    (* ~~~~~~~~~~~~~~~~ record targets of unconditional and conditional jumps *)
    !mips_assembly_instructions#itera
     (fun _ instr ->
       try
         let opcode = instr#get_opcode in
         if is_direct_jump_instruction opcode then
           let tgtaddr = get_direct_jump_target_address opcode in
           set_block_entry tgtaddr
         else
           ()
       with
       | BCH_failure p ->
          ch_error_log#add
            "disassembly"
            (LBLOCK [
                 STR "assembly instruction creates incorrect block entry: (";
                 instr#get_address#toPretty;
                 STR "): ";
                 instr#toPretty;
                 STR ": ";
                 p])) ;
    (* ~~~~~~~~~~~ add block entries due to previous block-ending instruction *)
    !mips_assembly_instructions#itera
     (fun va instr ->
       try
         let opcode = instr#get_opcode in
         if is_jump_instruction opcode || is_halt_instruction opcode then
           begin
             set_delay_slot (va#add_int 4) ;
             set_block_entry (va#add_int 8)
           end
         else if is_nr_call_instruction instr then
           begin
             set_delay_slot (va#add_int 4) ;
             set_block_entry (va#add_int 8)
           end
         else
           ()
       with
       | BCH_failure p ->
          raise
            (BCH_failure
               (LBLOCK [STR "Error in set_block_boundaries: "; p])))
  end


(*
let is_so_jump_target (target_address:doubleword_int) =
  match elf_header#get_relocation target_address with
  | Some _ -> true
  | _ -> false
 *)


let get_successors (faddr:doubleword_int) (iaddr:doubleword_int)  =
  if system_info#is_nonreturning_call faddr iaddr then
    []
  else
    log_tfold_default
      (mk_tracelog_spec
         ~tag:"get_successors"
         ("faddr:" ^ faddr#to_hex_string ^ ", iaddr:" ^ iaddr#to_hex_string))
      (fun instr ->
        let opcode = instr#get_opcode in
        let next () = [iaddr#add_int 4] in
        let delaynext () = [iaddr#add_int 8] in
        let successors =
          if is_conditional_jump_instruction opcode then
            (delaynext ()) @ [get_direct_jump_target_address opcode]
          else if is_direct_jump_instruction opcode then
            [get_direct_jump_target_address opcode]
          else
            next () in
        List.map
          (fun va -> (make_location {loc_faddr = faddr; loc_iaddr = va})#ci)
          successors)
      []
      (get_mips_assembly_instruction iaddr)


let trace_block (faddr:doubleword_int) (baddr:doubleword_int) =

  let set_block_entry (va: doubleword_int) =
    TR.titer
      ~ok:(fun instr -> instr#set_block_entry)
      ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
      (get_mips_assembly_instruction va) in

  let get_instr iaddr = get_mips_assembly_instruction iaddr in

  let get_next_instr_addr a = a#add_int 4 in

  let mk_ci_succ l =
    List.map
      (fun va -> (make_location {loc_faddr = faddr ; loc_iaddr = va})#ci) l in

  let rec find_last_instr (va: doubleword_int) (prev: doubleword_int) =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "find_last_instr: "; va#toPretty]))
        (get_instr va) in

    (* continue tracing thee block *)
    let nextva () = get_next_instr_addr va in

    if va#equal wordzero
       || not (!mips_assembly_instructions#is_code_address va) then
      (Some [],prev,[])
    else if is_return_instruction instr#get_opcode then
      (Some [],va#add_int 4,[])
    else if instr#is_block_entry then
      (None,prev,[])
    else if is_nr_call_instruction instr then
      (Some [],va#add_int 4,[])
    else if is_conditional_jump_instruction instr#get_opcode
            || is_fp_conditional_jump_instruction instr#get_opcode then
      let nextblock = va#add_int 8 in
      let tgtblock = get_direct_jump_target_address instr#get_opcode in
      (Some (mk_ci_succ [ nextblock ; tgtblock ]),va#add_int 4,[])
    else if is_direct_jump_instruction instr#get_opcode then
      let tgtblock = get_direct_jump_target_address instr#get_opcode in
      if functions_data#is_function_entry_point tgtblock then
        (Some [], va#add_int 4, [])                (* function chaining *)
      else
        (Some (mk_ci_succ [tgtblock]), va#add_int 4, [])
    else if is_indirect_jump_instruction instr#get_opcode then
      if system_info#has_jump_table_target faddr va then
        let loc = make_location { loc_faddr = faddr ; loc_iaddr = va } in
        let ctxtiaddr = loc#ci in
        let finfo = get_function_info faddr in
        let (jt,_,lb,ub) = system_info#get_jump_table_target faddr va in
        let targets = jt#get_targets jt#get_start_address lb ub in
        let reg =
          MIPSRegister (get_indirect_jump_instruction_register instr#get_opcode) in
        let _ = finfo#set_jumptable_target ctxtiaddr jt#get_start_address jt reg in
        (Some (mk_ci_succ targets), va#add_int 4, [])
      else if system_info#has_indirect_jump_targets faddr va then
        let targets = system_info#get_indirect_jump_targets faddr va in
        (Some (mk_ci_succ targets), va#add_int 4, [])
      else
        (Some [], va#add_int 4, [])
    else if instr#is_delay_slot then
      (None, va, [])
    else if is_halt_instruction instr#get_opcode then
      (Some [], va, [])
    else if instr#is_inlined_call then
      let a = match instr#get_opcode with
        | BranchLTZeroLink (_,tgt)
          | BranchGEZeroLink (_,tgt)
          | BranchLink tgt
          | JumpLink tgt when tgt#is_absolute_address ->
           tgt#get_absolute_address
        | _ ->
           raise (BCH_failure (LBLOCK [ STR "Internal error in trace block" ])) in
      let fn = mips_assembly_functions#get_function_by_address a in
      let returnsite = get_next_instr_addr va in
      let _ = set_block_entry returnsite in
      let ctxt =
        FunctionContext
          { ctxt_faddr = faddr ;
            ctxt_callsite = a ;
            ctxt_returnsite = returnsite } in
      let callloc = make_location { loc_faddr = a ; loc_iaddr = a } in
      let ctxtcallloc = make_c_location callloc ctxt in
      let callsucc = ctxtcallloc#ci in
      let inlinedblocks =
        List.map
          (fun b ->
            let succ =
              match b#get_successors with
              | [] ->
                 [(make_location {loc_faddr = faddr; loc_iaddr = returnsite})#ci]
              | l -> List.map (fun s -> add_ctxt_to_ctxt_string faddr s ctxt) l in
            make_ctxt_mips_assembly_block ctxt b succ) fn#get_blocks in
      (Some [ callsucc ],va,inlinedblocks)
    else
      find_last_instr (nextva ()) va in

  let (succ, lastaddr, inlinedblocks) =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "find_last_instr: "; baddr#toPretty]))
        (get_instr baddr) in
    let opcode = instr#get_opcode in
    if is_return_instruction opcode then
      (Some [],baddr#add_int 4,[])
    else if system_info#is_nonreturning_call faddr baddr then
      (Some [], baddr#add_int 4, [])
    else if is_indirect_jump_instruction opcode then
      if system_info#has_jump_table_target faddr baddr then
        let (jt,_,lb,ub) = system_info#get_jump_table_target faddr baddr in
        let targets = jt#get_targets jt#get_start_address lb ub in
        (Some (mk_ci_succ targets), baddr#add_int 4, [])
      else
        (Some [], baddr#add_int 4, [])
    else if is_conditional_jump_instruction opcode then
      let nextblock = baddr#add_int 8 in
      let tgtblock = get_direct_jump_target_address opcode in
      (Some (mk_ci_succ [ nextblock ; tgtblock ]),baddr#add_int 4,[])
    else if is_direct_jump_instruction opcode then
      let tgtblock = get_direct_jump_target_address opcode in
      (Some (mk_ci_succ [ tgtblock ]),baddr#add_int 4,[])
    else
      find_last_instr (get_next_instr_addr baddr) baddr in

  let successors =
    match succ with Some s -> s | _ -> get_successors faddr lastaddr in
  (inlinedblocks, make_mips_assembly_block faddr baddr lastaddr successors)


let trace_function (faddr:doubleword_int) =
  let workSet = new DoublewordCollections.set_t in
  let doneSet = new DoublewordCollections.set_t in
  let set_block_entry (baddr: doubleword_int) =
    TR.titer
      ~ok:(fun instr -> instr#set_block_entry)
      ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
      (get_mips_assembly_instruction baddr) in
  let get_iaddr s = (ctxt_string_to_location faddr s)#i in
  let add_to_workset l =
    List.iter (fun a -> if doneSet#has a then () else workSet#add a) l in
  let blocks = ref [] in
  let rec add_block (entry:doubleword_int) =
    let (inlinedblocks,block) = trace_block faddr entry in
    let blocksuccessors = block#get_successors in
    begin
      set_block_entry entry ;
      workSet#remove entry ;
      doneSet#add entry ;
      blocks := (block :: inlinedblocks) @ !blocks ;
      add_to_workset (List.map get_iaddr blocksuccessors) ;
      match workSet#choose with Some a -> add_block a | _ -> ()
    end in
  let _ = add_block faddr in
  let blocklist =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_context_string b2#get_context_string) !blocks in
  let successors =
    List.fold_left (fun acc b ->
        let src = b#get_context_string in
        (List.map (fun tgt -> (src,tgt)) b#get_successors) @ acc) [] blocklist in
  make_mips_assembly_function faddr blocklist successors


let construct_mips_assembly_function (_count: int) (faddr: doubleword_int) =
  try
    let _ = pverbose [STR "  trace function "; faddr#toPretty; NL] in
    let fn = trace_function faddr in
    let _ = pverbose [STR "  add function "; faddr#toPretty; NL] in
    mips_assembly_functions#add_function fn
  with
  | BCH_failure p ->
     raise
       (BCH_failure
          (LBLOCK [
               STR "Error in constructing function ";
               faddr#toPretty;
               STR ": ";
               p]))


let construct_functions f =
  let _ = system_info#initialize_function_entry_points f in
  let _ = set_block_boundaries () in
  let functionentrypoints = functions_data#get_function_entry_points in
  let count = ref 0 in
  begin
    List.iter (fun faddr ->
        let default () =
          try
            begin
              count := !count + 1;
              construct_mips_assembly_function !count faddr
            end
          with
          | BCH_failure p ->
             ch_error_log#add
               "construct functions"
               (LBLOCK [STR "function "; faddr#toPretty; STR ": "; p]) in
        let fndata = functions_data#get_function faddr in
        if fndata#is_library_stub then
          ()
        else if fndata#has_name then
          if is_library_stub faddr then
            let has_summary =
              function_summary_library#has_so_function fndata#get_function_name in
            begin
              fndata#set_library_stub;
              chlog#add
                "ELF library stub"
                (LBLOCK [
                     faddr#toPretty;
                     STR ": ";
                     STR fndata#get_function_name;
                     STR (if has_summary then "" else " (no summary)")])
            end
          else
            default ()
        else if is_library_stub faddr then
          set_library_stub_name faddr
        else
          default ()
      ) functionentrypoints;
    List.iter (fun faddr ->
        begin
          count := !count + 1;
          construct_mips_assembly_function !count faddr
        end)  mips_assembly_functions#add_functions_by_preamble
  end


let record_call_targets () =
  mips_assembly_functions#itera
    (fun faddr f ->
      try
        let finfo = get_function_info faddr in
        begin
          f#iteri
            (fun _ ctxtiaddr instr ->
              match instr#get_opcode with
              | BranchLink op
              | JumpLink op ->
                 if finfo#has_call_target ctxtiaddr
                    && not (finfo#get_call_target ctxtiaddr)#is_unknown then
                   let loc = ctxt_string_to_location faddr ctxtiaddr in
                   let floc = get_floc loc in
                   floc#update_call_target
                 else
                   begin
                     match get_so_target op#get_absolute_address instr with
                     | Some tgt ->
                        finfo#set_call_target ctxtiaddr (mk_so_target tgt)
                     | _ ->
                        if op#is_absolute_address then
                          finfo#set_call_target
                            ctxtiaddr (mk_app_target op#get_absolute_address)
                   end
              | JumpLinkRegister (_ra, _op) ->
                 let iaddr = (ctxt_string_to_location faddr ctxtiaddr)#i in
                 if finfo#has_call_target ctxtiaddr then
                   let loc = ctxt_string_to_location faddr ctxtiaddr in
                   let floc = get_floc loc in
                   floc#update_call_target
                 else if system_info#has_call_target faddr iaddr then
                   let calltgt = system_info#get_call_target faddr iaddr in
                   let ctinfo = mk_call_target_info calltgt in
                   finfo#set_call_target ctxtiaddr ctinfo
                 else
                   finfo#set_call_target ctxtiaddr (mk_unknown_target ())
              | Jump op
                   when functions_data#is_function_entry_point
                          op#get_absolute_address ->
                 let _ =
                   chlog#add
                     "function chaining"
                     (LBLOCK [
                          faddr#toPretty;
                          STR " @ "; STR ctxtiaddr;
                          STR ": ";
                          op#get_absolute_address#toPretty]) in
                 finfo#set_call_target
                   ctxtiaddr (mk_app_target op#get_absolute_address)
              | _ -> ())
        end
      with
      | BCH_failure p ->
         ch_error_log#add
           "record call targets"
           (LBLOCK [STR "function "; faddr#toPretty; STR ": "; p]))



let decorate_functions () =
  begin
    record_call_targets ()
  end


let construct_functions_mips () =
  begin
    construct_functions collect_function_entry_points ;
    decorate_functions ()
  end


let set_call_address (floc:floc_int) (op:mips_operand_int) =
  let env = floc#f#env in
  let opExpr = op#to_expr floc in
  let opExpr = floc#inv#rewrite_expr opExpr in
  let logerror msg = ch_error_log#add "set call address" msg in
  match opExpr with
  | XConst (IntConst c) ->
     let dw = TR.tget_ok (numerical_to_doubleword c) in
     if functions_data#has_function_name dw then
       let fndata = functions_data#get_function dw in
       let name = fndata#get_function_name in
       if fndata#is_library_stub then
         if function_summary_library#has_so_function name then
           floc#set_call_target (mk_so_target name)
         else
           begin
             floc#set_call_target (mk_so_target name);
             chlog#add "missing library summary" (STR name)
           end
       else
         if mips_assembly_functions#has_function_by_address dw then
           floc#set_call_target (mk_app_target dw)
         else if functions_data#is_function_entry_point dw then
           let fndata = functions_data#get_function dw in
           if fndata#has_name then
             let name = List.hd fndata#get_names in
             let _ = chlog#add "look for library function" (STR name) in
             if function_summary_library#has_so_function name then
               floc#set_call_target (mk_so_target name)
             else
               ()
           else
             ()
         else
           ()
     else
       if mips_assembly_functions#has_function_by_address dw then
         floc#set_call_target (mk_app_target dw)
       else if functions_data#is_function_entry_point dw then
         let fndata = functions_data#get_function dw in
         if fndata#has_name then
           let name = List.hd fndata#get_names in
           let _ = chlog#add "look for library function" (STR name) in
           if function_summary_library#has_so_function name then
             floc#set_call_target (mk_so_target name)
           else
             ()
         else
           ()
       else
         ()

  | XVar v when env#is_global_variable v ->
     log_tfold
       (log_error "set_call_target" "invalid global address")
       ~ok:(fun gaddr ->
         if elf_header#is_program_address gaddr then
           let dw = elf_header#get_program_value gaddr in
           if functions_data#has_function_name dw then
             let fndata = functions_data#get_function dw in
             let name = fndata#get_function_name in
             if fndata#is_library_stub
                && function_summary_library#has_so_function name then
               floc#set_call_target (mk_so_target name)
             else
               if mips_assembly_functions#has_function_by_address dw then
                 floc#set_call_target (mk_app_target dw)
               else
                 begin
                   floc#set_call_target (mk_so_target name);
                   chlog#add "missing library summary" (STR name)
                 end
           else
             if mips_assembly_functions#has_function_by_address dw then
               floc#set_call_target (mk_app_target dw)
             else
               logerror
                 (LBLOCK [
                      STR "reference does not resolve to function address: ";
                      dw#toPretty])
         else
       logerror
         (LBLOCK [STR "reference is not in program space: "; gaddr#toPretty]))
       ~error:(fun _ ->
         logerror (LBLOCK [STR "global address is invalid"]))
       (env#get_global_variable_address v)


  | XOp (XPlus, [XVar v; XConst (IntConst n)]) when env#is_global_variable v ->
     log_tfold
       (log_error "set_call_target" "invalid global address (2)")
       ~ok:(fun gaddr ->
         if elf_header#is_program_address gaddr then
           let dw = elf_header#get_program_value gaddr in
           let dwfun = dw#add (TR.tget_ok (numerical_to_doubleword n)) in
           let _ = chlog#add "resolve gv-expr" (x2p opExpr) in
           if functions_data#has_function_name dwfun then
             let name = (functions_data#get_function dwfun)#get_function_name in
             if function_summary_library#has_so_function name then
               floc#set_call_target (mk_so_target name)
             else
               if mips_assembly_functions#has_function_by_address dwfun then
                 floc#set_call_target (mk_app_target dwfun)
               else
                 logerror
                   (LBLOCK [
                        STR "Function name not associated with address: ";
                        STR name])
           else
             if mips_assembly_functions#has_function_by_address dwfun then
               floc#set_call_target (mk_app_target dwfun)
             else
               begin
                 ignore (functions_data#add_function dwfun);
                 floc#set_call_target (mk_app_target dwfun);
                 chlog#add
                   "add gv-based function"
                   (LBLOCK [
                        STR "Addr expr: ";
                        x2p opExpr;
                        STR " resolves to ";
                        dwfun#toPretty])
               end
         else
           logerror
             (LBLOCK [STR "reference is not in program space: "; gaddr#toPretty]))
       ~error:(fun _ -> logerror (STR "invalid global address"))
       (env#get_global_variable_address v)
  | _ ->
     ()


let set_syscall_target (floc:floc_int) (op:mips_operand_int) =
  let opval = op#to_expr floc in
  let tgtindex = floc#inv#rewrite_expr opval in
  match tgtindex with
  | XConst (IntConst n) ->
     floc#set_call_target (mk_syscall_target n#toInt)
  | _ -> ()


let resolve_indirect_mips_calls (f:mips_assembly_function_int) =
  let _ =
    f#iteri
      (fun faddr ctxtiaddr instr ->
        let loc = ctxt_string_to_location faddr ctxtiaddr in
        match instr#get_opcode with
        | JumpLinkRegister (_ra, tgt) ->
           let floc = get_floc loc in
           if (floc#has_call_target && floc#get_call_target#is_unknown)
              || not floc#has_call_target then
             set_call_address floc tgt
        | JumpRegister tgt ->
           let floc = get_floc loc in
           let env = floc#f#env in
           let ra_op = mips_register_op MRra RD in
           let ra = floc#inv#rewrite_expr (ra_op#to_expr floc) in
           begin
             match ra with
             | XVar ra_var ->
                if env#is_initial_register_value ra_var then
                  (* this is a tail call; ra has already been restored *)
                  if (floc#has_call_target && floc#get_call_target#is_unknown)
                     || not floc#has_call_target then
                    set_call_address floc tgt
             | _ ->
                pr_debug [floc#l#toPretty; STR ": ra = "; x2p ra; NL]
           end
        | Syscall _ ->
           let floc = get_floc loc in
           if (floc#has_call_target && floc#get_call_target#is_unknown)
              || not floc#has_call_target then
             let v0_op = mips_register_op MRv0 RD in
             set_syscall_target floc v0_op
           else
             ()
        | _ ->
           ()) in
  ()

(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2023  Aarno Labs LLC

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

(* bchlibpower32 *)
open BCHConstructPowerFunction
open BCHDisassemblePowerInstruction
open BCHDisassembleVLEInstruction
open BCHPowerAssemblyFunctions
open BCHPowerAssemblyInstruction
open BCHPowerAssemblyInstructions
open BCHPowerOpcodeRecords
open BCHPowerTypes

module TR = CHTraceResult


module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


let disassemble
      (base: doubleword_int)
      (is_vle: bool)
      (displacement: int)
      (x: string) =
  let size = String.length x in
  let add_instr (position: int) (opcode: pwr_opcode_t) (bytes: string) =
    let index = (position + displacement) in
    let addr = base#add_int position in
    let instr = make_pwr_assembly_instruction addr is_vle opcode bytes in
    begin
      set_pwr_assembly_instruction instr;
      instr
    end in
  let ch = make_pushback_stream ~little_endian:system_info#is_little_endian x in
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "base: ";
           base#toPretty;
           STR "; displacement";
           INT displacement;
           STR "; size: ";
           INT size]) in
  try
    begin
      while ch#pos + 2 < size do
        let prevPos = ch#pos in
        let iaddr = base#add_int ch#pos in
        try
          if is_vle then
            let instrbytes = ch#read_ui16 in
            let opcode =
              try
                disassemble_vle_instruction ch iaddr instrbytes
              with
              | _ -> OpInvalid in
            let currentPos = ch#pos in
            let instrlen = currentPos - prevPos in
            let instrBytes = Bytes.make instrlen ' ' in
            let _ =
              try
                Bytes.blit (Bytes.of_string x) prevPos instrBytes 0 instrlen
              with
              | _ ->
                 raise
                   (BCH_failure
                      (LBLOCK [
                           STR "Error in Bytes.blit (VLE): ";
                           STR "prevPos: ";
                           INT prevPos;
                           STR "; instrlen";
                           INT instrlen;
                           STR "; ch#pos";
                           INT ch#pos;
                           STR "; size: ";
                           INT size])) in
            let _ = add_instr prevPos opcode (Bytes.to_string instrBytes) in
            let _ =
              pverbose [
                  (base#add_int prevPos)#toPretty;
                  STR "  ";
                  STR (pwr_opcode_to_string opcode);
                  NL] in
            ()
          else
            let instrbytes = ch#read_doubleword in
            let opcode =
              try
                disassemble_pwr_instruction ch iaddr instrbytes
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
            let instrlen = currentPos - prevPos in
            let instrBytes = Bytes.make instrlen ' ' in
            let _ =
              try
                Bytes.blit (Bytes.of_string x) prevPos instrBytes 0 instrlen
              with
              | _ ->
                 raise
                   (BCH_failure
                      (LBLOCK [
                           STR "Error in Bytes.blit (Power): ";
                           STR "prevPos: ";
                           INT prevPos;
                           STR "; instrlen: ";
                           INT instrlen])) in
            let _ = add_instr prevPos opcode (Bytes.to_string instrBytes) in
            let _ =
              pverbose [
                  (base#add_int prevPos)#toPretty;
                  STR "  ";
                  STR (pwr_opcode_to_string opcode);
                  NL] in
            ()
        with
        | BCH_failure p ->
           begin
             ch_error_log#add
               "disassembly"
               (LBLOCK [
                 STR "failure in disassembling instruction at ";
                 (base#add_int prevPos)#toPretty;
                 STR " in mode ";
                 STR (if is_vle then "VLE" else "PowerPC")]);
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


let disassemble_pwr_sections () =
  let xSections = elf_header#get_executable_sections in
  let (startOfCode, endOfCode) =
    if (List.length xSections) = 0 then
      raise (BCH_failure (STR "Executable does not have section headers"))
    else
      let headers =
        List.sort (fun (h1, _) (h2, _) ->
            h1#get_addr#compare h2#get_addr) xSections in
      let (lowest, _) = List.hd headers in
      let (highest, _) = List.hd (List.rev headers) in
      let _ =
        chlog#add
          "disassembly"
          (LBLOCK [
               pretty_print_list
                 headers
                 (fun (s, _) ->
                   LBLOCK [
                       STR s#get_section_name;
                       STR ":";
                       s#get_addr#toPretty;
                       STR " (";
                       s#get_size#toPretty;
                       STR ")"])
                 "[" " ; " "]"]) in
      let startOfCode = lowest#get_addr in
      let endOfCode = highest#get_addr#add highest#get_size in
      (startOfCode, endOfCode) in
  let sizeOfCode = TR.tget_ok (endOfCode#subtract startOfCode) in
  (* can be 2 (VLE) or 4-byte aligned *)
  let _ = initialize_pwr_instructions sizeOfCode#to_int in
  let _ =
    pr_debug [
        STR "Create space for ";
        sizeOfCode#toPretty;
        STR " (";
        INT sizeOfCode#to_int;
        STR ")";
        STR " instructions"] in
  let _ = initialize_pwr_assembly_instructions sizeOfCode#to_int startOfCode in
  let _ =
    List.iter
      (fun (h, x) ->
        let displacement =
          fail_tvalue
            (trerror_record
               (LBLOCK [
                    STR "Error in disassemble_power_sections: displacement ";
                    STR "header address: ";
                    h#get_addr#toPretty;
                    STR "; startOfCode: ";
                    startOfCode#toPretty]))
            (h#get_addr#subtract_to_int startOfCode) in
        disassemble h#get_addr h#is_pwr_vle displacement x) xSections in
  sizeOfCode


let collect_function_entry_points () =
  let _ = pverbose [STR "Collect function entry points"; NL] in
  let addresses = new DoublewordCollections.set_t in
  begin
    !pwr_assembly_instructions#itera
      (fun va instr ->
        match instr#get_opcode with
        | BranchLink (_, tgt, _) ->
           let tgtaddr = tgt#get_absolute_address in
           addresses#add tgtaddr
        | _ -> ());
    addresses#toList
  end


let collect_call_targets () =
  let _ = pverbose [STR "Collect call targets"; NL] in
  !pwr_assembly_instructions#itera
    (fun va instr ->
      match instr#get_opcode with
      | BranchLink (_, tgt, _) ->
         let tgtaddr = tgt#get_absolute_address in
         if functions_data#is_function_entry_point tgtaddr then
           let fndata = functions_data#get_function tgtaddr in
           fndata#add_callsite
      | _ -> ())


let set_block_boundaries () =
  let _ = pverbose [STR "Set block boundaries"; NL] in
  let set_inlined_call (a: doubleword_int) =
    log_titer
      (mk_tracelog_spec
         ~tag:"set_block_boundaries"
         ("set_inlined_call:" ^ a#to_hex_string))
      (fun instr -> instr#set_inlined_call)
      (get_pwr_assembly_instruction a) in
  let set_block_entry a =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "set block boundaries:set_block_entry: "; a#toPretty]))
        (get_pwr_assembly_instruction a) in
    instr#set_block_entry in
  let feps = functions_data#get_function_entry_points in
  begin
    pverbose [STR "   record function entry points"; NL];
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

    (* ----------------------------- record targets of unconditional jumps -- *)
    !pwr_assembly_instructions#itera
      (fun va instr ->
        try
          (match instr#get_opcode with
           | Branch (_, tgt)
             | BranchConditional (_, _, _, _, tgt)
             | CBranchDecrementNotZero (_, _, _, _, _, tgt, _)
             | CBranchDecrementZero(_, _, _, _, _, tgt, _) ->
              if tgt#is_absolute_address then
                let jumpaddr = tgt#get_absolute_address in
                set_block_entry jumpaddr
              else
                ()
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

    (* ----------------------- add block entries due to previous block-ending -- *)
    !pwr_assembly_instructions#itera
      (fun va instr ->
        let opcode = instr#get_opcode in
        let is_block_ending =
          match opcode with
          | BranchLinkRegister _ -> true
          | Branch _
            | BranchConditional _
            | CBranchDecrementNotZero _
            | CBranchDecrementZero _ -> true
          | _ -> false in
        if is_block_ending && has_next_valid_instruction va then
          let nextva =
            fail_tvalue
              (trerror_record
                 (LBLOCK [STR "Internal error in set_block_boundaries"]))
              (get_next_valid_instruction_address va) in
          set_block_entry nextva
        else
          ());

    pverbose [STR "    set_block_entries: Done"; NL]
  end


let construct_assembly_function
      (count: int) (faddr: doubleword_int): doubleword_int list =
  try
    let newfns =
      if !pwr_assembly_instructions#is_code_address faddr then
        let (fl, fn) = construct_pwr_assembly_function faddr in
        begin
          pwr_assembly_functions#add_function fn;
          fl
        end
      else
        [] in
    newfns
  with
  | BCH_failure p ->
     begin
       ch_error_log#add
         "construct assembly function"
         (LBLOCK [faddr#toPretty; STR ": "; p]);
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in constructing function ";
                   faddr#toPretty;
                   STR ": ";
                   p]))
     end


let construct_functions_pwr () =
  let _ =
    system_info#initialize_function_entry_points collect_function_entry_points in
  let _ = collect_call_targets () in
  let _ = set_block_boundaries () in
  let feps = functions_data#get_function_entry_points in
  let count = ref 0 in
  begin
    List.iter (fun faddr ->
        let default () =
          try
            begin
              count := !count + 1;
              let newfns = construct_assembly_function !count faddr in
              ()
            end
          with
          | BCH_failure p ->
             ch_error_log#add
               "construct functions"
               (LBLOCK [STR "function"; faddr#toPretty; STR ": "; p]) in
        let fndata = functions_data#get_function faddr in
        if fndata#is_library_stub then
          ()
        else
          default ()) feps;

    pr_debug [STR "Constructed: "; INT !count; STR " functions"; NL]
  end

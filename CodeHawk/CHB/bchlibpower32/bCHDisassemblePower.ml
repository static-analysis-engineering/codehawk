(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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
open BCHDisassembleVLEInstruction
open BCHPowerAssemblyInstruction
open BCHPowerAssemblyInstructions
open BCHPowerOpcodeRecords
open BCHPowerTypes



let disassemble
      (base: doubleword_int)
      (is_vle: bool)
      (displacement: int)
      (x: string) =
  let size = String.length x in
  let add_instr (position: int) (opcode: power_opcode_t) (bytes: string) =
    let index = (position + displacement) in
    let addr = base#add_int position in
    let instr = make_power_assembly_instruction addr is_vle opcode bytes in
    !power_assembly_instructions#set index instr in
  let ch = system_info#get_string_stream x in
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
                disassemble_vle_instruction ch base instrbytes
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
                  STR (power_opcode_to_string opcode);
                  NL] in
            ()
          else
            let instrbytes = ch#read_doubleword in
            let opcode =
              try
                NotRecognized ("powerpc", instrbytes)
                (* disassemble_power_instruction ch base instrbytes *)
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
                  STR (power_opcode_to_string opcode);
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


let disassemble_power_sections () =
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
  let sizeOfCode = endOfCode#subtract startOfCode in
  (* can be 2 (VLE) or 4-byte aligned *)
  let _ = initialize_power_instructions sizeOfCode#to_int in
  let _ =
    pr_debug [
        STR "Create space for ";
        sizeOfCode#toPretty;
        STR " (";
        INT sizeOfCode#to_int;
        STR ")";
        STR " instructions"] in
  let _ = initialize_power_assembly_instructions sizeOfCode#to_int startOfCode in
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
                       STR "Error in disassemble_power_secitons: displacement ";
                       STR "header address: ";
                       h#get_addr#toPretty;
                       STR "; startOfCode: ";
                       startOfCode#toPretty;
                       STR ": ";
                       STR s])) in
        disassemble h#get_addr h#is_power_vle displacement x) xSections in
  sizeOfCode

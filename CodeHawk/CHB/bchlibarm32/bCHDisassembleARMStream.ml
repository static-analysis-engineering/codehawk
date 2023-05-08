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
open CHPretty

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFloc
open BCHLibTypes
open BCHLocation
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings

(* bchlibarm32 *)
open BCHARMAssemblyBlock
open BCHARMAssemblyFunction
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMTypes
open BCHConstructARMFunction
open BCHDisassembleARMInstruction
open BCHDisassembleThumbInstruction

module TR = CHTraceResult


module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


let disassemble_arm_stream (va: doubleword_int) (codestring: string) =
  let size = String.length codestring in
  let ch = make_pushback_stream ~little_endian:true codestring in
  let sectionsizes = [("stream", va, (TR.tget_ok (int_to_doubleword size)))] in
  let _ = initialize_arm_instructions sectionsizes in
  let _ = initialize_arm_assembly_instructions sectionsizes [] in
  let add_instruction (pos: int) (opcode: arm_opcode_t) (bytes: string) =
    let addr = va#add_int pos in
    let instr = make_arm_assembly_instruction addr true opcode bytes in
    begin
      set_arm_assembly_instruction instr;
      instr
    end in
  try
    while ch#pos + 2 < size do
      let prevpos = ch#pos in
      let instrbytes = ch#read_doubleword in
      let opcode = disassemble_arm_instruction ch va instrbytes in
      let curpos = ch#pos in
      let instrlen = curpos - prevpos in
      let instrstring = String.sub codestring prevpos instrlen in
      ignore (add_instruction prevpos opcode instrstring)
    done
  with
  | BCH_failure p ->
     ch_error_log#add
       "stream arm disassembly"
       (LBLOCK [STR "failure in disassembling codestring: "; p])
  | IO.No_more_input -> ()


let disassemble_thumb_stream (va: doubleword_int) (codestring: string) =
  let size = String.length codestring in
  let _ = pr_debug [STR "Codestring of length: "; INT size; NL] in
  let ch = make_pushback_stream ~little_endian:true codestring in
  let sectionsizes = [("stream", va, (TR.tget_ok (int_to_doubleword size)))] in
  let _ = initialize_arm_instructions sectionsizes in
  let _ = initialize_arm_assembly_instructions sectionsizes [] in
  let add_instruction (pos: int) (opcode: arm_opcode_t) (bytes: string) =
    let addr = va#add_int pos in
    let instr = make_arm_assembly_instruction addr false opcode bytes in
    begin
      set_arm_assembly_instruction instr;
      instr
    end in
  try
    while ch#pos + 2 < size do
      let prevpos = ch#pos in
      let instrbytes = ch#read_ui16 in
      let opcode = disassemble_thumb_instruction ch va instrbytes in
      let curpos = ch#pos in
      let instrlen = curpos - prevpos in
      let instrstring = String.sub codestring prevpos instrlen in
      ignore (add_instruction prevpos opcode instrstring)
    done
  with
  | BCH_failure p ->
     ch_error_log#add
       "stream thumb disassembly"
       (LBLOCK [STR "failure in disassembling codestring: "; p])
  | IO.No_more_input -> ()


let set_block_boundaries () =
  let set_block_entry a =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "set_block_boundaries:set_block_entry: "; a#toPretty]))
        (get_arm_assembly_instruction a) in
    instr#set_block_entry in
  begin
    !arm_assembly_instructions#itera
      (fun va instr ->
        match instr#get_opcode with
        | Branch (_, op, _) ->
           if op#is_absolute_address then
             let jmpaddr = op#get_absolute_address in
             set_block_entry jmpaddr
           else
             ()
        | _ -> ());
    !arm_assembly_instructions#itera
      (fun va instr ->
        let opcode = instr#get_opcode in
        let is_block_ending =
          match opcode with
          | Branch _ | BranchExchange _ -> true
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
        

let disassemble_stream (va: doubleword_int) (codestring: string) =
  let _ =
    if system_settings#has_thumb then
      disassemble_thumb_stream va codestring
    else
      disassemble_arm_stream va codestring in
  let _ = set_block_boundaries () in
  let _ = system_info#initialize_function_entry_points (fun _ -> [va]) in
  let (_, fn) = construct_arm_assembly_function va in
  begin
    arm_assembly_functions#add_function fn;
    pr_debug [STR ((!arm_assembly_instructions)#toString ())]
  end

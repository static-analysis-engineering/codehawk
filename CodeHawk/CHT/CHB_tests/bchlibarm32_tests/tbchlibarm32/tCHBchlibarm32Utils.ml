(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
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
open CHLanguage

(* bchlib *)
open BCHByteUtilities
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMAssemblyBlock
open BCHARMAssemblyFunction
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstructions
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMOpcodeRecords
open BCHARMTestSupport
open BCHARMTypes
open BCHDisassembleARM
open BCHDisassembleARMInstruction
open BCHDisassembleThumbInstruction
open BCHConstructARMFunction
open BCHFnARMDictionary

module TR = CHTraceResult


let string_of_opcode (opcode: arm_opcode_t) = arm_opcode_to_string opcode


let make_stream (s: string) =
  let bytestring = write_hex_bytes_to_bytestring s in
  make_pushback_stream ~little_endian:true bytestring


let make_dw (s: string) = TR.tget_ok (string_to_doubleword s)


let arm_function_setup
      (faddr: doubleword_int) (bytes: string): arm_assembly_function_int =
  let bytestring = write_hex_bytes_to_bytestring bytes in
  let ch = make_stream bytes in
  let size = String.length bytestring in
  begin
    ignore (functions_data#add_function faddr);
    initialize_arm_assembly_instructions (String.length bytes) faddr [];
    while ch#pos + 4 < size do
      let prevpos = ch#pos in
      let iaddr = faddr#add_int ch#pos in
      let instrbytes = ch#read_doubleword in
      let opcode = disassemble_arm_instruction ch iaddr instrbytes in
      let currentpos = ch#pos in
      let instrlen = currentpos - prevpos in
      let instrbytes = String.sub bytestring prevpos instrlen in
      let instr = make_arm_assembly_instruction iaddr false opcode instrbytes in
      set_arm_assembly_instruction instr
    done;
    let _ = set_block_boundaries () in
    let fn = construct_arm_assembly_function faddr in
    arm_assembly_functions#add_function fn;
    fn
  end


let thumb_function_setup
      (faddr: doubleword_int) (bytes: string): arm_assembly_function_int =
  let bytestring = write_hex_bytes_to_bytestring bytes in
  let ch = make_stream bytes in
  let size = String.length bytestring in
  begin
    ignore (functions_data#add_function faddr);
    initialize_arm_assembly_instructions (String.length bytes) faddr [];
    while ch#pos + 2 < size do
      let prevpos = ch#pos in
      let iaddr = faddr#add_int ch#pos in
      let instrbytes = ch#read_ui16 in
      let opcode = disassemble_thumb_instruction ch iaddr instrbytes in
      let currentpos= ch#pos in
      let instrlen = currentpos - prevpos in
      let instrbytes = String.sub bytestring prevpos instrlen in
      let instr = make_arm_assembly_instruction iaddr false opcode instrbytes in
      set_arm_assembly_instruction instr
    done;
    let _ = set_block_boundaries () in
    let fn = construct_arm_assembly_function faddr in
    arm_assembly_functions#add_function fn;
    associate_condition_code_users ();
    fn
  end


let get_instrxdata_xprs (faddr: doubleword_int) (iaddr: doubleword_int) =
  let _ = testsupport#request_instrx_data in
  let finfo = get_function_info faddr in
  let floc = get_floc_by_address faddr iaddr in
  let instr = TR.tget_ok (get_arm_assembly_instruction iaddr) in
  let id = mk_arm_opcode_dictionary faddr finfo#env#varmgr#vard in
  let _ = id#index_instr instr floc in
  let (_, xprs) =
    TR.tget_ok (testsupport#retrieve_instrx_data iaddr#to_hex_string) in
  xprs

(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022      Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes
open BCHDisassembleARM
open BCHConstructARMFunction


(* bchlib *)
module U = BCHByteUtilities
module D = BCHDoubleword
module F = BCHFunctionData
module SW = BCHStreamWrapper
module SI = BCHSystemInfo

(* bchlibarm32 *)
module ARMB = BCHARMAssemblyBlock
module ARMF = BCHARMAssemblyFunction
module ARMFS = BCHARMAssemblyFunctions
module ARMI = BCHARMAssemblyInstruction
module ARMIS = BCHARMAssemblyInstructions
module R = BCHARMOpcodeRecords
module DT = BCHDisassembleARMInstruction


let string_of_opcode (opcode: arm_opcode_t) = R.arm_opcode_to_string opcode


let make_stream (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  SW.make_pushback_stream ~little_endian:true bytestring


let arm_function_setup
      (faddr: doubleword_int) (bytes: string): arm_assembly_function_int =
  let bytestring = U.write_hex_bytes_to_bytestring bytes in
  let ch = make_stream bytes in
  let size = String.length bytestring in
  begin
    ignore (F.functions_data#add_function faddr);
    ARMIS.initialize_arm_assembly_instructions (String.length bytes) faddr [];
    while ch#pos + 4 < size do
      let prevpos = ch#pos in
      let iaddr = faddr#add_int ch#pos in
      let instrbytes = ch#read_doubleword in
      let opcode = DT.disassemble_arm_instruction ch iaddr instrbytes in
      let currentpos = ch#pos in
      let instrlen = currentpos - prevpos in
      let instrbytes = String.sub bytestring prevpos instrlen in
      let instr = ARMI.make_arm_assembly_instruction iaddr false opcode instrbytes in
      ARMIS.set_arm_assembly_instruction instr
    done;
    let _ = set_block_boundaries () in
    let fn = construct_arm_assembly_function faddr in
    ARMFS.arm_assembly_functions#add_function fn;
    fn
  end

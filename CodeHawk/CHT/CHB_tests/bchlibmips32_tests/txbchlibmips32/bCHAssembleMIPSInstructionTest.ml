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

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSTypes

(* tchlib *)
module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

(* bchlib *)
module D = BCHDoubleword
module SI = BCHSystemInfo
module SW = BCHStreamWrapper
module U = BCHByteUtilities

(* bchlibmips32 *)
module R = BCHMIPSOpcodeRecords
module DIS = BCHDisassembleMIPSInstruction
module TF = BCHAssembleMIPSInstruction

module TR = CHTraceResult


let testname = "bCHAssembleMIPSInstructionTest"
let lastupdated = "2022-12-18"

let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)

let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:false s


let asm_move (rd: mips_reg_t) (rs: mips_reg_t): string =
  TF.assemble_mips_move_instruction ~bigendian:true rd rs


let asm_sw_stack (rs: mips_reg_t) (offset: int): string =
  TF.assemble_mips_sw_stack_instruction ~bigendian:true rs offset


let mips_assemble_move_be () =
  let tests = [
      ("move-a1-t9", asm_move MRa1 MRt9, "03202821  move     $a1, $t9");
      ("move-a2-a1", asm_move MRa2 MRa1, "00a03021  move     $a2, $a1");
      ("move-a3-a2", asm_move MRa3 MRa2, "00c03821  move     $a3, $a2");
      ("move-ra-s1", asm_move MRra MRs1, "0220f821  move     $ra, $s1");
      ("move-s1-ra", asm_move MRs1 MRra, "03e08821  move     $s1, $ra");
      ("move-t9-a0", asm_move MRt9 MRa0, "0080c821  move     $t9, $a0")
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_assemble_test_be") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let opcode = DIS.disassemble_mips_instruction D.wordzero instrbytes in
            let opcodetxt =
              bytes ^ "  " ^ (R.mips_opcode_to_string ~width:8 opcode) in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let mips_assemble_sw_be () =
  let tests = [
      ("sw-a3-10", asm_sw_stack MRa3 16, "afa70010  sw       $a3, 0x10($sp)")
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_assemble_test_be") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let opcode = DIS.disassemble_mips_instruction D.wordzero instrbytes in
            let opcodetxt =
              bytes ^ "  " ^ (R.mips_opcode_to_string ~width:8 opcode) in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end
  
  

let () =
  begin
    TS.new_testfile testname lastupdated;
    mips_assemble_move_be ();
    mips_assemble_sw_be ();
    TS.exit_file ()
  end

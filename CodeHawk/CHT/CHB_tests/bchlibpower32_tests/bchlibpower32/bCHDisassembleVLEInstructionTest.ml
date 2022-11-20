(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
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

(* bchlibpower32 *)
open BCHPowerTypes

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

(* bchlibpower32 *)
module R = BCHPowerOpcodeRecords
module TF = BCHDisassembleVLEInstruction


let testname = "bCHDisassembleVLEInsturctionTest"
let lastupdated = "2022-11-20"


let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:false s


let base = D.string_to_doubleword "0x400000"


(* 2-byte VLE16 opcodes, not pc-relative *)
let vle16_basic () =
  let tests = [
      ("se_addi",  "2027", "se_addi      r7, r7, 3");
      ("se_bctr",  "0006", "se_bctr");
      ("se_bctrl", "0007", "se_bctrl");
      ("se_bgeni", "6217", "se_bgeni     r7, 1");
      ("se_blr",   "0004", "se_blr");
      ("se_bmaski","2c03", "se_bmaski    r3, 0");
      ("se_bseti", "65f6", "se_bseti     r6, 31");
      ("se_cmpi",  "2a07", "se_cmpi      r7, 0");
      ("se_cmpl",  "0de7", "se_cmpl      r7, r30");
      ("se_cmpli", "2257", "se_cmpli     r7, 6");
      ("se_extzh", "00e6", "se_extzh     r6");
      ("se_lhz",   "00e6", "se_lwh       r6, 12(r31)");
      ("se_li",    "4817", "se_li        r7, 1");
      ("se_lwz",   "c07f", "se_lwz       r7, 0(r31)");
      ("se_mflr",  "0080", "se_mflr      r0");
      ("se_mr",    "0173", "se_mr        r3, r7");
      ("se_mtctr", "00b7", "se_mtctr     r7");
      ("se_mtlr",  "0090", "se_mtlr      r0");
      ("se_srawi", "6a24", "se_srawi     r4, r4, 2");
      ("se_stw",   "d701", "se_stw       r0, 28(r1)");
      ("se_subi",  "0637", "se_sub       r7, r3");

    ] in
  begin
    TS.new_testsuite (testname ^ "_vle16_basic") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let opcode = TF.disassemble_vle_instruction ch base instrbytes in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let () =
  begin
    vle16_basic ();
  end

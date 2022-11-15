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

(* bchlibarm32 *)
open BCHARMTypes

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

(* bchlibarm32 *)
module R = BCHARMOpcodeRecords
module TF = BCHDisassembleThumbInstruction


let testname = "bCHDisassembleThumbInstructionTest"
let lastupdated = "2022-11-14"


let two_byte_instr_opcode_tests = [
    ("04ac", "ADD            R4, SP, #0x10");
    ("7c44", "ADDS           R4, R4, PC");
    ("1e40", "AND            R6, R6, R3");
    ("7047", "BX             LR");
    ("102b", "CMP            R3, #0x10");
    ("9a42", "CMP            R2, R3");
    ("0099", "LDR            R1, [SP, #0]");
    ("9b78", "LDRB           R3, [R3, #2]");
    ("1988", "LDRH           R1, [R3, #0]");
    ("9b08", "LSRS           R3, R3, #0x2");
    ("1346", "MOV            R3, R2");
    ("2022", "MOVS           R2, #0x20");
    ("1e43", "ORRS           R6, R6, R3");
    ("90bd", "POP            {R4,R7,PC}");
    ("f0bd", "POP            {R4,R5,R6,R7,PC}");
    ("90b5", "PUSH           {R4,R7,LR}");
    ("f0b5", "PUSH           {R4,R5,R6,R7,LR}");
    ("02ba", "REV            R2, R0");    
    ("6dba", "REV16          R5, R5");
    ("5b42", "RSBS           R3, R3, #0x0");
    ("3560", "STR            R5, [R6, #0]");
    ("2170", "STRB           R1, [R4, #0]");
    ("8d80", "STRH           R5, [R1, #4]");
    ("85b0", "SUB            SP, SP, #0x14");
    ("ea1a", "SUBS           R2, R5, R3");
    ("c9b2", "UXTB           R1, R1");
    ("adb2", "UXTH           R5, R5")
  ]


let pc_relative_two_byte_opcode_tests = [
    ("0x112a8", "f1a7", "ADR            R7, 0x11670");
    ("0x11cf4", "e1e7", "B              0x11cba");
    ("0x11adc", "1bd2", "BCS            0x11b16");
    ("0x11cb8", "01d0", "BEQ            0x11cbe");
    ("0x11dbe", "33dc", "BGT            0x11e28");
    ("0x11ab8", "09d8", "BHI            0x11ace");
    ("0x113e6", "38dd", "BLE            0x1145a");
    ("0x111ea", "f9db", "BLT            0x111e0");
    ("0x11ccc", "f5d1", "BNE            0x11cba");
    ("0x11a52", "0bb9", "CBNZ           R3, 0x11a58");
    ("0x11d86", "13b1", "CBZ            R3, 0x11d8e");
    ("0x11ca8", "744c", "LDR            R4, 0x11e7c")
  ]


let four_byte_instr_opcode_tests = [
    ("0ceb8200", "ADD.W          R0, R12, R2,LSL #2");
    ("23f0ff03", "BIC            R3, R3, #0xff");
    ("5cf82230", "LDR.W          R3, [R12, R2,LSL #2]");
    ("9ef81040", "LDRB.W         R4, [LR, #16]");
    ("dee90201", "LDRD           R0, R1, [LR, #8]");
    ("4fea5002", "LSR.W          R2, R0, #0x1");
    ("0efb1202", "MLS            R2, LR, R2, R0");
    ("c8f20214", "MOVT           R4, #0x8102");
    ("40f20944", "MOVW           R4, #0x409");
    ("46f00046", "ORR            R6, R6, #0x80000000");
    ("41f8206f", "STR.W          R6, [R1, #32]!");
    ("4cf82630", "STR.W          R3, [R12, R6,LSL #2]");
    ("cde90023", "STRD           R2, R3, [SP, #0]");
    ("a4fb0232", "UMULL          R3, R2, R4, R2")
  ]

let two_byte_instr_opcode_failures = [
    ("03c4", "STM            R4!, {R0,R1}");  (* needs writeback register *)    
  ]

let four_byte_instr_opcode_failures = [
  ]    

let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:true s


let base = D.string_to_doubleword "0x400000"


let () =
  begin
    TS.new_testsuite testname lastupdated;

    (* 2-byte thumb opcodes *)
    List.iter (fun (bytes, result) ->
        TS.add_simple_test
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let opcode = TF.disassemble_thumb_instruction ch base instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) two_byte_instr_opcode_tests;            

    (* 2-byte pc-relative thumb opcodes *)
    SI.system_info#set_elf_is_code_address D.wordzero base;
    List.iter (fun (iaddr, bytes, result) ->
        TS.add_simple_test
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let iaddr = D.string_to_doubleword iaddr in
            let opcode = TF.parse_thumb_opcode ch base iaddr instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) pc_relative_two_byte_opcode_tests;

    (* 4-byte thumb opcodes *)
    List.iter (fun (bytes, result) ->
        TS.add_simple_test
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let opcode = TF.disassemble_thumb_instruction ch base instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) four_byte_instr_opcode_tests;

    TS.launch_tests ();
    exit 0
  end

        
  

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

module TR = CHTraceResult


let testname = "bCHDisassembleThumbInstructionTest"
let lastupdated = "2022-12-09"


let two_byte_instr_opcode_failures = [
    ("03c4", "STM            R4!, {R0,R1}");  (* needs writeback register *)    
  ]


let four_byte_instr_opcode_failures = [
  ]    


let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)


let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:true s


let base = make_dw "0x400000"


(* 2-byte thumb opcodes, not pc-relative *)
let thumb_2_basic () =
  let tests = [
      ("ADD",   "04ac", "ADD            R4, SP, #0x10");
      ("ADDS",  "7c44", "ADDS           R4, R4, PC");
      ("AND",   "1e40", "AND            R6, R6, R3");
      ("ASRS",  "4910", "ASRS           R1, R1, #0x1");
      ("BLX",   "9847", "BLX            R3");
      ("BX",    "7047", "BX             LR");
      ("CMP-i", "102b", "CMP            R3, #0x10");
      ("CMP-r", "9a42", "CMP            R2, R3");
      ("LDR",   "0099", "LDR            R1, [SP, #0]");
      ("LDRB",  "9b78", "LDRB           R3, [R3, #2]");
      ("LDRH",  "1988", "LDRH           R1, [R3, #0]");
      ("LSLS",  "c507", "LSLS           R5, R0, #0x1f");
      ("LSRS",  "9b08", "LSRS           R3, R3, #0x2");
      ("MOV",   "1346", "MOV            R3, R2");
      ("MOVS",  "2022", "MOVS           R2, #0x20");
      ("ORRS",  "1e43", "ORRS           R6, R6, R3");
      ("POP-3", "90bd", "POP            {R4,R7,PC}");
      ("POP-5", "f0bd", "POP            {R4,R5,R6,R7,PC}");
      ("PUSH-3","90b5", "PUSH           {R4,R7,LR}");
      ("PUSH-5","f0b5", "PUSH           {R4,R5,R6,R7,LR}");
      ("REV",   "02ba", "REV            R2, R0");
      ("REV16", "6dba", "REV16          R5, R5");
      ("RSBS",  "5b42", "RSBS           R3, R3, #0x0");
      ("STR",   "3560", "STR            R5, [R6, #0]");
      ("STRB",  "2170", "STRB           R1, [R4, #0]");
      ("STRH",  "8d80", "STRH           R5, [R1, #4]");
      ("SUB",   "85b0", "SUB            SP, SP, #0x14");
      ("SUBS",  "ea1a", "SUBS           R2, R5, R3");
      ("SXTH",  "36b2", "SXTH           R6, R6");
      ("UDF",   "ffde", "UDF            #0xff");
      ("UXTB",  "c9b2", "UXTB           R1, R1");
      ("UXTH",  "adb2", "UXTH           R5, R5")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_2_basic") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let opcode = TF.disassemble_thumb_instruction ch base instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* 2-byte thumb opcodes, pc-relative *)
let thumb_2_pc_relative () =
  let tests = [
      ("ADDS","0x11cde", "7b44", "ADDS           R3, R3, PC");
      ("ADR", "0x112a8", "f1a7", "ADR            R7, 0x11670");
      ("B",   "0x11cf4", "e1e7", "B              0x11cba");
      ("BCC", "0x1105c", "02d3", "BCC            0x11064");
      ("BCS", "0x11adc", "1bd2", "BCS            0x11b16");
      ("BEQ", "0x11cb8", "01d0", "BEQ            0x11cbe");
      ("BGT", "0x11dbe", "33dc", "BGT            0x11e28");
      ("BHI", "0x11ab8", "09d8", "BHI            0x11ace");
      ("BLE", "0x113e6", "38dd", "BLE            0x1145a");
      ("BLT", "0x111ea", "f9db", "BLT            0x111e0");
      ("BMI", "0x11744", "4bd4", "BMI            0x117de");
      ("BNE", "0x11ccc", "f5d1", "BNE            0x11cba");
      ("BPL", "0x117f6", "06d5", "BPL            0x11806");
      ("CBNZ","0x11a52", "0bb9", "CBNZ           R3, 0x11a58");
      ("CBZ", "0x11d86", "13b1", "CBZ            R3, 0x11d8e");
      ("LDR", "0x11ca8", "744c", "LDR            R4, 0x11e7c")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_2_pc_relative") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    SI.system_info#set_elf_is_code_address D.wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_thumb_instruction ch iaddr instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* 4-byte thumb opcodes, not pc-relative *)
let thumb_4_basic () =
  let tests = [
      ("ADD.W",  "0ceb8200", "ADD.W          R0, R12, R2,LSL #2");
      ("AND",    "01f47f03", "AND.W          R3, R1, #0xff0000");
      ("BIC",    "23f0ff03", "BIC            R3, R3, #0xff");
      ("CLZ",    "b3fa83f3", "CLZ            R3, R3");
      ("CMP.W",  "b3f56c0f", "CMP.W          R3, #0xec0000");
      ("DMB",    "bff35b8f", "DMB            ISH");
      ("LDM",    "95e80f00", "LDM            R5, {R0,R1,R2,R3}");
      ("LDR.W",  "5cf82230", "LDR.W          R3, [R12, R2,LSL #2]");
      ("LDRB.W", "9ef81040", "LDRB.W         R4, [LR, #16]");
      ("LDRD",   "dee90201", "LDRD           R0, R1, [LR, #8]");
      ("LDREX",  "54e8002f", "LDREX          R2, [R4, #0]");
      ("LDRH.W", "b2f84d20", "LDRH.W         R2, [R2, #77]");
      ("LSR.W",  "4fea5002", "LSR.W          R2, R0, #0x1");
      ("MLS",    "0efb1202", "MLS            R2, LR, R2, R0");
      ("MOVT",   "c8f20214", "MOVT           R4, #0x8102");
      ("MOVW",   "40f20944", "MOVW           R4, #0x409");
      ("MRC",    "1dee705f", "MRC           p15, 0,  R5, c13, c0, 3");
      ("MVN",    "6ff06300", "MVN            R0, #0x63");
      ("NOP",    "aff30080", "NOP           ");
      ("POP.W",  "bde83840", "POP.W          {R3,R4,R5,LR}");
      ("ORR",    "46f00046", "ORR            R6, R6, #0x80000000");
      ("PUSH.W", "2de9f041", "PUSH.W         {R4,R5,R6,R7,R8,LR}");
      ("RSB.W",  "c1f10001", "RSB.W          R1, R1, #0x0");
      ("STM.W",  "84e80f00", "STM.W          R4, {R0,R1,R2,R3}");
      ("STMDB",  "04e90f00", "STMDB.W        R4, {R0,R1,R2,R3}");
      ("STR.W-1","41f8206f", "STR.W          R6, [R1, #32]!");
      ("STR.W-2","4cf82630", "STR.W          R3, [R12, R6,LSL #2]");
      ("STRB.W", "83f81044", "STRB.W         R4, [R3, #1040]");
      ("STRD",   "cde90023", "STRD           R2, R3, [SP, #0]");
      ("STREX",  "44e80031", "STREX          R1, R3, [R4, #0]");
      ("STRH.W", "a4f84430", "STRH.W         R3, [R4, #68]");
      ("SUB.W",  "a6f17f01", "SUB.W          R1, R6, #0x7f");
      ("TBB",    "dfe800f0", "TBB            [PC, R0]");
      ("UBFX",   "c0f30743", "UBFX           R3, R0, #16, #8");
      ("UMULL",  "a4fb0232", "UMULL          R3, R2, R4, R2")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_4_basic") lastupdated;

    (* 4-byte thumb opcodes *)
    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let opcode = TF.disassemble_thumb_instruction ch base instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* 4-byte thumb opcodes, pc-relative *)
let thumb_4_pc_relative () =
  let tests = [
      ("B.W",     "0x11a7a", "24f1e3be", "B.W            0x136844");
      ("BEQ.W",   "0x1119e", "00f0ed81", "BEQ.W          0x1157c");
      ("BHI.W",   "0x11e6a", "3ff626af", "BHI.W          0x11cba");
      ("BLE.W",   "0x111a2", "40f3e181", "BLE.W          0x11568");
      ("BL-b",    "0x1030e", "fff757ff", "BL             0x101c0");
      ("BL-f",    "0x10340", "01f08cfa", "BL             0x1185c");
      ("BLX",     "0x110fa", "27f1baee", "BLX            0x138e70");
      ("BNE.W",   "0x1156e", "7ff40eae", "BNE.W          0x1118e");
      ("LDR.W",   "0x11184", "dff8fc64", "LDR.W          R6, 0x11684");
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_4_pc_relative") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    SI.system_info#set_elf_is_code_address D.wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_thumb_instruction ch iaddr instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    thumb_2_basic ();
    thumb_2_pc_relative ();
    thumb_4_basic ();
    thumb_4_pc_relative ();
    TS.exit_file ()
  end

  

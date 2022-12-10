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
module TF = BCHDisassembleARMInstruction

module TR = CHTraceResult


let testname = "bCHDisassembleARMInstructionTest"
let lastupdated = "2022-12-09"


let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)


let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:true s


let base = make_dw "0x400000"


let arm_basic_failures = [
    ("ANDS",   "0c001ae2", "AND            R0, R10, #0xc");  (* needs to be ANDS *)
    ("BFC",    "1f19dfe7", "BFC            R1, 18, 14"); (* should be R1, #18, #14 *)
    ("BIC",    "0e72c6e3", "BIC            R7, R6, #0x40000000");  (* should be #0xe0000000 *)
  ]


(* basic arm opcodes *)
let arm_basic () =
  let tests = [
      ("ADD",    "1cb08de2", "ADD            R11, SP, #0x1c");
      ("ADDEQ",  "ff108102", "ADDEQ          R1, R1, #0xff");
      ("AND",    "1f0001e2", "AND            R0, R1, #0x1f");
      ("ASR",    "c10fa0e1", "ASR            R0, R1, #0x1f");
      ("BX",     "1eff2fe1", "BX             LR");
      ("BXNE",   "1eff2f11", "BXNE           LR");
      ("CLZ",    "111f6fe1", "CLZ            R1, R1");
      ("CMN",    "010070e3", "CMN            R0, #0x1");
      ("CMP",    "010050e3", "CMP            R0, #0x1");
      ("CMPNE",  "00005111", "CMPNE          R1, R0,LSL #0");
      ("LDM",    "1c5091e8", "LDM            R1, {R2,R3,R4,R12,LR}");
      ("LDR",    "001094e5", "LDR            R1, [R4, #0]");
      ("LDRB",   "1000d5e5", "LDRB           R0, [R5, #16]");
      ("LDRBNE", "1000d515", "LDRBNE         R0, [R5, #16]");
      ("LDRD",   "d840c4e1", "LDRD           R4, R5, [R4, #8]");
      ("LSL",    "1200a0e1", "LSL            R0, R2, R0");
      ("MOV",    "0140a0e1", "MOV            R4, R1");
      ("MOVCC",  "0010a033", "MOVCC          R1, #0x0");
      ("MOVT",   "050040e3", "MOVT           R0, #0x5");      
      ("MOVW",   "e40e05e3", "MOVW           R0, #0x5ee4");
      ("MOVWEQ", "ff100003", "MOVWEQ         R1, #0xff");
      ("MOVWNE", "01000013", "MOVWNE         R0, #0x1");
      ("ORR",    "046087e3", "ORR            R6, R7, #0x4");
      ("POP",    "f08fbde8", "POP            {R4,R5,R6,R7,R8,R9,R10,R11,PC}");
      ("POPCC",  "108cbd38", "POPCC          {R4,R10,R11,PC}");
      ("POPEQ",  "f088bd08", "POPEQ          {R4,R5,R6,R7,R11,PC}");
      ("POPLT",  "108cbdb8", "POPLT          {R4,R10,R11,PC}");
      ("POPNE",  "108cbd18", "POPNE          {R4,R10,R11,PC}");
      ("PUSH",   "f04f2de9", "PUSH           {R4,R5,R6,R7,R8,R9,R10,R11,LR}");
      ("REV",    "321fbfe6", "REV            R1, R2");
      ("RSB",    "866366e0", "RSB            R6, R6, R6,LSL #7");
      ("SBCS",   "0510d1e0", "SBCS           R1, R1, R5,LSL #0");
      ("SMMLA",  "100256e7", "SMMLA          R6, R0, R2, R0");
      ("STM",    "1a0080e8", "STM            R0, {R1,R3,R4}");
      ("STMIB",  "21078de9", "STMIB          SP, {R0,R5,R8,R9,R10}");
      ("STR",    "38008de5", "STR            R0, [SP, #56]");
      ("STRCC",  "00118337", "STRCC          R1, [R3, R0,LSL #2]");
      ("STRB",   "0b00c4e5", "STRB           R0, [R4, #11]");
      ("STRBEQ", "0300c405", "STRBEQ         R0, [R4, #3]");
      ("STRD",   "f800c5e1", "STRD           R0, R1, [R5, #8]");
      ("STRH",   "b007cde1", "STRH           R0, [SP, #112]");
      ("SUB",    "45df4de2", "SUB            SP, SP, #0x114");
      ("SUBS",   "062052e0", "SUBS           R2, R2, R6,LSL #0");
      ("UBFX",   "50ede2e7", "UBFX           LR, R0, #26, #3");
      ("UXTB",   "7600efe6", "UXTB           R0, R6")
    ] in
  begin
    TS.new_testsuite (testname ^ "_arm_basic") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let opcode = TF.disassemble_arm_instruction ch base instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let arm_pc_relative () =
  let tests = [
      ("B",    "0x116f8", "060000ea", "B              0x11718");
      ("BEQ",  "0x10764", "f5ffff0a", "BEQ            0x10740");
      ("BGT",  "0x10434", "060000ca", "BGT            0x10454");
      ("BHI",  "0x10e14", "0400008a", "BHI            0x10e2c");
      ("BLE",  "0x10694", "480100da", "BLE            0x10bbc");
      ("BLX",  "0x10444", "661600fa", "BLX            0x15de4");
      ("BNE",  "0x1064c", "fbffff1a", "BNE            0x10640");
    ] in
  begin
    TS.new_testsuite (testname ^ "_arm_pc_relative") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    SI.system_info#set_elf_is_code_address D.wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_arm_instruction ch iaddr instrbytes in
            let opcodetxt = R.arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    arm_basic ();
    arm_pc_relative ();
    TS.exit_file ()
  end
                

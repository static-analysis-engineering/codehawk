(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2024  Aarno Labs LLC

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

(* tchlib *)
module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

module TR = CHTraceResult


(* bchlib *)
open BCHByteUtilities
open BCHDoubleword
open BCHStreamWrapper
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMOpcodeRecords
open BCHDisassembleARMInstruction


let testname = "bCHDisassembleARMInstructionTest"
let lastupdated = "2025-06-09"


let make_dw (s: string) = TR.tget_ok (string_to_doubleword s)


let make_stream ?(len=0) (s: string) =
  let bytestring = write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  make_pushback_stream ~little_endian:true s


let base = make_dw "0x400000"


(* basic arm opcodes *)
let arm_basic () =
  let tests = [
      ("ADD",    "1cb08de2", "ADD            R11, SP, #0x1c");
      ("ADDEQ",  "ff108102", "ADDEQ          R1, R1, #0xff");
      ("AND",    "1f0001e2", "AND            R0, R1, #0x1f");
      ("ASR",    "c10fa0e1", "ASR            R0, R1, #0x1f");
      ("BIC",    "0320c2e3", "BIC            R2, R2, #3");
      ("BX",     "1eff2fe1", "BX             LR");
      ("BXNE",   "1eff2f11", "BXNE           LR");
      ("CLZ",    "111f6fe1", "CLZ            R1, R1");
      ("CMN",    "010070e3", "CMN            R0, #1");
      ("CMP",    "010050e3", "CMP            R0, #1");
      ("CMPNE",  "00005111", "CMPNE          R1, R0");
      ("DMB",    "5bf07ff5", "DMB            ISH");
      ("LDC2",   "0181b0fc", "LDC2           p1, c8, [R0],#4");
      ("LDCL",   "02a1f0ec", "LDCL           p1, c10, [R0],#8");
      ("LDM",    "1c5091e8", "LDM            R1, {R2,R3,R4,R12,LR}");
      ("LDR",    "001094e5", "LDR            R1, [R4]");
      ("LDRB",   "1000d5e5", "LDRB           R0, [R5,#0x10]");
      ("LDRBNE", "1000d515", "LDRBNE         R0, [R5,#0x10]");
      ("LDRD",   "d840c4e1", "LDRD           R4, R5, [R4,#8]");
      ("LSL",    "1200a0e1", "LSL            R0, R2, R0");
      ("LSR",    "a662a0e1", "LSR            R6, R6, #5");
      ("MOV",    "0140a0e1", "MOV            R4, R1");
      ("MOVCC",  "0010a033", "MOVCC          R1, #0");
      ("MOVT",   "050040e3", "MOVT           R0, #5");
      ("MOVW",   "e40e05e3", "MOVW           R0, #0x5ee4");
      ("MOVWEQ", "ff100003", "MOVWEQ         R1, #0xff");
      ("MOVWNE", "01000013", "MOVWNE         R0, #1");
      ("MRS",    "00000fe1", "MRS            R0, CPSR");
      ("MRS_p",  "00304fe1", "MRS            R3, SPSR");
      ("MSR",    "93f021e3", "MSR            CPSR, #0x93");
      ("MSR_r",  "06f021e1", "MSR            CPSR, R6");
      ("MSR_p",  "03f061e1", "MSR            SPSR, R3");
      ("ORR",    "046087e3", "ORR            R6, R7, #4");
      ("POP",    "f08fbde8", "POP            {R4,R5,R6,R7,R8,R9,R10,R11,PC}");
      ("POPCC",  "108cbd38", "POPCC          {R4,R10,R11,PC}");
      ("POPEQ",  "f088bd08", "POPEQ          {R4,R5,R6,R7,R11,PC}");
      ("POPLT",  "108cbdb8", "POPLT          {R4,R10,R11,PC}");
      ("POPNE",  "108cbd18", "POPNE          {R4,R10,R11,PC}");
      ("PUSH",   "f04f2de9", "PUSH           {R4,R5,R6,R7,R8,R9,R10,R11,LR}");
      ("QADD",   "558006e1", "QADD           R8, R5, R6");
      ("QDADD",  "566048e1", "QDADD          R6, R6, R8");
      ("QDSUB",  "513063e1", "QDSUB          R3, R1, R3");
      ("QSUB",   "555026e1", "QSUB           R5, R5, R6");
      ("REV",    "321fbfe6", "REV            R1, R2");
      ("RSB",    "866366e0", "RSB            R6, R6, R6,LSL#7");
      ("SBCS",   "0510d1e0", "SBCS           R1, R1, R5");
      ("SMLABB", "840800e1", "SMLABB         R0, R4, R8, R0");
      ("SMLABT", "c50800e1", "SMLABT         R0, R5, R8, R0");
      ("SMLATB", "ac3700e1", "SMLATB         R0, R12, R7, R3");
      ("SMLATT", "e42703e1", "SMLATT         R3, R4, R7, R2");
      ("SMLAWB", "834e28e1", "SMLAWB         R8, R3, LR, R4");
      ("SMLAWT", "c03529e1", "SMLAWT         R9, R0, R5, R3");
      ("SMMLA",  "100256e7", "SMMLA          R6, R0, R2, R0");
      ("SMULBB", "840c63e1", "SMULBB         R3, R4, R12");
      ("SMULBT", "c80a65e1", "SMULBT         R5, R8, R10");
      ("SMULTB", "a30162e1", "SMULTB         R2, R3, R1");
      ("SMULTT", "e80a62e1", "SMULTT         R2, R8, R10");
      ("SMULL",  "9310c7e0", "SMULL          R1, R7, R3, R0");
      ("SMULWB", "a90523e1", "SMULWB         R3, R9, R5");
      ("SMULWT", "e00c23e1", "SMULWT         R3, R0, R12");
      ("STC2",   "0181a0fc", "STC2           p1, c8, [R0],#4");
      ("STCL",   "0201e0ec", "STCL           p1, c0, [R0],#8");
      ("STM",    "1a0080e8", "STM            R0, {R1,R3,R4}");
      ("STMDA",  "030003e8", "STMDA          R3, {R0,R1}");
      ("STMIB",  "21078de9", "STMIB          SP, {R0,R5,R8,R9,R10}");
      ("STR",    "38008de5", "STR            R0, [SP,#0x38]");
      ("STRwb",  "08402de5", "STR            R4, [SP,-#8]!");
      ("STRCC",  "00118337", "STRCC          R1, [R3,R0,LSL#2]");
      ("STRB",   "0b00c4e5", "STRB           R0, [R4,#0xb]");
      ("STRBEQ", "0300c405", "STRBEQ         R0, [R4,#3]");
      ("STRD",   "f800c5e1", "STRD           R0, R1, [R5,#8]");
      ("STRDwb", "fc406de1", "STRD           R4, R5, [SP,-#0xc]!");
      ("STRH",   "b007cde1", "STRH           R0, [SP,#0x70]");
      ("SUB",    "45df4de2", "SUB            SP, SP, #0x114");
      ("SUBS",   "062052e0", "SUBS           R2, R2, R6");
      ("TST",    "020c12e3", "TST            R2, #0x200");
      ("UBFX",   "50ede2e7", "UBFX           LR, R0, #26, #3");
      ("UDF",    "fedeffe7", "UDF            #0xfdee");
      ("UMLAL",  "9324a5e0", "UMLAL          R2, R5, R3, R4");
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
            let opcode = disassemble_arm_instruction ch base instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let arm_pc_relative () =
  let tests = [
      ("ADR-A1", "0xa01021d8", "80104fe2", "ADR            R1, 0xa0102160");
      ("ADR-A2", "0xa0354fc4", "14108fe2", "ADR            R1, 0xa0354fe0");
      ("B",    "0x116f8", "060000ea", "B              0x11718");
      ("BCS",  "0x118d4", "9d00002a", "BCS            0x11b50");
      ("BEQ",  "0x10764", "f5ffff0a", "BEQ            0x10740");
      ("BGT",  "0x10434", "060000ca", "BGT            0x10454");
      ("BHI",  "0x10e14", "0400008a", "BHI            0x10e2c");
      ("BLE",  "0x10694", "480100da", "BLE            0x10bbc");
      ("BLS",  "0x11e24", "3400009a", "BLS            0x11efc");
      ("BLX",  "0x10444", "661600fa", "BLX            0x15de4");
      ("BNE",  "0x1064c", "fbffff1a", "BNE            0x10640");
    ] in
  begin
    TS.new_testsuite (testname ^ "_arm_pc_relative") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    system_info#set_elf_is_code_address wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = disassemble_arm_instruction ch iaddr instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let arm_vector () =
  let tests = [
      ("FLDMIAX",                     "210b90ec",
       "FLDMIAX        R0, {D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15}");
      ("FSTMIAX",                     "210b80ec",
       "FSTMIAX        R0, {D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15}");
      ("VDUP.32",                     "474cfcf3", "VDUP.32        Q10, D7[1]");
      ("VDUP.32-scalar",              "622cfcf3", "VDUP.32        Q9, D18[1]");
      ("VEOR-Q",                      "746106f3", "VEOR           Q3, Q3, Q10");
      ("VEXT",                        "462cf0f2", "VEXT.8         Q9, Q0, Q3, #0xc");
      ("VLD1.8",                      "0d0760f4", "VLD1.8         {D16}, [R0]!");
      ("VLD1.32",                     "8f2a23f4", "VLD1.32        {D2,D3}, [R3]");
      ("VMOV.I8",                     "584ec0f2", "VMOV.I8        Q10, #8");
      ("VMOV.32-core-to-scalar",      "90cb25ee", "VMOV.32        D21[1], R12");
      ("VMOV-R-A1",                   "502120f2", "VMOV           Q1, Q0");
      ("VMSR",                        "101ae1ee", "VMSR           FPSCR, R1");
      ("VMULL.P64",                   "a94ea9f2", "VMULL.P64      Q2, D25, D25");
      ("VPOP",                        "108bbdec", "VPOP           {D8,D9,D10,D11,D12,D13,D14,D15}");
      ("VPUSH",                       "108b2bed", "VPUSH          {D8,D9,D10,D11,D12,D13,D14,D15}");
      ("VSHL-I-I8",                   "522589f2", "VSHL.I8        Q1, Q1, #1");
      ("VSHR.S32",                    "7220e1f2", "VSHR.S32       Q9, Q9, #0x1f");
      ("VSHR.U64",                    "d640c1f3", "VSHR.U64       Q10, Q3, #0x3f");
      ("VST1.8",                      "0f4a01f4", "VST1.8         {D4,D5}, [R1]");
      ("VST1.32",                     "8d6a02f4", "VST1.32        {D6,D7}, [R2]!");
      ("VST1.64",                     "cd8a40f4", "VST1.64        {D24,D25}, [R0]!");
      ("VTBL",                        "0449f6f3", "VTBL.8         D20, {D6,D7}, D4");
    ] in
  begin
    TS.new_testsuite (testname ^ "_arm_vector") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let opcode = disassemble_arm_instruction ch base instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* ARM-V8 crypto extension instructions *)
let armv8_crypto () =
  let tests = [
      ("AESD,8-A1",     "4043b0f3", "AESD.8         Q2, Q0");
      ("AESE.8-A1",     "0043b0f3", "AESE.8         Q2, Q0");
      ("AESIMC.8-A1",   "c443b0f3", "AESIMC.8       Q2, Q2");
      ("AESMC.8-A1",    "8443b0f3", "AESMC.8        Q2, Q2");
    ] in
  begin
    TS.new_testsuite (testname ^ "_arm_basic") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let opcode = disassemble_arm_instruction ch base instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    arm_basic ();
    arm_pc_relative ();
    arm_vector ();
    armv8_crypto ();
    TS.exit_file ()
  end

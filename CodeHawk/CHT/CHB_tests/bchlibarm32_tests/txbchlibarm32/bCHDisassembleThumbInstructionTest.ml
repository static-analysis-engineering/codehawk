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
open BCHDisassembleThumbInstruction
open BCHARMOpcodeRecords


let testname = "bCHDisassembleThumbInstructionTest"
let lastupdated = "2024-01-02"


let make_dw (s: string) = TR.tget_ok (string_to_doubleword s)


let make_stream ?(len=0) (s: string) =
  let bytestring = write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  make_pushback_stream ~little_endian:true s


let base = make_dw "0x400000"


(* 2-byte thumb opcodes, not pc-relative *)
let thumb_2_basic () =
  let tests = [
      ("ADCS-R-T1",  "4041", "ADCS           R0, R0, R0");
      ("ADD-SPI-T1", "04ac", "ADD            R4, SP, #0x10");
      ("ADDS-I-T2",  "0132", "ADDS           R2, R2, #1");
      ("ADDS-R-T2",  "7c44", "ADDS           R4, R4, PC");
      ("ADD-SPI-T2", "0ab0", "ADD            SP, SP, #0x28");
      ("AND-R-T1",   "1e40", "AND            R6, R6, R3");
      ("ASRS-I-T1",  "4910", "ASRS           R1, R1, #1");
      ("BKPT",       "fbbe", "BKPT           #0xfb");
      ("BLX-R-T1",   "9847", "BLX            R3");
      ("BX-T1",      "7047", "BX             LR");
      ("CMP-I-T1-1", "002f", "CMP            R7, #0");
      ("CMP-I-T1",   "102b", "CMP            R3, #0x10");
      ("CMP-R-T1",   "9a42", "CMP            R2, R3");
      ("CPSID-I",    "72b6", "CPSID          I");
      ("CPSIE-I",    "62b6", "CPSIE          I");
      ("LDR-I-T2",   "0099", "LDR            R1, [SP]");
      ("LDR-I-T2-o", "2d99", "LDR            R1, [SP,#0xb4]");
      ("LDRB-I-T1",  "9b78", "LDRB           R3, [R3,#2]");
      ("LDRH-I-T1",  "1988", "LDRH           R1, [R3]");
      ("LSLS-I-T1",  "c507", "LSLS           R5, R0, #0x1f");
      ("LSRS-I-T1",  "9b08", "LSRS           R3, R3, #2");
      ("MOV-R-T1",   "1346", "MOV            R3, R2");
      ("MOV-I-T1",   "0a27", "MOVS           R7, #0xa");
      ("MOVS-I-T1",  "2022", "MOVS           R2, #0x20");
      ("NOP",        "00bf", "NOP           ");
      ("ORRS-R-T1",  "1e43", "ORRS           R6, R6, R3");
      ("POP-3-T1",   "90bd", "POP            {R4,R7,PC}");
      ("POP-5-T1",   "f0bd", "POP            {R4,R5,R6,R7,PC}");
      ("PUSH-3-T1",  "90b5", "PUSH           {R4,R7,LR}");
      ("PUSH-5-T1",  "f0b5", "PUSH           {R4,R5,R6,R7,LR}");
      ("REV-T1",     "02ba", "REV            R2, R0");
      ("REV16-T1",   "6dba", "REV16          R5, R5");
      ("RSBS-I-T1",  "5b42", "RSBS           R3, R3, #0");
      ("STR-I-T1",   "3560", "STR            R5, [R6]");
      ("STRB-I-T1",  "2170", "STRB           R1, [R4]");
      ("STRH-I-T1",  "8d80", "STRH           R5, [R1,#4]");
      ("SUB-I-T1",   "7f1e", "SUBS           R7, R7, #1");
      ("SUB-SPI-T1", "85b0", "SUB            SP, SP, #0x14");
      ("SUBS-R-T1",  "ea1a", "SUBS           R2, R5, R3");
      ("SXTH-T1",    "36b2", "SXTH           R6, R6");
      ("UDF-T1",     "ffde", "UDF            #0xff");
      ("UXTB-T1",    "c9b2", "UXTB           R1, R1");
      ("UXTH-T1",    "adb2", "UXTH           R5, R5")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_2_basic") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let opcode = disassemble_thumb_instruction ch base instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* 2-byte thumb opcodes, pc-relative *)
let thumb_2_pc_relative () =
  let tests = [
      ("ADR-T1",   "0x112a8", "f1a7", "ADR            R7, 0x11670");
      ("B-T2",     "0x11cf4", "e1e7", "B              0x11cba");
      ("BCC-T1",   "0x1105c", "02d3", "BCC            0x11064");
      ("BCS-T1",   "0x11adc", "1bd2", "BCS            0x11b16");
      ("BEQ-T1",   "0x11cb8", "01d0", "BEQ            0x11cbe");
      ("BGT-T1",   "0x11dbe", "33dc", "BGT            0x11e28");
      ("BHI-T1",   "0x11ab8", "09d8", "BHI            0x11ace");
      ("BLE-T1",   "0x113e6", "38dd", "BLE            0x1145a");
      ("BLT-T1+",  "0x108fe", "11db", "BLT            0x10924");
      ("BLT-T1",   "0x111ea", "f9db", "BLT            0x111e0");
      ("BMI-T1",   "0x11744", "4bd4", "BMI            0x117de");
      ("BNE-T1",   "0x11ccc", "f5d1", "BNE            0x11cba");
      ("BPL-T1",   "0x117f6", "06d5", "BPL            0x11806");
      ("CBNZ-T1",  "0x11a52", "0bb9", "CBNZ           R3, 0x11a58");
      ("CBZ-T1-1", "0x108fe", "8fb1", "CBZ            R7, 0x10924");
      ("CBZ-T1-2", "0x11d86", "13b1", "CBZ            R3, 0x11d8e");
      ("LDR-L-T1", "0x11ca8", "744c", "LDR            R4, 0x11e7c")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_2_pc_relative") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    system_info#set_elf_is_code_address wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let iaddr = make_dw iaddr in
            let opcode = disassemble_thumb_instruction ch iaddr instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* 4-byte thumb opcodes, not pc-relative *)
let thumb_4_basic () =
  let tests = [
      ("ADC.W-I-T1",  "43f1000c", "ADC.W          R12, R3, #0");
      ("ADC.W-R-T2",  "4eeb0b0e", "ADC.W          LR, LR, R11");
      ("ADD.W-I-T3",  "13f1ff33", "ADDS.W         R3, R3, #0xffffffff");
      ("ADD.W-R-T3",  "0ceb8200", "ADD.W          R0, R12, R2,LSL#2");
      ("AND-I-T1",    "01f47f03", "AND.W          R3, R1, #0xff0000");
      ("BIC-I-T1",    "23f0ff03", "BIC            R3, R3, #0xff");
      ("CLZ-T1",      "b3fa83f3", "CLZ            R3, R3");
      ("CMP.W-T2",    "b3f56c0f", "CMP.W          R3, #0xec0000");
      ("DMB-T1",      "bff35b8f", "DMB            ISH");
      ("EOR.W-T2",    "80ea0c0c", "EOR.W          R12, R0, R12");
      ("LDC2",        "b0fc0181", "LDC2           p1, c8, [R0],#4");
      ("LDM-T2",      "95e80f00", "LDM            R5, {R0,R1,R2,R3}");
      ("LDR.W-T2",    "5cf82230", "LDR.W          R3, [R12,R2,LSL#2]");
      ("LDRB.W-T2",   "9ef81040", "LDRB.W         R4, [LR,#0x10]");
      ("LDRD-T1-off", "dee90201", "LDRD           R0, R1, [LR,#8]");
      ("LDRD-T1-post","f4e80201", "LDRD           R0, R1, [R4],#8");
      ("LDREX-T1",    "54e8002f", "LDREX          R2, [R4]");
      ("LDRH.W-I-T2", "b2f84d20", "LDRH.W         R2, [R2,#0x4d]");
      ("LSR.W-I-T2",  "4fea5002", "LSR.W          R2, R0, #1");
      ("MLS-T1",      "0efb1202", "MLS            R2, LR, R2, R0");
      ("MOVT-T1",     "c8f20214", "MOVT           R4, #0x8102");
      ("MOVW-I-T3",   "40f20944", "MOVW           R4, #0x409");
      ("MRC-T1",      "1dee705f", "MRC            p15, 0, R5, c13, c0, 3");
      ("MRRC",        "51ec1e0f", "MRRC           p15, 1, R0, R1, c14");
      ("MVN-T1",      "6ff06300", "MVN            R0, #0x63");
      ("NOP-T2",      "aff30080", "NOP           ");
      ("ORR-I-T1",    "46f00046", "ORR            R6, R6, #0x80000000");
      ("PLD-I",       "90f840f0", "PLD            [R0,#0x40]");
      ("POP.W-T2",    "bde83840", "POP.W          {R3,R4,R5,LR}");
      ("PUSH.W-T2",   "2de9f041", "PUSH.W         {R4,R5,R6,R7,R8,LR}");
      ("RBIT",        "90faa0f0", "RBIT           R0, R0");
      ("REV16.W",     "9bfa9bfb", "REV16.W        R11, R11");
      ("ROR.W",       "66fa0cf6", "ROR.W          R6, R6, R12");
      ("RSB.W-T2",    "c1f10001", "RSB.W          R1, R1, #0");
      ("STC2",        "a0fc0181", "STC2           p1, c8, [R0],#4");
      ("STM.W-T2",    "84e80f00", "STM.W          R4, {R0,R1,R2,R3}");
      ("STMDB-T1",    "04e90f00", "STMDB          R4, {R0,R1,R2,R3}");
      ("STR.W-I-T4",  "41f8206f", "STR.W          R6, [R1,#0x20]!");
      ("STR.W-R-T2",  "4cf82630", "STR.W          R3, [R12,R6,LSL#2]");
      ("STRB.W-T3",   "83f81044", "STRB.W         R4, [R3,#0x410]");
      ("STRD-T1",     "cde90023", "STRD           R2, R3, [SP]");
      ("STRD-T1-8",   "cde90278", "STRD           R7, R8, [SP,#8]");
      ("STREX-T1",    "44e80031", "STREX          R1, R3, [R4]");
      ("STRH.W-T2",   "a4f84430", "STRH.W         R3, [R4,#0x44]");
      ("SUB.W-T3",    "a6f17f01", "SUB.W          R1, R6, #0x7f");
      ("SUBW-T4",     "a0f20107", "SUBW           R7, R0, #1");
      ("TBB-T1",      "dfe800f0", "TBB            [PC,R0]");
      ("UBFX-T1",     "c0f30743", "UBFX           R3, R0, #16, #8");
      ("UDIV",        "b6fbf1f2", "UDIV           R2, R6, R1");
      ("UMLAL",       "e8fb0a23", "UMLAL          R2, R3, R8, R10");
      ("UMULL-T1",    "a4fb0232", "UMULL          R3, R2, R4, R2");
      ("UQSUB8",      "ccfa52f4", "UQSUB8         R4, R12, R2");
      ("USAT",        "80f30100", "USAT           R0, #1, R0");
      ("UXTAB",       "52fa81f5", "UXTAB          R5, R2, R1");
      ("UXTAH",       "12fa84f4", "UXTAH          R4, R2, R4");
      ("UXTB.W",      "5ffa83fe", "UXTB.W         LR, R3");
      ("UXTH.W",      "1ffa83f8", "UXTH.W         R8, R3");
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
            let opcode = disassemble_thumb_instruction ch base instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* 4-byte thumb opcodes, pc-relative *)
let thumb_4_pc_relative () =
  let tests = [
      ("B.W-T3?",    "0x7200",  "f9f73ebe", "B.W            0xe80");
      ("B.W-T3??",   "0xe7c",   "06f0bcb9", "B.W            0x71f8");
      ("B.W-T4",     "0x11a7a", "24f1e3be", "B.W            0x136844");
      ("BEQ.W-T3",   "0x1119e", "00f0ed81", "BEQ.W          0x1157c");
      ("BHI.W-T3",   "0x11e6a", "3ff626af", "BHI.W          0x11cba");
      ("BLE.W-T3",   "0x111a2", "40f3e181", "BLE.W          0x11568");
      ("BL-b-T1",    "0x1030e", "fff757ff", "BL             0x101c0");
      ("BL-f-T1",    "0x10340", "01f08cfa", "BL             0x1185c");
      ("BLX-T2",     "0x110fa", "27f1baee", "BLX            0x138e70");
      ("BNE.W-T3",   "0x1156e", "7ff40eae", "BNE.W          0x1118e");
      ("LDR.W-T2",   "0x11184", "dff8fc64", "LDR.W          R6, 0x11684");
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_4_pc_relative") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    system_info#set_elf_is_code_address wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let iaddr = make_dw iaddr in
            let opcode = disassemble_thumb_instruction ch iaddr instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


(* 4-byte thumb vector instructions *)
let thumb_4_vector () =
  let tests = [
      ("FLDMIAX-T1",                  "90ec210b", "FLDMIAX        R0, {D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15}");
      ("VABS.F64",                    "b0eec07b", "VABS.F64       D7, D0");
      ("VADD.F32-T2",                 "77ee877a", "VADD.F32       S15, S15, S14");
      ("VADD.F64-T2",                 "37ee067b", "VADD.F64       D7, D7, D6");
      ("VADD-I-T1",                   "72efee28", "VADD.I64       Q9, Q9, Q15");
      ("VADDL-u-T1",                  "aaff2ea0", "VADDL.U32      Q5, D10, D30");
      ("VAND-T1",                     "40eff201", "VAND           Q8, Q8, Q9");
      ("VBIC-I-T1-1",                 "c7ff3c07", "VBIC.I32       D16, #0xfc000000");
      ("VCMPE.F64-T1-double",         "b4eec07b", "VCMPE.F64      D7, D0");
      ("VCMPE.F64.T2-double",         "b5eec00b", "VCMPE.F64      D0, #0.0");
      ("VCVT.F32.U32-single-from-T1", "b8ee470a", "VCVT.F32.U32   S0, S14");
      ("VCVT.F64.F32-ds-T1",          "b7eec00a", "VCVT.F64.F32   D0, S0");
      ("VCVT.F64.S32-double-from-T1", "b8eee77b", "VCVT.F64.S32   D7, S15");
      ("VCVT.F64.U32",                "bbeeee0b", "VCVT.F64.U32   D0, D0, #3");
      ("VDIV.F32",                    "80ee270a", "VDIV.F32       S0, S0, S15");
      ("VDIV.F64",                    "87ee067b", "VDIV.F64       D7, D7, D6");
      ("VDUP.8-scalar",               "ffff472c", "VDUP.8         Q9, D7[7]");
      ("VEOR-Q",                      "06ff7061", "VEOR           Q3, Q3, Q8");
      ("VFMA.F64",                    "a6ee047b", "VFMA.F64       D7, D6, D4");
      ("VLD1.8",                      "6cf90d82", "VLD1.8         {D24,D25,D26,D27}, [R12]!");
      ("VLD1.32-1",                   "20f99d07", "VLD1.32        {D0}, [R0:64]!");
      ("VLD1.32-4",                   "60f99d42", "VLD1.32        {D20,D21,D22,D23}, [R0:64]!");
      ("VLD1.32-one-lane",            "a0f90f28", "VLD1.32        {D2[0]}, [R0]");
      ("VLD1.32-all-lanes",           "e8f9bdcc", "VLD1.32        {D28[],D29[]}, [R8:32]!");
      ("VLD4.32-one-lane",            "a0f94dab", "VLD4.32        {D10[0],D12[0],D14[0],D16[0]}, [R0]!");
      ("VLD4.32-multiple-2",          "61f98f41", "VLD4.32        {D20,D22,D24,D26}, [R1]");
      ("VLDM-T1",                     "90ec200b", "VLDM           R0, {D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15}");
      ("VLDR-imm",                    "dded108b", "VLDR           D24, [SP,#0x40]");
      ("VMLA.F64",                    "07ee052b", "VMLA.F64       D2, D7, D5");
      ("VMLAL.U32-by-scalar-T2",      "a7ff62a2", "VMLAL.U32      Q5, D7, D2[1]");
      ("VMOV.32-core-to-scalar",      "0aee102b", "VMOV.32        D10[0], R2");
      ("VMOV-core-to-sp-T1",          "07ee907a", "VMOV           S15, R7");
      ("VMOV.F32-I",                  "b7ee00aa", "VMOV.F32       S20, #0x3f800000");
      ("VMOV.F32-R",                  "f0ee418a", "VMOV.F32       S17, S2");
      ("VMOVDDS",                     "53ec172b", "VMOV           R2, R3, D7");
      ("VMOVDSS",                     "41ec170b", "VMOV           D7, R0, R1");
      ("VMOVN.I64",                   "faff2002", "VMOVN.I64      D16, Q8");
      ("VMRS-T1",                     "f1ee10fa", "VMRS           APSR_nzcv, FPSCR");
      ("VMSR-T1",                     "e1ee102a", "VMSR           FPSCR, R2");
      ("VMUL.F64-T2",                 "27ee0bbb", "VMUL.F64       D11, D7, D11");
      ("VMULL.P64",                   "a0ef000e", "VMULL.P64      Q0, D0, D0");
      ("VMULL.U32-by-scalar-T2",      "a0ff60aa", "VMULL.U32      Q5, D0, D0[1]");
      ("VNEG.F64",                    "b1ee400b", "VNEG.F64       D0, D0");
      ("VNMLS.F64",                   "12ee063b", "VNMLS.F64      D3, D2, D6");
      ("VORN-quad",                   "30ef5001", "VORN           Q0, Q0, Q0");
      ("VORR-R-D",                    "27ef3a71", "VORR           D7, D7, D26");
      ("VPOP-T1",                     "bdec0a8b", "VPOP           {D8,D9,D10,D11,D12}");
      ("VRHADD.U16",                  "1eff2fe1", "VRHADD.U16     D14, D14, D31");
      ("VSHL.I32",                    "e2ef3ee5", "VSHL.I32       D30, D30, #2");
      ("VSHR.S8",                     "c9ef7220", "VSHR.S8        Q9, Q9, #7");
      ("VSHR.U32",                    "e6ff1ae0", "VSHR.U32       D30, D10, #0x1a");
      ("VSHR.U64",                    "a6ffda80", "VSHR.U64       Q4, Q5, #0x1a");
      ("VSHRN.I64",                   "e6ef32e8", "VSHRN.I64      D30, Q9, #0x1a");
      ("VST1.32-1",                   "00f99d07", "VST1.32        {D0}, [R0:64]!");
      ("VST1.32-4",                   "40f99d42", "VST1.32        {D20,D21,D22,D23}, [R0:64]!");
      ("VST1.32-one-lane",            "80f90f28", "VST1.32        {D2[0]}, [R0]");
      ("VST4.32-one-lane",            "86f90d0b", "VST4.32        {D0[0],D1[0],D2[0],D3[0]}, [R6]!");
      ("VSUB.F64-T2",                 "3cee47cb", "VSUB.F64       D12, D12, D7");
      ("VTRN.32",                     "baff8a00", "VTRN.32        D0, D10");
      ("VZIP.16",                     "f6ff88c1", "VZIP.16        D28, D8");
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_4_vector") lastupdated;

    (* 4-byte thumb opcodes *)
    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let opcode = disassemble_thumb_instruction ch base instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let thumb_armv8_crypto () =
  let tests = [
      ("AESE.8",            "b0ff0003", "AESE.8         Q0, Q0");
      ("SHA1C.32",          "00ef400c", "SHA1C.32       Q0, Q0, Q0");
      ("SHA1H.32",          "b9ffc062", "SHA1H.32       Q3, Q0");
      ("SHA1P.32",          "16ef6a0c", "SHA1P.32       Q0, Q3, Q13");
      ("SHA1SU0.32",        "3aef4c8c", "SHA1SU0.32     Q4, Q5, Q6");
      ("SHA1SU1.32",        "baff8e83", "SHA1SU1.32     Q4, Q7");
      ("SHA256H.32",        "00ff400c", "SHA256H.32     Q0, Q0, Q0");
      ("SHA256H2.32",       "14ff682c", "SHA256H2.32    Q1, Q2, Q12");
      ("SHA256SU0.32",      "faffe423", "SHA256SU0.32   Q9, Q10");
      ("SHA256SU1.32",      "64ffe60c", "SHA256SU1.32   Q8, Q10, Q11");
      ("VBSL",              "50ffb1d1", "VBSL           D29, D16, D17");
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_armv8_crypto") lastupdated;

    (* 4-byte thumb opcodes *)
    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_ui16 in
            let opcode = disassemble_thumb_instruction ch base instrbytes in
            let opcodetxt = arm_opcode_to_string ~width:14 opcode in
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
    thumb_4_vector ();
    thumb_armv8_crypto();
    TS.exit_file ()
  end

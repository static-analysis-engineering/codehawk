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

module TR = CHTraceResult


let testname = "bCHDisassembleVLEInstructionTest"
let lastupdated = "2023-02-07"


let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)


let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:false s


let base = make_dw "0x4000000"


(* 2-byte VLE16 opcodes, not pc-relative *)
let vle16_basic () =
  let tests = [
      ("se_add",   "04b6", "se_add       r6, r27");
      ("se_addi",  "2027", "se_addi      r7, 0x3");
      ("se_and",   "4656", "se_and       r6, r5");
      ("se_andc",  "45cf", "se_andc      r31, r28");
      ("se_andi",  "2e16", "se_andi      r6, 0x1");
      ("se_bclri", "6006", "se_bclri     r6, 0x0");
      ("se_bctr",  "0006", "se_bctr");
      ("se_bctrl", "0007", "se_bctrl");
      ("se_bgeni", "6217", "se_bgeni     r7, 0x1");
      ("se_blr",   "0004", "se_blr");
      ("se_bmaski","2c03", "se_bmaski    r3, 0x0");
      ("se_bseti", "65f6", "se_bseti     r6, 0x1f");
      ("se_btsti", "6787", "se_btsti     r7, 0x18");
      ("se_cmp",   "0cfe", "se_cmp       r30, r31");
      ("se_cmpi",  "2a07", "se_cmpi      r7, 0x0");
      ("se_cmpl",  "0de7", "se_cmpl      r7, r30");
      ("se_cmpli", "2257", "se_cmpli     r7, 0x6");
      ("se_extsb", "00d7", "se_extsb     r7");
      ("se_extsh", "00f7", "se_extsh     r7");
      ("se_extzb", "00c7", "se_extzb     r7");
      ("se_extzh", "00e6", "se_extzh     r6");
      ("se_isync", "0001", "se_isync");
      ("se_lhz",   "a66f", "se_lhz       r6, 12(r31)");
      ("se_li",    "4817", "se_li        r7, 0x1");
      ("se_lbz",   "8277", "se_lbz       r7, 2(r7)");
      ("se_lwz",   "c07f", "se_lwz       r7, 0(r31)");
      ("se_mfar",  "0331", "se_mfar      r1, r11");
      ("se_mfctr", "00a0", "se_mfctr     r0");
      ("se_mflr",  "0080", "se_mflr      r0");
      ("se_mr",    "0173", "se_mr        r3, r7");
      ("se_mtar",  "023e", "se_mtar      r22, r3");
      ("se_mtctr", "00b7", "se_mtctr     r7");
      ("se_mtlr",  "0090", "se_mtlr      r0");
      ("se_mullw", "0576", "se_mullw     r6, r7");
      ("se_neg",   "0037", "se_neg       r7");
      ("se_not",   "0026", "se_not       r6");
      ("se_or",    "4400", "se_or        r0, r0");
      ("se_rfdi",  "000a", "se_rfdi");
      ("se_rfi",   "0008", "se_rfi");
      ("se_rfmci", "000b", "se_rfmci");
      ("se_slw",   "4276", "se_slw       r6, r7");
      ("se_srw",   "4046", "se_srw       r6, r4");
      ("se_slwi",  "6c46", "se_slwi      r6, r6, 0x4");
      ("se_sraw",  "41d7", "se_sraw      r7, r29");
      ("se_srawi", "6a24", "se_srawi     r4, r4, 0x2");
      ("se_srwi",  "69f7", "se_srwi      r7, 0x1f");
      ("se_stb",   "987f", "se_stb       r7, 8(r31)");
      ("se_stw",   "d701", "se_stw       r0, 28(r1)");
      ("se_sub",   "0637", "se_sub       r7, r3");
      ("se_subf",  "0757", "se_subf      r7, r5");
      ("se_subi",  "2406", "se_subi      r6, 0x1");

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


(* 4-byte VLE32 opcodes, not pc-relative *)
let vle32_basic () =
  let tests = [
      ("e_add16i",   "1c6321f8", "e_add16i     r3, r3, 0x21f8");
      ("e_add2is",   "73069010", "e_add2is     r6, -0x3ff0");
      ("e_addi",     "18a584ff", "e_addi       r5, r5, -0x1");
      ("e_addic",    "1be794ff", "e_addic      r31, r7, -0x1");
      ("e_and2is.",  "70efeff0", "e_and2is.    r7, 0x7ff0");
      ("e_andi",     "18e7c230", "e_andi       r7, r7, 0x300000");
      ("e_andi.",    "18e6c803", "e_andi.      r6, r7, 0x3");
      ("e_clrlwi",   "74e7007f", "e_clrlwi     r7, r7, 0x1");
      ("e_clrrwi",   "74e7002b", "e_clrrwi     r7, r7, 0xa");
      ("e_cmp16i",   "700799ff", "e_cmp16i     r7, 0x1ff");
      ("e_cmpl16i",  "7005a83f", "e_cmpl16i    r5, 0x3f");
      ("e_cmpli",    "1887af3f", "e_cmpli      cr0, r7, 0x3fffffff");
      ("e_cror",     "7fbdcb82", "e_cror       4*cr7+gt, 4*cr7+gt, 4*cr6+gt");
      ("e_cror_",    "7c3d0b82", "e_cror       gt, 4*cr7+gt, gt");
      ("e_extrwi",   "74e7ffff", "e_extrwi     r7, r7, 0x1, 0x1e");
      ("e_insrwi",   "74c4f800", "e_insrwi     r4, r6, 0x1, 0x0");
      ("e_insrwi_",  "74a4007e", "e_insrwi     r4, r5, 0x1f, 0x1");
      ("e_lbz" ,     "30ff0010", "e_lbz        r7, 16(r31)");
      ("e_lbzu",     "188a0001", "e_lbzu       r4, 1(r10)");
      ("e_lhz",      "58e70020", "e_lhz        r7, 32(r7)");
      ("e_li",       "70780520", "e_li         r3, 0xc520");
      ("e_li(h)",    "71400000", "e_li         r10, 0x0");
      ("e_lis",      "707fe700", "e_lis        r3, -0x100");
      ("e_lis(h)",   "7142e001", "e_lis        r10, 0x1001");
      ("e_lmvgprw",  "18011024", "e_lmvgprw    36(r1)");
      ("e_lmvsprw",  "18211014", "e_lmvsprw    20(r1)");
      ("e_lmvssrw",  "1881100c", "e_lmvsrrw    12(r1)");
      ("e_lmw",      "1b810808", "e_lmw        r28, 8(r1)");
      ("e_lwz",      "50fffff8", "e_lwz        r7, -8(r31)");
      ("e_lwzu",     "18ff02fc", "e_lwzu       r7, -4(r31)");
      ("e_mcrf",     "7f800020", "e_mcrf       cr7, cr0");
      ("e_mull2i",   "7007a3e8", "e_mull2i     r7, 0x3e8");
      ("e_mulli",    "1880a4fc", "e_mulli      r4, r0, -0x4");
      ("e_or2i",     "7060c10a", "e_or2i       r3, 0x10a");
      ("e_or2is",    "7000d200", "e_or2is      r0, 0x200");
      ("e_ori",      "18e7d144", "e_ori        r7, r7, 0x4400");
      ("e_rlw",      "7cc73a30", "e_rlw        r7, r6, r7");
      ("e_rlwinm",   "74c6ca11", "e_rlwinm     r6, r6, 0x19, 0x8, 0x8");
      ("e_slwi",     "7ce61070", "e_slwi       r6, r7, 0x2");
      ("e_srwi",     "7fa48470", "e_srwi       r4, r29, 0x10");
      ("e_stb",      "34fc21fc", "e_stb        r7, 8700(r28)");
      ("e_stbu",     "18850401", "e_stbu       r4, 1(r5)");
      ("e_sth",      "5cc70038", "e_sth        r6, 56(r7)");
      ("e_stmvgprw", "18011124", "e_stmvgprw   36(r1)");
      ("e_stmvsprw", "18211114", "e_stmvsprw   20(r1)");
      ("e_stmvsrrw", "1881110c", "e_stmvsrrw   12(r1)");
      ("e_stmw",     "1b810908", "e_stmw       r28, 8(r1)");
      ("e_stw",      "54640010", "e_stw        r3, 16(r4)");
      ("e_stw_",     "54fffff8", "e_stw        r7, -8(r31)");
      ("e_stwu",     "180106c0", "e_stwu       r0, -64(r1)");
      ("e_subfic",   "1884b000", "e_subfic     r4, r4, 0x0");
      ("e_subfic_",  "18c6b482", "e_subfic     r6, r6, -0x7e");
      ("e_xori",     "18e7e001", "e_xori       r7, r7, 0x1")
    ] in
  begin
    TS.new_testsuite (testname ^ "_vle32_basic") lastupdated;

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


(* b-byte VLE32 opcodes, pc-relative *)
let vle32_pc_relative () =
  let tests = [
      ("e_b",     "0x82d8ee", "79fffe82", "e_b          0x82d770");
      ("e_bdnz",  "0x800626", "7a20ffe0", "e_bdnz       0x800606");
      ("e_bdz",   "0x82da28", "7a300012", "e_bdz        0x82da3a");
      ("e_beq",   "0x82fcaa", "7a120010", "e_beq        0x82fcba");
      ("e_beq_1", "0x812338", "7a160162", "e_beq        cr1, 0x81249a");
      ("e_beq_2", "0x8131e4", "7a1a0006", "e_beq        cr2, 0x8131ea");
      ("e_bge",   "0x8118c4", "7a00001c", "e_bge        0x8118e0");
      ("e_bge_1", "0x82d83a", "7a04001a", "e_bge        cr1, 0x82d854");
      ("e_bge_3", "0x82e0c0", "7a0c0078", "e_bge        cr3, 0x82e138");
      ("e_bgt",   "0x81232c", "7a110178", "e_bgt        0x8124a4");
      ("e_bgt_1", "0x82d7b6", "7a15ffea", "e_bgt        cr1, 0x82d7a0");
      ("e_bl",    "0x82d910", "7800010d", "e_bl         0x82da1c");
      ("e_ble",   "0x811836", "7a010016", "e_ble        0x81184c");
      ("e_ble_3", "0x82f17e", "7a0d0034", "e_ble        cr3, 0x82f1b2");
      ("e_blt",   "0x8118dc", "7a10ffec", "e_blt        0x8118c8");
      ("e_blt_1", "0x813662", "7a14005c", "e_blt        cr1, 0x8136be");
      ("e_blt_3", "0x82e1d2", "7a1c0066", "e_blt        cr3, 0x82e238");
      ("e_bne",   "0x81189a", "7a02006a", "e_bne        0x811904");
      ("e_bne_1", "0x82d7a6", "7a06fff0", "e_bne        cr1, 0x82d796");
      ("e_bne_3", "0x82f1b2", "7a0e001a", "e_bne        cr3, 0x82f1cc")
    ] in
  begin
    TS.new_testsuite (testname ^ "_vle32_pc_relative") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    SI.system_info#set_elf_is_code_address D.wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            try
              let ch = make_stream bytes in
              let instrbytes = ch#read_ui16 in
              let iaddr = make_dw iaddr in
              let opcode = TF.disassemble_vle_instruction ch iaddr instrbytes in
              let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
              A.equal_string result opcodetxt
            with BCH_failure p ->
              pr_debug [STR "Error: "; p; NL])) tests;
    TS.launch_tests ()
  end


(* 4-byte non-VLE opcodes used in VLE32, not pc-relative *)
let nonvle_basic () =
  let tests = [
      ("add",     "7cc51a14", "add          r6, r5, r3");
      ("addc",    "7d1f2814", "addc         r8, r31, r5");
      ("adde",    "7cfe2114", "adde         r7, r30, r4");
      ("addme",   "7fc601d4", "addme        r30, r6");
      ("addze.",  "7c840195", "addze.       r4, r4");
      ("and",     "7d673838", "and          r7, r11, r7");
      ("andc",    "7ce52878", "andc         r5, r7, r5");
      ("cmplw",   "7c9e3040", "cmplw        cr1, r30, r6");
      ("cmpw",    "7c832000", "cmpw         cr1, r3, r4");
      ("cntlzw",  "7ca70034", "cntlzw       r7, r5");
      ("crnot",   "7fdde842", "crnot        4*cr7+eq, 4*cr7+gt");
      ("divw",    "7ce63bd6", "divw         r7, r6, r7");
      ("divwu",   "7fc62396", "divwu        r30, r6, r4");
      ("extsh",   "7ce60734", "extsh        r6, r7");
      ("iseleq",  "7c67189e", "iseleq       r3, r7, r3");
      ("iselgt",  "7ca5485e", "iselgt       r5, r5, r9");
      ("isellt",  "7fe7f81e", "isellt       r31, r7, r31");
      ("lbzx",    "7cc438ae", "lbzx         r6, r4, r7");
      ("lwzx",    "7cfd302e", "lwzx         r7, r29, r6");
      ("mbar",    "7c0006ac", "mbar         0x0");
      ("mfcr",    "7c000026", "mfcr         r0");
      ("mfmsr",   "7c0000a6", "mfmsr        r0");
      ("mfxer",   "7c0102a6", "mfxer        r0");
      ("mtcr",    "7c0ff120", "mtcr         r0");
      ("mtcrf",   "7d810120", "mtcrf        0x10, r12");
      ("mtctr",   "7c2903a6", "mtctr        r1");
      ("mtlr",    "7fe803a6", "mtlr         r31");
      ("mtmsr",   "7c600124", "mtmsr        r3");
      ("mtspr",   "7c3a0ba6", "mtspr        0x3a, r1");
      ("mulhwu",  "7ca6e016", "mulhwu       r5, r6, r28");
      ("mullw",   "7ffe21d6", "mullw        r31, r30, r4");
      ("neg",     "7cc700d0", "neg          r6, r7");
      ("not",     "7d6b58f8", "not          r11, r11");
      ("or",      "7c862b78", "or           r6, r4, r5");
      ("slw",     "7cdf3830", "slw          r31, r6, r7");
      ("sraw",    "7c674e30", "sraw         r7, r3, r9");
      ("srawi",   "7c06fe70", "srawi        r6, r0, 0x1f");
      ("srw",     "7fe52c30", "srw          r5, r31, r5");
      ("stbx",    "7cc339ae", "stbx         r6, r3, r7");
      ("stwux",   "7c21016e", "stwux        r1, r1, r0");
      ("stwx",    "7c05312e", "stwx         r0, r5, r6");
      ("subf",    "7cbe3050", "subf         r5, r30, r6");
      ("subfc",   "7ceb4810", "subfc        r7, r11, r9");
      ("subfe",   "7cca4110", "subfe        r6, r10, r8");
      ("subfze",  "7c630190", "subfze       r3, r3");
      ("tlbwe",   "7c0007a4", "tlbwe");
      ("wrteei_0","7c000146", "wrteei       0");
      ("wrteei_1","7c008146", "wrteei       1");
      ("xor",     "7d5e1a78", "xor          r30, r10, r3");
    ] in
  begin
    TS.new_testsuite (testname ^ "_nonvle_basic") lastupdated;

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
    TS.new_testfile testname lastupdated;
    vle16_basic ();
    vle32_basic ();
    vle32_pc_relative ();
    nonvle_basic ();
    TS.exit_file ()
  end

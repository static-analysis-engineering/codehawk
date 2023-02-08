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
module TF = BCHDisassemblePowerInstruction

module TR = CHTraceResult


let testname = "bCHDisassemblePowerInstructionTest"
let lastupdated = "2023-02-07"


let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)


let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:false s


let base = make_dw "0x4000000"

(* opcode-31 opcodes, not pc-relative *)

let opcode_7_opcodes () =
  let tests = [
      ("addi",       "38610040", "addi         r3, r1, 0x40");
      ("addic",      "3108ffff", "addic        r8, r8, -0x1");
      ("li",         "3860ffff", "li           r3, -0x1");
      ("lis",        "3cc016be", "lis          r6, 0x16be");
      ("mulli",      "1ce7004c", "mulli        r7, r7, 0x4c");
      ("subfic",     "20e7001f", "subfic       r7, r7, 0x1f");
    ] in
  begin
    TS.new_testsuite (testname ^ "_opcode_7_opcodes") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instr = ch#read_doubleword in
            let opcode = TF.disassemble_power_instruction ch base instr in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let opcode_10_11_opcodes () =
  let tests = [
      ("cmplwi",     "2b830080", "cmplwi       cr7, r3, 0x80");
      ("cmpwi",      "2f84ffff", "cmpwi        cr7, r4, -0x1")
    ] in
  begin
    TS.new_testsuite (testname ^ "_opcode_10_11_opcodes") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instr = ch#read_doubleword in
            let opcode = TF.disassemble_power_instruction ch base instr in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end
  

let opcode_16_opcodes () =
  let tests = [
      ("bdnz",    "0x800630", "4200ffd8", "bdnz         0x800608");
      ("bdz",     "0x834bd4", "42400014", "bdz          0x834be8");
      ("beq",     "0x8349f0", "41820060", "beq          0x834a50");
      ("beq_cr1", "0x8390b0", "41860008", "beq          cr1, 0x8390b8");
      ("beq_cr7", "0x811914", "419e0010", "beq          cr7, 0x811924");
      ("beq+_cr7","0x834c2c", "41be000c", "beq+         cr7, 0x834c38");
      ("beq-",    "0x8360a8", "41a2ff68", "beq-         0x836010");
      ("beq-_cr7","0x8119cc", "41beffe4", "beq-         cr7, 0x8119b0");
      ("bge_cr6", "0x83492c", "40980020", "bge          cr6, 0x83494c");
      ("bge_cr7", "0x8118dc", "409c0028", "bge          cr7, 0x811904");
      ("bge+_cr7","0x834a1c", "40bc0038", "bge+         cr7, 0x834a54");
      ("bge-_cr7","0x837c08", "40bcfde4", "bge-         cr7, 0x8379ec");
      ("bgt_cr6", "0x8363ac", "4199ffe4", "bgt          cr6, 0x836390");
      ("bgt_cr7", "0x814a14", "419d0018", "bgt          cr7, 0x814a2c");
      ("bgt+_cr7","0x834fc8", "41bd0014", "bgt+         cr7, 0x834fdc");
      ("bgt-_cr7","0x837d10", "41bdfcd8", "bgt-         cr7, 0x8379e8");
      ("ble_cr7", "0x816350", "409dff98", "ble          cr7, 0x8162e8");
      ("ble+_cr7","0x835290", "40bd0028", "ble+         cr7, 0x8352b8");
      ("ble-_cr7","0x83963c", "40bdffb0", "ble-         cr7, 0x8395ec");
      ("blt",     "0x835860", "4180000c", "blt          0x83586c");
      ("blt_cr7", "0x811900", "419cffe0", "blt          cr7, 0x8118e0");
      ("blt+_cr6","0x834950", "41b8003c", "blt+         cr6, 0x83498c");
      ("blt-",    "0x8348f8", "41a0ff60", "blt-         0x834858");
      ("bne",     "0x83525c", "4082001c", "bne          0x835278");
      ("bne_cr7", "0x8118ac", "409e0080", "bne          cr7, 0x81192c");
      ("bne+",    "0x834854", "40a2001c", "bne+         0x834870");
      ("bne+_cr7","0x8347f8", "40be0010", "bne+         cr7, 0x834808");
      ("bne-_cr7","0x838704", "40beff60", "bne-         cr7, 0x838664");
  ] in
  begin
    TS.new_testsuite (testname ^ "_opcode_16_opcodes") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    SI.system_info#set_elf_is_code_address D.wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            try
              let ch = make_stream bytes in
              let instr = ch#read_doubleword in
              let iaddr = make_dw iaddr in
              let opcode = TF.disassemble_power_instruction ch iaddr instr in
              let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
              A.equal_string result opcodetxt
            with BCH_failure p ->
              pr_debug [STR "Error: "; p; NL])) tests;
    TS.launch_tests ()
  end


let opcode_18_opcodes () =
  let tests = [
      ("b",       "0x83843c", "4bfffe74", "b            0x8382b0");
      ("bl",      "0x8377e8", "48000e2d", "bl           0x838614");
    ] in
  begin
    TS.new_testsuite (testname ^ "_opcode_18_opcodes") lastupdated;

    (* set code extent so checks on absolute code addresses pass *)
    SI.system_info#set_elf_is_code_address D.wordzero base;
    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            try
              let ch = make_stream bytes in
              let instr = ch#read_doubleword in
              let iaddr = make_dw iaddr in
              let opcode = TF.disassemble_power_instruction ch iaddr instr in
              let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
              A.equal_string result opcodetxt
            with BCH_failure p ->
              pr_debug [STR "Error: "; p; NL])) tests;
    TS.launch_tests ()
  end


let opcode_19_opcodes_npc () =
  let tests = [
      ("bctr",       "4e800420", "bctr");
      ("beqlr_cr7",  "4d9e0020", "beqlr        cr7");
      ("beqlr",      "4d820020", "beqlr");
      ("beqlr+_cr7", "4dbe0020", "beqlr+       cr7");
      ("bgtlr_cr7",  "4d9d0020", "bgtlr        cr7");
      ("blelr+cr7",  "4c9d0020", "blelr        cr7");
      ("blr",        "4e800020", "blr");
      ("bnelr_0",    "4c820020", "bnelr");
      ("bnelr+",     "4ca20020", "bnelr+");
      ("crnot",      "4fdde842", "crnot        4*cr7+eq, 4*cr7+gt");
      ("isync",      "4c00012c", "isync");
      ("rfdi",       "4c00004e", "rfdi");
      ("rfi",        "4c000064", "rfi");
      ("rfmci",      "4c00004c", "rfmci");
    ] in
  begin
    TS.new_testsuite (testname ^ "_opcode_19_opcodes_npc") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instr = ch#read_doubleword in
            let opcode = TF.disassemble_power_instruction ch base instr in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let opcode_20_opcodes () =
  let tests = [
      ("clrlslwi",   "54c6416e", "clrlslwi     r6, r6, 0xd, 0x8");
      ("clrlwi",     "5503063e", "clrlwi       r3, r8, 0x18");
      ("clrrwi",     "54a8002e", "clrrwi       r8, r5, 0x8");
      ("extrwi",     "54c7ca7e", "extrwi       r7, r6, 0x17, 0x2");
      ("insrwi",     "50a6f800", "insrwi       r6, r5, 0x1, 0x0");
      ("rlwinm",     "54e706b4", "rlwinm       r7, r7, 0x0, 0x1a, 0x1a");
      ("rotlw",      "5cc7383e", "rotlw        r7, r6, r7");
      ("slwi",       "548b083c", "slwi         r11, r4, 0x1");
    ] in
  begin
    TS.new_testsuite (testname ^ "_opcode_20_opcodes") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instr = ch#read_doubleword in
            let opcode = TF.disassemble_power_instruction ch base instr in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let opcode_24_29_opcodes () =
  let tests = [
      ("andi.",      "70e70003", "andi.        r7, r7, 0x3");
      ("andis.",     "74667ff0", "andis.       r6, r3, 0x7ff0");
      ("ori",        "6084f359", "ori          r4, r4, 0xf359");
      ("oris",       "64c60010", "oris         r6, r6, 0x10");
      ("xori",       "68e70001", "xori         r7, r7, 0x1");
      ("xoris",      "6ce7ffff", "xoris        r7, r7, 0xffff");
    ] in
  begin
    TS.new_testsuite (testname ^ "_opcode_24_29_opcodes") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instr = ch#read_doubleword in
            let opcode = TF.disassemble_power_instruction ch base instr in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end  
  
  
let opcode_31_opcodes () =
  let tests = [
      ("add",        "7ce63a14", "add          r7, r6, r7");
      ("addc",       "7d08d014", "addc         r8, r8, r26");
      ("adde",       "7ce7c914", "adde         r7, r7, r25");
      ("addme",      "7ce701d4", "addme        r7, r7");
      ("addze",      "7c840195", "addze.       r4, r4");
      ("and",        "7cc63838", "and          r6, r6, r7");
      ("andc",       "7fffe078", "andc         r31, r31, r28");
      ("cmplw",      "7f87f040", "cmplw        cr7, r7, r30");
      ("cmpw",       "7f863800", "cmpw         cr7, r6, r7");
      ("cntlzw",     "7ca60034", "cntlzw       r6, r5");
      ("divw",       "7ce63bd6", "divw         r7, r6, r7");
      ("divwu",      "7cc63b96", "divwu        r6, r6, r7");
      ("eieio",      "7c0006ac", "eieio        0x0");
      ("extsb",      "7ce70774", "extsb        r7, r7");
      ("extsh",      "7ce70734", "extsh        r7, r7");
      ("isel_7eq",   "7c671f9e", "isel         r3, r7, r3, 4*cr7+eq");
      ("isel_7lt",   "7ce63f1e", "isel         r7, r6, r7, 4*cr7+lt");
      ("iseleq",     "7fe0389e", "iseleq       r31, 0x0, r7");
      ("isellt",     "7f60381e", "isellt       r27, 0x0, r7");
      ("lbzx",       "7ce638ae", "lbzx         r7, r6, r7");
      ("lwzx",       "7cfd302e", "lwzx         r7, r29, r6");
      ("mfcr",       "7c000026", "mfcr         r0");
      ("mfctr",      "7c0902a6", "mfctr        r0");
      ("mflr",       "7c0802a6", "mflr         r0");
      ("mfmsr",      "7cc000a6", "mfmsr        r6");
      ("mfxer",      "7c0102a6", "mfxer        r0");
      ("mr",         "7ce33b78", "mr           r3, r7");
      ("mtcr",       "7c2ff120", "mtcr         r1");
      ("mtcrf",      "7d808120", "mtcrf        0x8, r12");      
      ("mtctr",      "7c2903a6", "mtctr        r1");
      ("mtlr",       "7fe803a6", "mtlr         r31");
      ("mtmsr",      "7cc00124", "mtmsr        r6");
      ("mtspr",      "7c709ba6", "mtspr        0x270, r3");
      ("mtxer",      "7c2103a6", "mtxer        r1");
      ("mulhwu",     "7cf8d016", "mulhwu       r7, r24, r26");
      ("mullw",      "7cc639d6", "mullw        r6, r6, r7");
      ("neg",        "7ce700d0", "neg          r7, r7");
      ("not",        "7ce738f8", "not          r7, r7");
      ("or",         "7cc73b78", "or           r7, r6, r7");
      ("slw",        "7ce73030", "slw          r7, r7, r6");
      ("sraw",       "7cfdee30", "sraw         r29, r7, r29");
      ("srawi",      "7c841670", "srawi        r4, r4, 0x2");
      ("srw",        "7cc73c30", "srw          r7, r6, r7");
      ("stbx",       "7ca639ae", "stbx         r5, r6, r7");
      ("stwx",       "7c05312e", "stwx         r0, r5, r6");
      ("subf",       "7ce33850", "subf         r7, r3, r7");
      ("subfc",      "7d083010", "subfc        r8, r8, r6");
      ("subfe",      "7ce72910", "subfe        r7, r7, r5");
      ("subfze",     "7ce70190", "subfze       r7, r7");
      ("wrteei",     "7c008146", "wrteei       1");
      ("tlbwe",      "7c0007a4", "tlbwe");
      ("xor",        "7cc73a78", "xor          r7, r6, r7");
    ] in
  begin
    TS.new_testsuite (testname ^ "_opcode_31_opcodes") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instr = ch#read_doubleword in
            let opcode = TF.disassemble_power_instruction ch base instr in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let load_opcodes () =
  let tests = [
      ("lbz",        "88e70004", "lbz          r7, 4(r7)");
      ("lbzu",       "8cc70001", "lbzu         r6, 1(r7)");
      ("lbzu_",      "8cc4ffff", "lbzu         r6, -1(r4)");
      ("lhz",        "a0ff000c", "lhz          r7, 12(r31)");
      ("lmw",        "bba1000c", "lmw          r29, 12(r1)");
      ("lwz",        "80e1000c", "lwz          r7, 12(r1)");
      ("lwz_",       "83abfff4", "lwz          r29, -12(r11)");
      ("lwzu",       "879e0004", "lwzu         r28, 4(r30)");
      ("lwzu_",      "84fffffc", "lwzu         r7, -4(r31)");
    ] in
  begin
    TS.new_testsuite (testname ^ "_load_opcodes") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instr = ch#read_doubleword in
            let opcode = TF.disassemble_power_instruction ch base instr in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end
  

let store_opcodes () =
  let tests = [
      ("stb",        "98c7000c", "stb          r6, 12(r7)");
      ("stbu_",      "9cc7ffff", "stbu         r6, -1(r7)");
      ("sth",        "b0ff0008", "sth          r7, 8(r31)");
      ("stmw",       "bfc10008", "stmw         r30, 8(r1)");
      ("stw",        "91640008", "stw          r11, 8(r4)");
      ("stwu",       "94670018", "stwu         r3, 24(r7)");
    ] in
  begin
    TS.new_testsuite (testname ^ "_store_opcodes") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instr = ch#read_doubleword in
            let opcode = TF.disassemble_power_instruction ch base instr in
            let opcodetxt = R.power_opcode_to_string ~width:12 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end

let () =
  begin
    TS.new_testfile testname lastupdated;
    opcode_7_opcodes ();
    opcode_10_11_opcodes ();
    opcode_16_opcodes ();
    opcode_18_opcodes ();
    opcode_19_opcodes_npc ();
    opcode_20_opcodes ();
    opcode_24_29_opcodes ();
    opcode_31_opcodes ();
    load_opcodes ();
    store_opcodes ();
    TS.exit_file ()
  end
             

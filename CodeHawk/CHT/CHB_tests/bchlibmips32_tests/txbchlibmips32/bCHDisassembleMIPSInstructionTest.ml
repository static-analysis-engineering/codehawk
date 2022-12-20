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
module TF = BCHDisassembleMIPSInstruction

module TR = CHTraceResult


let testname = "bCHDisassembleMIPSInstructionTest"
let lastupdated = "2022-12-13"


let make_dw (s: string) = TR.tget_ok (D.string_to_doubleword s)

let missing_I_opcodes = [
    "ldc1";
    "ll";
    "lwc1";
    "mfc2";
    "mfhc2";
    "mtc2";
    "pref";
    "sc";
    "sdc1";
    "swc1"
  ]

let missing_I_opcode_branches = [
    "bgezal";
    "bltzal";    
    "teqi";
    "blezl";
  ]

let missing_R_opcode = [
    "add",
    "mthi",
    "mtlo",
    "sub"
  ]

let missing_R2_opcode = [
    "madd";
    "maddu"
  ]

let missing_R3_opcode = [
    "ext";
    "ins";
    "rdhwr";
    "seb";
    "seh";
    "wsbh"
  ]


let make_stream ?(len=0) (s: string) =
  let bytestring = U.write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  SW.make_pushback_stream ~little_endian:false s


let mips_I_opcode_be () =
  let tests = [
      ("addi",  "0x494db8", "23bdff8c", "addi     $sp, $sp, -116");
      ("addiu", "0x494d84", "27bdffe8", "addiu    $sp, $sp, -24");
      ("andi",  "0x405dbc", "304200ff", "andi     $v0, $v0, 255");
      ("lb",    "0x405db0", "8083ffff", "lb       $v1, -0x1($a0)");
      ("lbu",   "0x405538", "92840004", "lbu      $a0, 0x4($s4)");
      ("lh",    "0x406d00", "84430000", "lh       $v1, ($v0)");
      ("lhu",   "0x406bfc", "94430000", "lhu      $v1, ($v0)");
      ("li",    "0x405da8", "2406002e", "li       $a2, 46");
      ("lui",   "0x40525c", "3c03004a", "lui      $v1, 74");
      ("lw",    "0x41b778", "8fbc0018", "lw       $gp, 0x18($sp)");
      ("lwl",   "0x41b78c", "88440000", "lwl      $a0, ($v0)");
      ("lwr",   "0x41b79c", "98440003", "lwr      $a0, 0x3($v0)");
      ("ori",   "0x40a0d0", "34460080", "ori      $a2, $v0, 128");
      ("sb",    "0x40554c", "a0440004", "sb       $a0, 0x4($v0)");
      ("sh",    "0x408bf4", "a7a00024", "sh       $zero, 0x24($sp)");
      ("slti",  "0x410af4", "28a20004", "slti     $v0, $a1, 4");
      ("sltiu", "0x405dc4", "2c42000a", "sltiu    $v0, $v0, 10");
      ("subu",  "0x40526c", "00431023", "subu     $v0, $v0, $v1");
      ("sw",    "0x40555c", "ae220000", "sw       $v0, ($s1)");
      ("swl",   "0x405540", "a8430000", "swl      $v1, ($v0)");
      ("swr",   "0x405548", "b8430003", "swr      $v1, 0x3($v0)");
      ("xori",  "0x408850", "3882000a", "xori     $v0, $a0, 10")
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_I_opcode_be") lastupdated;

    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_mips_instruction iaddr instrbytes in
            let opcodetxt = R.mips_opcode_to_string ~width:8 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let mips_I_opcode_be_branch () =
  let tests = [
      ("beq",   "0x4053e8", "10510011", "beq      $v0, $s1, 0x405430");
      ("beql",  "0x46d7bc", "50820054", "beql     $a0, $v0, 0x46d910");
      ("bgez",  "0x411b38", "04e1ffde", "bgez     $a3, 0x411ab4");
      ("bgezl", "0x46f0c4", "04a30007", "bgezl    $a1, 0x46f0e4");
      ("bgtz",  "0x407820", "1e40ffe1", "bgtz     $s2, 0x4077a8");
      ("bgtzl", "0x46ef20", "5c400005", "bgtzl    $v0, 0x46ef38");
      ("blez",  "0x40778c", "1a4001ae", "blez     $s2, 0x407e48");
      ("bltz",  "0x411aa8", "04e00025", "bltz     $a3, 0x411b40");
      ("bltzl", "0x46d864", "04620005", "bltzl    $v1, 0x46d87c");
      ("bne",   "0x405560", "1615ffdf", "bne      $s0, $s5, 0x4054e0");
      ("bnel",  "0x46dd90", "5462000a", "bnel     $v1, $v0, 0x46ddbc");
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_I_opcode_be_branch") lastupdated;

    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_mips_instruction iaddr instrbytes in
            let opcodetxt = R.mips_opcode_to_string ~width:8 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let mips_J_opcode_be () =
  let tests = [
      ("j",   "0x409d80", "0810267c", "j        0x4099f0");
      ("jal", "0x407e1c", "0c101d62", "jal      0x407588")
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_J_opcode_be") lastupdated;

    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_mips_instruction iaddr instrbytes in
            let opcodetxt = R.mips_opcode_to_string ~width:8 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let mips_R_opcode_be () =
  let tests = [
      ("addu",    "0x405160", "0399e021", "addu     $gp, $gp, $t9");
      ("and",     "0x4051f8", "03a1e824", "and      $sp, $sp, $at");
      ("div",     "0x415744", "0043001a", "div      $v0, $v1");
      ("divu",    "0x44b090", "00be001b", "divu     $a1, $fp");
      ("jalr-t9", "0x40518c", "0320f809", "jalr     $ra, $t9");
      ("jr-ra",   "0x4051c0", "03e00008", "jr       $ra");
      ("jr-t9",   "0x405340", "03200008", "jr       $t9");
      ("mfhi",    "0x411898", "00002010", "mfhi     $a0");
      ("mflo",    "0x415750", "00001812", "mflo     $v1");
      ("movn",    "0x415964", "0102180b", "movn     $v1, $t0, $v0");
      ("movz",    "0x40678c", "0090800a", "movz     $s0, $a0, $s0");
      ("mult",    "0x411890", "00440018", "mult     $v0, $a0");
      ("multu",   "0x4615d4", "00440019", "multu    $v0, $a0");
      ("nop",     "0x405178", "00000000", "<nop>");
      ("nor",     "0x40b28c", "00033027", "nor      $a2, $zero, $v1");
      ("or",      "0x406ce4", "00451025", "or       $v0, $v0, $a1");
      ("sll",     "0x40529c", "00041880", "sll      $v1, $a0, 2");
      ("sllv",    "0x411ae0", "00ed1004", "sllv     $v0, $t5, $a3");
      ("slt",     "0x407780", "0212802a", "slt      $s0, $s0, $s2");
      ("sltu",    "0x4052a0", "0050102b", "sltu     $v0, $v0, $s0");
      ("sra",     "0x405270", "00021083", "sra      $v0, $v0, 2");
      ("srav",    "0x411acc", "00ea4007", "srav     $t0, $t2, $a3");
      ("srl",     "0x40b290", "00032e02", "srl      $a1, $v1, 24");
      ("srlv",    "0x46d804", "00851806", "srlv     $v1, $a1, $a0");
      ("teq",     "0x415748", "006001f4", "teq      $v1, $zero");
      ("xor",     "0x40b29c", "00451026", "xor      $v0, $v0, $a1");
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_R_opcode_be") lastupdated;

    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_mips_instruction iaddr instrbytes in
            let opcodetxt = R.mips_opcode_to_string ~width:8 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end
 

let mips_R2_opcode_be () =
  let tests = [
      ("clz",   "0x46e094", "70a21020", "clz      $v0, $a1");
      ("mul",   "0x4118ac", "70832802", "mul      $a1, $a0, $v1")
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_R2_opcode_be") lastupdated;

    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_mips_instruction iaddr instrbytes in
            let opcodetxt = R.mips_opcode_to_string ~width:8 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let mips_R3_opcode_be () =
  let tests = [
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_R3_opcode_be") lastupdated;

    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_mips_instruction iaddr instrbytes in
            let opcodetxt = R.mips_opcode_to_string ~width:8 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end


let mips_test_code_be () =
  let tests = [
      ("li-32",    "0x494da4", "24060020", "li       $a2, 32");
      ("li-256",   "0x494da4", "24060100", "li       $a2, 256");
      ("jal-patch","0x414248", "0c125361", "jal      0x494d84");
      ("move-a0",  "0x41424c", "02802021", "move     $a0, $s4");
      ("sp-dec-20","0x45fe78", "27bdffec", "addiu    $sp, $sp, -20");
      ("sw-ra",    "0x40516c", "afbf0010", "sw       $ra, 0x10($sp)");
      ("lw-t9",    "0x494d98", "8f9983e0", "lw       $t9, -0x7c20($gp)");
      ("jalr-t9",  "0x40518c", "0320f809", "jalr     $ra, $t9");
      ("nop",      "0x405178", "00000000", "<nop>");      
      ("lw-ra",    "0x4052d4", "8fbf0010", "lw       $ra, 0x10($sp)");
      ("jr-ra",    "0x4051c0", "03e00008", "jr       $ra");      
      ("sp-inc-4", "0x45ff34", "27bd0014", "addiu    $sp, $sp, 20");
      ("move-a3",  "0x494db4", "00063821", "move     $a3, $a2");
      ("move-a2",  "0x494db8", "00053021", "move     $a2, $a1");
      ("move-a1",  "0x494bdc", "00192821", "move     $a1, $t9");
      ("lw-t9-s",  "0x494bc0", "8f998788", "lw       $t9, -0x7878($gp)")
    ] in
  begin
    TS.new_testsuite (testname ^ "_mips_test_code_be") lastupdated;

    List.iter (fun (title, iaddr, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let ch = make_stream bytes in
            let instrbytes = ch#read_doubleword in
            let iaddr = make_dw iaddr in
            let opcode = TF.disassemble_mips_instruction iaddr instrbytes in
            let opcodetxt = R.mips_opcode_to_string ~width:8 opcode in
            A.equal_string result opcodetxt)) tests;

    TS.launch_tests ()
  end
  
  
  

let () =
  begin
    TS.new_testfile testname lastupdated;
    mips_I_opcode_be ();
    mips_I_opcode_be_branch ();
    mips_J_opcode_be ();
    mips_R_opcode_be ();
    mips_R2_opcode_be ();
    mips_R3_opcode_be ();
    mips_test_code_be ();
    TS.exit_file ()
  end

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


module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

module BA = TCHBchlibAssertion
module BG = TCHBchlibGenerator
module BS = TCHBchlibSpecification

module ARMA = TCHBchlibarm32Assertion
module ARMU = TCHBchlibarm32Utils


(* chutil *)
module TR = CHTraceResult

(* bchlib *)
open BCHDoubleword
open BCHLibTypes
open BCHSystemInfo
open BCHStreamWrapper
open BCHByteUtilities

(* bchlibarm32 *)
open BCHARMTypes
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHDisassembleThumbInstruction
open BCHDisassembleARMInstruction
open BCHARMInstructionAggregate


let testname = "bCHARMJumptableTest"
let lastupdated = "2024-01-02"


let make_dw (s: string) = TR.tget_ok (string_to_doubleword s)


let codemax = make_dw "0x400000"


let make_stream ?(len=0) (s: string) =
  let bytestring = write_hex_bytes_to_bytestring s in
  let s = (String.make len ' ') ^ bytestring in
  make_pushback_stream ~little_endian:true s


let add_instruction
      (_pos: int)
      (iaddr: doubleword_int)
      (opcode: arm_opcode_t)
      (bytes: string) =
  let instr = make_arm_assembly_instruction iaddr false opcode bytes in
  begin
    set_arm_assembly_instruction instr;
    instr
  end

let jt_setup_thumb hexbase bytes: arm_jumptable_int TR.traceresult =
  let base = make_dw hexbase in
  let bytestring = write_hex_bytes_to_bytestring bytes in
  let ch = make_stream bytes in
  let aggregate = ref None in
  let size = String.length bytestring in
  begin
    while ch#pos + 2 < size do
      let prevpos = ch#pos in
      let iaddr = base#add_int ch#pos in
      let instrbytes = ch#read_ui16 in
      let opcode = disassemble_thumb_instruction ch iaddr instrbytes in
      let currentpos = ch#pos in
      let instrlen = currentpos - prevpos in
      let instrbytes = String.sub bytestring prevpos instrlen in
      let instr = add_instruction prevpos iaddr opcode instrbytes in
      let optagg = identify_arm_aggregate ch instr in
      match optagg with
      | Some agg -> aggregate := Some agg
      | _ -> ()
    done;
    match !aggregate with
    | Some agg ->
       (match agg#kind with
        | ARMJumptable jt ->
           (* let _ = pr_debug [jt#toPretty; NL; NL] in *)
           Ok jt
          | _ -> Error ["other aggregate found"])
    | _ ->
       Error ["no aggregate found:" ^ (string_of_int ch#pos)]
  end


let jt_setup_arm hexbase bytes: arm_jumptable_int TR.traceresult =
  let base = make_dw hexbase in
  let bytestring = write_hex_bytes_to_bytestring bytes in
  let ch = make_stream bytes in
  let aggregate = ref None in
  let size = String.length bytestring in
  begin
    while ch#pos + 4 <= size do
      let prevpos = ch#pos in
      let iaddr = base#add_int ch#pos in
      let instrbytes = ch#read_doubleword in
      let opcode = disassemble_arm_instruction ch iaddr instrbytes in
      let currentpos = ch#pos in
      let instrlen = currentpos - prevpos in
      let instrbytes = String.sub bytestring prevpos instrlen in
      let instr = add_instruction prevpos iaddr opcode instrbytes in
      let optagg = identify_arm_aggregate ch instr in
      match optagg with
      | Some agg -> aggregate := Some agg
      | _ -> ()
    done;
    match !aggregate with
    | Some agg ->
       (match agg#kind with
          | ARMJumptable jt -> Ok jt
          | _ -> Error ["other aggregate found"])
    | _ ->
       Error ["no aggregate found:" ^ (string_of_int ch#pos)]
  end


let tb_table_branch () =
  let tests = [
      ("tbb", "0x120f6", "0x12144",
       "022924d8dfe801f00d021800",
       [("0x12102", [1]); ("0x12118", [0]); ("0x1212e", [2])]);
      ("tbb-hiw", "0x4ab74", "0x4acec",
       "052900f2b980dfe801f06f452c231a1100",
       [("0x4aba0", [5]); ("0x4abb2", [4]); ("0x4abc4", [3]);
        ("0x4abd6", [2]); ("0x4ac08", [1]); ("0x4ac5c", [0])]);
      ("tbb-cmpw", "0xc1eda", "0xc1f24",
       "bbf1070f21d8dfe80bf04d194f114b0a070400",
       [("0xc1eec", [7]); ("0xc1ef2", [6]); ("0xc1ef8", [5]);
        ("0xc1f06", [3]); ("0xc1f16", [1]); ("0xc1f7a", [4]);
        ("0xc1f7e", [0]); ("0xc1f82", [2])]);
      ("tbb-ww", "0xc1d78", "0xc1ff2",
       "baf1070f00f23981dfe80af07c7976747270047f00",
       [("0xc1d8c", [6]); ("0xc1e64", [5]); ("0xc1e68", [4]);
        ("0xc1e6c", [3]); ("0xc1e70", [2]); ("0xc1e76", [1]);
        ("0xc1e7c", [0]); ("0xc1e82", [7])]);
      ("tbh", "0x4bec4", "0x4bed6",
       "042906d8dfe811f0f00005000500e40005000000",
       [("0x4bed6", [1; 2; 4]); ("0x4c094", [3]); ("0x4c0ac", [0])]);
      ("tbh-hiw", "0x72080", "0x722b6",
       "082800f21881dfe810f050000900b100090009000900dc000900c6000000",
       [("0x7209c", [1; 3; 4; 5; 7]); ("0x7212a", [0]); ("0x721ec", [2]);
        ("0x72216", [8]); ("0x72242", [6])]);
      ("tbh-ww", "0xc1c88", "0xc1ff8",
       "bbf1070f00f2b481dfe81bf07b018501820180017e017901fc0088010000",
       [("0xc1e8c", [6]); ("0xc1f86", [5]); ("0xc1f8a", [0]);
        ("0xc1f90", [4]); ("0xc1f94", [3]); ("0xc1f98", [2]);
        ("0xc1f9e", [1]); ("0xc1fa4", [7])])
      ] in
  begin
    TS.new_testsuite (testname ^ "_tb_table_branch") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x10000") 0xc0000;
    List.iter (fun (title, hexbase, expecteddefault, bytes, expectedtargets) ->
        let jtresult = jt_setup_thumb hexbase bytes in

        TS.add_simple_test
          ~title:(title ^ "-targets")
          (fun () ->
            match jtresult with
            | Ok jt ->
               ARMA.equal_jumptable_targets
                 ~msg:"" ~expected:expectedtargets ~received:jt ()
            | Error e ->
               A.fail_msg (String.concat "; " e));

        TS.add_simple_test
          ~title:(title ^ "-default")
          (fun () ->
            match jtresult with
            | Ok jt ->
               A.equal_string expecteddefault jt#default_target#to_hex_string
            | Error e ->
               A.fail_msg (String.concat "; " e))
      ) tests;

    TS.launch_tests ()
  end


let ldr_table_branch () =
  let tests = [
      ("ldr", "0x16c922", "0x16c526",
       "032b3ff6ffad01a252f823f000bf43c3160043c3160027c5160027c5160000",
       [("0x16c342", [0; 1]); ("0x16c526", [2; 3])])
    ] in
  begin
    TS.new_testsuite (testname ^ "_ldr_table_branch") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x160000") 0x10000;
    List.iter (fun (title, hexbase, expecteddefault, bytes, expectedtargets) ->
        let jtresult = jt_setup_thumb hexbase bytes in

        TS.add_simple_test
          ~title:(title ^ "-targets")
          (fun () ->
            match jtresult with
            | Ok jt ->
               ARMA.equal_jumptable_targets
                 ~msg:"" ~expected:expectedtargets ~received:jt ()
            | Error e ->
               A.fail_msg (String.concat "; " e));

        TS.add_simple_test
          ~title:(title ^ "-default")
          (fun () ->
            match jtresult with
            | Ok jt ->
               A.equal_string expecteddefault jt#default_target#to_hex_string
            | Error e ->
               A.fail_msg (String.concat "; " e))
      ) tests;

    TS.launch_tests ()
  end


let ldrls_jumptable () =
  let tests = [
      ("ldrls", "0x191ac", "0x190e0",
       "050053e303f19f97c9ffffea1092010008920100e090010000920100f8910100f091010000",
       [("0x190e0", [2]); ("0x191f0", [5]); ("0x191f8", [4]);
        ("0x19200", [3]); ("0x19208", [1]); ("0x19210", [0])])
    ] in
  begin
    TS.new_testsuite (testname ^ "_ldrls_jumptable") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x10000") 0x10000;
    List.iter (fun (title, hexbase, expecteddefault, bytes, expectedtargets) ->
        let jtresult = jt_setup_arm hexbase bytes in

        TS.add_simple_test
          ~title:(title ^ "-targets")
          (fun () ->
            match jtresult with
            | Ok jt ->
               ARMA.equal_jumptable_targets
                 ~msg:"" ~expected:expectedtargets ~received:jt ()
            | Error e ->
               A.fail_msg (String.concat "; " e));

        TS.add_simple_test
          ~title:(title ^ "-default")
          (fun () ->
            match jtresult with
            | Ok jt ->
               A.equal_string expecteddefault jt#default_target#to_hex_string
            | Error e ->
               A.fail_msg (String.concat "; " e))
      ) tests;

    TS.launch_tests ()
  end


let bx_table_branch () =
  let tests = [
      ("bx-w", "0x6c0d0", "0x6c080",
       "062bd5d802a252f823301a44104700bf1d000000"
       ^ "3b01000023010000a1ffffffa1ffffff95ffffff3b0100000000",
       [("0x6c074", [5]); ("0x6c080", [3; 4]); ("0x6c0fc", [0]);
        ("0x6c202", [2]); ("0x6c21a", [1; 6])]);
      ("bx-ww", "0xc22e8", "0xc21d2",
       "062a3ff672af02a151f82220114408471d000000"
       ^ "cbfeffffc5feffff21000000b7feffffb1feffffabfeffff0000",
       [("0xc21a2", [6]); ("0xc21a8", [5]); ("0xc21ae", [4]);
        ("0xc21bc", [2]); ("0xc21c2", [1]); ("0xc2314", [0]);
        ("0xc2318", [3])]);
      ("bx-www", "0xc1e32", "0xc1cdc",
       "baf1070f3ff651af02a252f82a100a44104773010000"
       ^ "8bfeffff6f0100007bfeffff6b0100006dfeffff67feffff61feffff0000",
       [("0xc1ca4", [7]); ("0xc1caa", [6]); ("0xc1cb0", [5]);
        ("0xc1cbe", [3]); ("0xc1cce", [1]); ("0xc1fae", [4]);
        ("0xc1fb2", [2]); ("0xc1fb6", [0])])
    ] in
  begin
    TS.new_testsuite (testname ^ "_bx_table_branch") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x60000") 0xa0000;
    List.iter (fun (title, hexbase, expecteddefault, bytes, expectedtargets) ->
        let jtresult = jt_setup_thumb hexbase bytes in

        TS.add_simple_test
          ~title:(title ^ "-targets")
          (fun () ->
            match jtresult with
            | Ok jt ->
               ARMA.equal_jumptable_targets
                 ~msg:"" ~expected:expectedtargets ~received:jt ()
            | Error e ->
               A.fail_msg (String.concat "; " e));

        TS.add_simple_test
          ~title:(title ^ "-default")
          (fun () ->
            match jtresult with
            | Ok jt ->
               A.equal_string expecteddefault jt#default_target#to_hex_string
            | Error e ->
               A.fail_msg (String.concat "; " e))
      ) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    tb_table_branch ();
    ldr_table_branch ();
    ldrls_jumptable ();
    bx_table_branch ();
    TS.exit_file ()
  end

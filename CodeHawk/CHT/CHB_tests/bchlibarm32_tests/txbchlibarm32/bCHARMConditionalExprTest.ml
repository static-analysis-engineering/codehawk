(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs LLC

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
module BU = TCHBchlibUtils

module ARMA = TCHBchlibarm32Assertion
module ARMU = TCHBchlibarm32Utils

module TR = CHTraceResult


(* bchlib *)
open BCHDoubleword
open BCHFunctionData
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMAssemblyFunctions
open BCHARMTestSupport
open BCHTranslateARMToCHIF


(* bchanalyze *)

open BCHAnalyzeApp


let testname = "bCHARMConditionalExprTest"
let lastupdated = "2024-01-02"


let make_dw (s: string) = TR.tget_ok (string_to_doubleword s)


let codemax = make_dw "0x400000"

(* a: BX LR; ---; a+8: BX LR; --- *)
let bxlr_bxlr = "1eff2fe1000000001eff2fe100000000"


(* Compare subtracts the second argument from the first, updates the condition
   flags according to the result, and discards the result.

   CMP x, y

   (result, carry, overflow) = AddWithCarry(x, NOT(y), "1");
   APSR.N = result<31>
   APSR.Z = IsZeroBit(result)
   APSR.C = carry
   APSR.V = overflow
 *)
let compare_tests () =
  let tests = [
      ("cmp-bcc", "0x10ae0", "0x10ae4", "020051e10100003a", 3, "(R1 < R2)");
      ("cmp-bcs", "0x1d734", "0x1d738", "030052e10100002a", 3, "(R2 >= R3)");
      ("cmp-beq", "0x10184", "0x10188", "000053e30100000a", 3, "(R3 = 0)");
      ("cmp-bge", "0x10418", "0x1041c", "000053e3010000aa", 3, "(R3 >= 0)");
      ("cmp-bgt", "0x10380", "0x10384", "000053e3010000ca", 3, "(R3 > 0)");
      ("cmp-bhi", "0x10cf4", "0x10cf8", "020051e10100008a", 3, "(R1 > R2)");
      ("cmp-ble", "0x100e8", "0x100ec", "000053e3010000da", 3, "(R3 <= 0)");
      ("cmp-bls", "0x195f4", "0x195f8", "2f0054e30100009a", 3, "(R4 <= 47)");
      ("cmp-blt", "0x10c44", "0x10c48", "000053e3010000ba", 3, "(R3 < 0)");
      ("cmp-bne", "0x100b0", "0x100b4", "000053e30100001a", 3, "(R3 != 0)")
    ] in
  begin
    TS.new_testsuite (testname ^ "_compare_tests") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x100b0") 0x10000;
    List.iter (fun (title, cfaddr, ccaddr, bytes, iterations, expectedcond) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let _ = functions_data#reset in
            let _ = arm_assembly_functions#reset in
            let faddr = make_dw cfaddr in
            let bytes = bytes ^ bxlr_bxlr in
            let fn = ARMU.arm_function_setup faddr bytes in
            (* let _ = pr_debug [fn#toPretty; NL] in *)
            let _ =
              for _i = 1 to iterations do
                analyze_arm_function faddr fn 0
              done in
            let _ = testsupport#request_arm_conditional_expr in
            let _ = translate_arm_assembly_function fn in
            let (_, _, optxpr) =
              TR.tget_ok (testsupport#retrieve_arm_conditional_expr ccaddr) in
            ARMA.equal_arm_conditional_expr
              ~expected:expectedcond ~received:optxpr ())
      ) tests;

    TS.launch_tests ()
  end


(* Compare Negative adds the two operands. It updates the condition flags based
   on the result and discards the result.

   CMN x, y

   (result, carry, overflow) = AddWithCarry(x, y, "0");
   APSR.N = result<31>
   APSR.Z = IsZeroBit(result)
   APSR.C = carry
   APSR.V = overflow
 *)
let compare_negative_tests () =
  let tests = [
      ("cmn-bcs", "0x18620", "0x18624", "010572e30100002a", 3, "(R2 >= 4290772992)");
      ("cmn-beq", "0x170d0", "0x170d4", "010073e30100000a", 3, "(R3 = -1)");
      ("cmn-bhi", "0x1f9b0", "0x1f9b4", "1f0270e30100008a", 3, "(R0 > 268435455)");
      ("cmn-bne", "0x10a0c", "0x10a10", "010072e30100001a", 3, "((R2 + 1) != 0)")
    ] in
  begin
    TS.new_testsuite (testname ^ "_compare_negative_tests") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x100b0") 0x10000;
    List.iter (fun (title, cfaddr, ccaddr, bytes, iterations, expectedcond) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let _ = functions_data#reset in
            let _ = arm_assembly_functions#reset in
            let faddr = make_dw cfaddr in
            let bytes = bytes ^ bxlr_bxlr in
            let fn = ARMU.arm_function_setup faddr bytes in
            (* let _ = pr_debug [fn#toPretty; NL] in *)
            let _ =
              for _i = 1 to iterations do
                analyze_arm_function faddr fn 0
              done in
            let _ = testsupport#request_arm_conditional_expr in
            let _ = translate_arm_assembly_function fn in
            let (_, _, optxpr) =
              TR.tget_ok (testsupport#retrieve_arm_conditional_expr ccaddr) in
            ARMA.equal_arm_conditional_expr
              ~expected:expectedcond ~received:optxpr ())
      ) tests;

    TS.launch_tests ()
  end



(** Subtract subtracts the second argument from the first, writes the result to the
    destination and optionally updates the condition flags.

    SUB d, x, y

    (result, carry, overflow) = AddWithCarry(x, NOT(y), "1");
    R[d] = result;
    if setflags then
      APSR.N = result<31>
      APSR.Z = IsZeroBit(result)
      APSR.C = carry
      APSR.V = overflow
 *)
let subtract_tests () =
  let tests = [
      ("sub-bcs", "0x17a30", "0x17a34", "01805ce20100002a", 3, "(R12 >= 1)");
      ("sub-beq", "0x1aae4", "0x1aae8", "008052e20100000a", 3, "(R2 = 0)");
      ("sub-bge", "0x1a8a4", "0x1a8a8", "003050e2010000aa", 3, "(R0 >= 0)");
      ("sub-bgt", "0x1de50", "0x1de54", "001053e2010000ca", 3, "(R3 > 0)");
      ("sub-ble", "0x1ac00", "0x1ac04", "002055e2010000da", 3, "(R5 <= 0)");
      ("sub-blt", "0x11aac", "0x11ab0", "00a050e2010000ba", 3, "(R0 < 0)");
      ("sub-bmi", "0x152b8", "0x152bc", "017058e20100004a", 3, "(R8 < 1)");
      ("sub-bne", "0x18edc", "0x18ee0", "005050e20100001a", 3, "(R0 != 0)")
    ] in
  begin
    TS.new_testsuite (testname ^ "_subtract_tests") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x100b0") 0x10000;
    List.iter (fun (title, cfaddr, ccaddr, bytes, iterations, expectedcond) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let _ = functions_data#reset in
            let _ = arm_assembly_functions#reset in
            let faddr = make_dw cfaddr in
            let bytes = bytes ^ bxlr_bxlr in
            let fn = ARMU.arm_function_setup faddr bytes in
            (* let _ = pr_debug [fn#toPretty; NL] in *)
            let _ =
              for _i = 1 to iterations do
                analyze_arm_function faddr fn 0
              done in
            let _ = testsupport#request_arm_conditional_expr in
            let _ = translate_arm_assembly_function fn in
            let (_, _, optxpr) =
              TR.tget_ok (testsupport#retrieve_arm_conditional_expr ccaddr) in
            ARMA.equal_arm_conditional_expr
              ~expected:expectedcond ~received:optxpr ())
      ) tests;

    TS.launch_tests ()
  end


(* Test performs a bitwise AND operation, updates the condition flags based on
   the result and discards the result.

   TST x, y

   result = x & y;
   APSR.N = result<31>
   APSR.Z = IsZeroBit(result)
   APSR.C = carry
   // APSR.V unchanged
 *)
let test_tests () =
  let tests = [
      ("tst-beq", "0x18890", "0x18894", "010013e30100000a", 3, "((R3 & 1) = 0)");
      ("tst-bne", "0x18730", "0x18734", "020c13e30100001a", 3, "((R3 & 512) != 0)")
    ] in
  begin
    TS.new_testsuite (testname ^ "_test_tests") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x100b0") 0x10000;
    List.iter (fun (title, cfaddr, ccaddr, bytes, iterations, expectedcond) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let _ = functions_data#reset in
            let _ = arm_assembly_functions#reset in
            let faddr = make_dw cfaddr in
            let bytes = bytes ^ bxlr_bxlr in
            let fn = ARMU.arm_function_setup faddr bytes in
            (* let _ = pr_debug [fn#toPretty; NL] in *)
            let _ =
              for _i = 1 to iterations do
                analyze_arm_function faddr fn 0
              done in
            let _ = testsupport#request_arm_conditional_expr in
            let _ = translate_arm_assembly_function fn in
            let (_, _, optxpr) =
              TR.tget_ok (testsupport#retrieve_arm_conditional_expr ccaddr) in
            ARMA.equal_arm_conditional_expr
              ~expected:expectedcond ~received:optxpr ())
      ) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    compare_tests ();
    compare_negative_tests ();
    subtract_tests ();
    test_tests ();
    TS.exit_file()
  end

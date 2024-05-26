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
module BU = TCHBchlibUtils

module ARMA = TCHBchlibarm32Assertion
module ARMU = TCHBchlibarm32Utils

module TR = CHTraceResult


(* bchlib *)
open BCHDoubleword
open BCHFunctionData
open BCHSystemSettings
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMAssemblyFunctions

(* bchanalyze *)
open BCHAnalyzeApp


let testname = "bCHThumbITSequenceTest"
let lastupdated = "2024-05-25"


let make_dw (s: string) = TR.tget_ok (string_to_doubleword s)


let codemax = make_dw "0x400000"


(*
   sub-it-ne:
   0xdd2c  401a    SUBS   R0, R0, R1
   0xdd2e  18bf    IT NE              R0 := (R0_in - R1_in) != 0
   0xdd30  0120    MOVNE  R0, #0x1
   ---------------------------------
 *)
let thumb_it_predicates () =
  let tests = [
      ("sub-it-ne", "0xdd2c", "0xdd2e", "401a18bf0120704700", "(R0_in != R1_in)");
      ("sub-it-ne-2", "0x201be", "0x201c0", "f41a18bf012400", "(R6_in != R3_in)");
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_it_predicates") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0xd000") 0x20000;
    List.iter (fun (title, cfaddr, ccaddr, bytes, expectedcond) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let _ = functions_data#reset in
            let _ = arm_assembly_functions#reset in
            let _ = system_settings#set_thumb in
            let faddr = make_dw cfaddr in
            let _ = system_info#set_arm_thumb_switch faddr "T" in
            let iccaddr = make_dw ccaddr in
            let fn = ARMU.thumb_function_setup faddr bytes in
            let _ =
              for _i = 1 to 4 do
                analyze_arm_function faddr fn 0
              done in
            let xprs = ARMU.get_instrxdata_xprs faddr iccaddr in
            ARMA.equal_instrxdata_conditionxprs
              ~expected:expectedcond
              ~received:xprs
              ~index:1
              ())
      ) tests;

    TS.launch_tests ()
  end


(* ite-cmp-cc-r (C4):
   0x11a82  85 42   CMP     R5, R0
   0x11a84  34 bf   ITE CC            R5 := (R5_in >= R0_in)
   0x11a86  00 25   MOVCC  R5, #0
   0x11a88  01 25   MOVCS  R5, #1
   ---------------------------------

   ite-cmp-ne:
   0xd00  002b      CMP     R3, #0x0
   0xd02  14bf      ITE NE             R3 := (R3_in != 0)
   0xd04  0123      MOVNE   R3, #0x1
   0xd06  0023      MOVEQ   R3  #0x0
   ---------------------------------

   Note on modifications to ite-cmp-cc and ite-cmp-cs:
   In principle these are condition codes typically applied to unsigned
   integers. Occasionally these are found to be applied to signed integers
   to achieve, respectively, the disjunction:
     x >= y or x < 0
   or the conjunction
     x <= y and x >= 0
   Strictly speaking this can only be done if y >= 0, as explained in
   bCHARMConditionalExpr.
   For unsigned integers the additional disjunct or conjunct is vacuous,
   so does not affect the semantics.
 *)
let thumb_ite_predicates () =
  let tests = [
      ("ite-cmp-cc-r",
       "0x11a82", "0x11a84", "854234bf0025012500",
       "((R5_in >= R0_in) or (R5_in < 0))");
      ("ite-cmp-cs-r",
       "0x11aa0", "0x11aa2", "85422cbf0025012500",
       "((R5_in < R0_in) and (R5_in >= 0))");
      ("ite-cmp-ne",
       "0xd00", "0xd02", "002b14bf0123002300", "(R3_in != 0)");
      ("ite-cmp-hi",
       "0x1eb1c", "0x1eb1e", "a3428cbf0120002000", "(R3_in > R4_in)");
      ("ite-cmp-hi-r",
       "0x11abc", "0x11abe", "85428cbf0025012500", "(R5_in <= R0_in)");
      ("ite-cmp-ls",
       "0x21ee0", "0x21ee2", "032b94bf0123002300", "(R3_in <= 3)");
      ("ite-cmp-ls-r",
       "0x11a96", "0x11a98", "854294bf00250125", "(R5_in > R0_in)")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_ite_predicates") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0xd00") 0x30000;
    List.iter (fun (title, cfaddr, ccaddr, bytes, expectedcond) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let _ = functions_data#reset in
            let _ = arm_assembly_functions#reset in
            let _ = system_settings#set_thumb in
            let faddr = make_dw cfaddr in
            let _ = system_info#set_arm_thumb_switch faddr "T" in
            let iccaddr = make_dw ccaddr in
            let fn = ARMU.thumb_function_setup faddr bytes in
            let _ =
              for _i = 1 to 4 do
                analyze_arm_function faddr fn 0
              done in
            let xprs = ARMU.get_instrxdata_xprs faddr iccaddr in
            ARMA.equal_instrxdata_conditionxprs
              ~expected:expectedcond
              ~received:xprs
              ~index:1
              ())
      ) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    thumb_it_predicates ();
    thumb_ite_predicates ();
    TS.exit_file ()
  end

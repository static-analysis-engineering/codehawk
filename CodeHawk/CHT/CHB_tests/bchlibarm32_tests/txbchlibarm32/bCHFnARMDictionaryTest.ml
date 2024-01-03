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
open BCHSystemInfo
open BCHSystemSettings

(* bchlibarm32 *)
open BCHARMAssemblyFunctions

(* bchanalyze *)
open BCHAnalyzeApp


let testname = "bCHFnARMDictionaryTest"
let lastupdated = "2024-01-02"


let make_dw (s: string) = TR.tget_ok (string_to_doubleword s)


let codemax = make_dw "0x400000"


(* ite-ne:
   0xd00  002b      CMP     R3, #0x0
   0xd02  14bf      ITE NE             R3 := (R3_in != 0)
   0xd04  0123      MOVNE   R3, #0x1
   0xd06  0023      MOVEQ   R3  #0x0
   ---------------------------------

   sub-it-ne:
   0xdd26  00f001f8  BL     0xdd2c
   0xdd2a  7047      BX     LR

   0xdd2c  401a      SUBS   R0, R0, R1
   0xdd2e  18bf      IT NE              R0 := (R0_in - R1_in) != 0
   0xdd30  0120      MOVNE  R0, #0x1
   0xdd32  7047      BX     LR
   ---------------------------------
 *)
let inlined_thumb_it_predicates () =
  let tests = [
      ("sub-it-ne-subsumes",
       "0xdd26",
       "0xdd2c",
       "0xdd2e",
       [1; 2; 3],
       "00f001f87047401a18bf0120704700",
       "subsumes,F:0xdd26_0xdd2e,F:0xdd26_0xdd30");
      ("sub-it-ne-subsumed",
       "0xdd26",
       "0xdd2c",
       "0xdd30",
       [2; 3],
       "00f001f87047401a18bf0120704700",
       "subsumed,F:0xdd26_0xdd2e")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_it_predicates") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0xd00") 0x60000;
    List.iter
      (fun (title, cfaddr, inlcfaddr, ccaddr, indices, bytes, expectedcond) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let _ = functions_data#reset in
            let _ = arm_assembly_functions#reset in
            let _ = system_settings#set_thumb in
            let faddr = make_dw cfaddr in
            let _ = system_info#set_arm_thumb_switch faddr "T" in
            let inlfaddr = make_dw inlcfaddr in
            let _ = system_info#add_inlined_function inlfaddr in
            let iccaddr = make_dw ccaddr in
            let fn = ARMU.thumb_function_setup faddr bytes in
            let _ = for _i = 1 to 4 do analyze_arm_function faddr fn 0 done in
            let tags = ARMU.get_instrxdata_tags faddr iccaddr in
            ARMA.equal_instrxdata_tags
              ~expected:expectedcond
              ~received:tags
              ~indices:indices
              ())
      ) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    inlined_thumb_it_predicates ();
    TS.exit_file ()
  end

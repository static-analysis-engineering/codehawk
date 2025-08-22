(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2025 Aarno Labs LLC

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
open BCHFunctionInfo
open BCHSystemInfo
open BCHSystemSettings

(* bchlibarm32 *)
open BCHARMAssemblyFunctions
open BCHARMCHIFSystem
open BCHARMTestSupport
open BCHTranslateARMToCHIF

(* bchanalyze *)
open BCHAnalyzeApp


let testname = "bCHTranslateARMToCHIFTest"
let lastupdated = "2025-08-20"

let make_dw (s: string) = TR.tget_ok (string_to_doubleword s)


let codemax = make_dw "0x400000"


let translate_store () =
  let tests = [
      ("PUSHLR", "0x1b960", "04e02de500",
       [("var_0004", "LR_in"); ("SP", "sv__3__sv")]);
      ("PUSHR0_3", "0x19470", "0f002de900",
       [("var_0016", "R0_in");
        ("var_0012", "R1_in");
        ("var_0008", "R2_in");
        ("var_0004", "R3_in");
        ("SP", "sv__3__sv")]);
      ("STM", "0x3f7b8", "10128de800",
       [("var_0000", "R4_in"); ("arg_0004", "R9_in"); ("arg_0008", "R12_in")]);
      ("STMIB", "0x3ba4c", "10408de900",
       [("arg_0004", "R4_in"); ("arg_0008", "LR_in")]);
      ("STR", "0x1b4bc", "08608de500", [("arg_0008", "R6_in")]);
      ("STRBwb", "0x10208", "015062e500", [("R2", "sv__3__sv")]);
      ("STRwb", "0x10568", "08402de500",
       [("var_0008", "R4_in"); ("SP", "sv__3__sv")]);
      ("STRDwb1", "0x1b4bc", "f0416de100",
       [("var_0016", "R4_in");
        ("var_0012", "R5_in");
        ("SP", "sv__23__sv")]);
      ("STRDwb2", "0x10ab8", "fc406de100",
       [("var_0012", "R4_in");
        ("var_0008", "R5_in");
        ("SP", "sv__3__sv")]);
      ("STRH", "0x1b4bc", "b031cde100", [("arg_0016", "R3_in")])
    ] in
  begin
    TS.new_testsuite (testname ^ "_translate_store") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x10000") 0x30000;
    List.iter (fun (title, sfaddr, bytes, expectedcmds) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let faddr = make_dw sfaddr in
            let fn = ARMU.arm_function_setup faddr bytes in
            let _ = analyze_arm_function faddr fn 0 in
            let _ = translate_arm_assembly_function fn in
            let proc = arm_chif_system#get_arm_procedure faddr in
            (* remove the PC assignment at the end of the transaction *)
            let assigns = BU.extract_chif_cfg_assignments ~len:(-1) proc in
            let finfo = get_function_info faddr in
            BA.equal_assignments finfo ~expected:expectedcmds ~received:assigns)
      ) tests;

    TS.launch_tests ()
  end


(*
  reg-overwritten:
     0x4f04  MOVW         R3, #0x4925
     0x4f08  LDRB.W       R9, [R3, #1136]
     0x4f0c  CMP.W        R9, #0x91
     0x4f10  MOV          R9, PC
     0x4f12  BHI          0x4f1a
         -> 0x4f14, 0x4f1a

     0x4f14  SUBW         R9, R9, #0xde1
     0x4f18  BX           R9

     0x4f1a  SUBW         R9, R9, #0xee7
     0x4f1e  BX           R9

     Note: BHI produces a conjunction of expressions, but the retrieval
     mechanism currently retrieves the expressions after they have been
     broken up, and so only the last one survives. The correct expected
     value for this test is:
     ((gv_0x4d95_in <= 145) and (gv_0x4d95_in >= 0))
     but we only see the last one being reported.

     At some point this should be fixed.
 *)
let thumb_chif_conditionxprs () =
  let tests = [
      ("reg-overwritten",
       "0x4f04",
       "0x4f12",
       "44f6251393f87094b9f1910ff94602d8a9f6e1594847a9f6e769484700",
       3,
       "(gvb_0x4d95_in >= 0)")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_chif_conditionxprs") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x4000") 0x10000;
    List.iter (fun (title, cfaddr, ccaddr, bytes, iterations, expectedcond) ->

        TS.add_simple_test
          ~title
          (fun () ->
            let _ = functions_data#reset in
            let _ = arm_assembly_functions#reset in
            let _ = system_settings#set_thumb in
            let faddr = make_dw cfaddr in
            let _ = system_info#set_arm_thumb_switch faddr "T" in
            let fn = ARMU.thumb_function_setup faddr bytes in
            let _ =
              for _i = 1 to iterations do
                analyze_arm_function faddr fn 0
              done in
            let _ = testsupport#request_chif_conditionxprs in
            let _ = translate_arm_assembly_function fn in
            let (_, _, txprs) =
              TR.tget_ok (testsupport#retrieve_chif_conditionxprs ccaddr) in
            ARMA.equal_chif_conditionxprs ~expected:expectedcond ~received:txprs ())
      ) tests;

    TS.launch_tests ()
  end

(*
  reg-overwritten:
     0x4f04  MOVW         R3, #0x4925
     0x4f08  LDRB.W       R9, [R3, #1136]
     0x4f0c  CMP.W        R9, #0x91
     0x4f10  MOV          R9, PC
     0x4f12  BHI          0x4f1a
         -> 0x4f14, 0x4f1a

     0x4f14  SUBW         R9, R9, #0xde1
     0x4f18  BX           R9

     0x4f1a  SUBW         R9, R9, #0xee7
     0x4f1e  BX           R9
 *)
let thumb_instrxdata_conditionxprs () =
  let tests = [
      ("reg-overwritten",
       "0x4f04",
       "0x4f12",
       "44f6251393f87094b9f1910ff94602d8a9f6e1594847a9f6e769484700",
       3,
       "((gvb_0x4d95_in <= 145) and (gvb_0x4d95_in >= 0))")
    ] in
  begin
    TS.new_testsuite (testname ^ "_thumb_instrxdata_conditionxprs") lastupdated;

    system_info#set_elf_is_code_address wordzero codemax;
    ARMU.arm_instructions_setup (make_dw "0x4000") 0x10000;

    List.iter (fun (title, cfaddr, ccaddr, bytes, iterations, expectedcond) ->

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
              for _i = 1 to iterations do
                analyze_arm_function faddr fn 0
              done in
            let xprs = ARMU.get_instrxdata_xprs faddr iccaddr in
            ARMA.equal_instrxdata_conditionxprs
              ~expected:expectedcond ~received:xprs ~index:3 ())
      ) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    translate_store ();
    thumb_chif_conditionxprs ();
    thumb_instrxdata_conditionxprs ();
    TS.exit_file ()
  end

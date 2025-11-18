(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2025  Aarno Labs LLC

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

open CCHPreTypes
open CCHProofScaffolding

module A = TCHAssertion
module TS = TCHTestSuite
module CA = TCHCchanalyzeAssertion
module CU = TCHCchanalyzeUtils


let testname = "cCHPOCheckLocallyInitializedTest"
let lastupdated = "2025-11-12"


let po_filter (po: proof_obligation_int): proof_obligation_int option =
  match po#get_predicate with
  | PLocallyInitialized _ -> Some po
  | _ -> None


(* See CHT/CHC_tests/cchanalyze_tests/tcchanalyze/tCHCchanalyzeUtils.mli
   for a description and example of how to specify the tests.
 *)
let check_safe () =
  let tests = [
      ("gl-inv-001",
       "locally_initialized_gl_inv_001", "gl_inv_001",
       [], -1, -1,
       "inv_implies_safe", "local assignment(s): assignedAt#4");
      ("gl-memlval-memref-001",
       "locally_initialized_gl_memlval_memref_001", "gl_memlval_memref_001",
       [], -1, -1,
       "memlval_memref_implies_safe", "")
    ] in
  begin
    TS.new_testsuite (testname ^ "_check_safe") lastupdated;
    CHTiming.disable_timing ();

    List.iter
      (fun (title, filename, funname, reqargs, line, byte, xdetail, expl) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let _ = CCHSettings.system_settings#set_output_parameter_analysis in
            let _ = CU.analysis_setup "PLocallyInitialized" filename in
            let po_s = proof_scaffolding#get_proof_obligations funname in
            let po_s = List.filter_map po_filter po_s in
            let tgtpo_o = CU.select_target_po ~reqargs ~line ~byte po_s in
            begin
              CU.analysis_take_down filename;
              match tgtpo_o with
              | Some po -> CA.expect_safe_detail ~po ~xdetail ~expl ()
              | _ ->
                 let s_po_s = List.map CU.located_po_to_string po_s in
                 A.fail_msg
                   ("Unable to uniquely select target proof obligation: "
                    ^ "["
                    ^ (String.concat "; " s_po_s)
                    ^ "]")
            end
          )
      ) tests;

    TS.launch_tests()
  end


(* See CHT/CHC_tests/cchanalyze_tests/tcchanalyze/tCHCchanalyzeUtils.mli
   for a description and example of how to specify the tests.
 *)
let check_violation () =
  let tests = [
      ("rl-xpr-001",
       "locally_initialized_rl_xpr_001", "rl_xpr_001",
       [], -1, -1,
       "xpr_implies_violation",
       "value of (*p) is obtained from dereferencing parameter p");
      ("rl-xpr-002",
       "locally_initialized_rl_xpr_002", "rl_xpr_002",
       [], -1, -1,
       "xpr_implies_violation",
       "value of (*p) is obtained from dereferencing parameter p");
      ("rl-memlval-001",
       "locally_initialized_rl_memlval_001", "rl_memlval_001",
       [], -1, -1,
       "memlval_vinv_implies_violation",
       "initialized from parameter p->fld1 with offset .fld1");
      ("rl-memlval-002",
       "locally_initialized_rl_memlval_002", "rl_memlval_002",
       [], -1, -1,
       "memlval_vinv_implies_violation",
       "initialized from parameter p->fld1 with offset .fld1")
    ] in
  begin
    TS.new_testsuite (testname ^ "_check_violation") lastupdated;
    CHTiming.disable_timing ();

    List.iter
      (fun (title, filename, funname, reqargs, line, byte, xdetail, expl) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let _ = CCHSettings.system_settings#set_output_parameter_analysis in
            let _ = CU.analysis_setup "PLocallyInitialized" filename in
            let po_s = proof_scaffolding#get_proof_obligations funname in
            let po_s = List.filter_map po_filter po_s in
            let tgtpo_o = CU.select_target_po ~reqargs ~line ~byte po_s in
            begin
              CU.analysis_take_down filename;
              match tgtpo_o with
              | Some po -> CA.expect_violation_detail ~po ~xdetail ~expl ()
              | _ ->
                 let s_po_s = List.map CU.located_po_to_string po_s in
                 A.fail_msg
                   ("Unable to uniquely select target proof obligation: "
                    ^ "["
                    ^ (String.concat "; " s_po_s)
                    ^ "]")
            end
          )
      ) tests;

    TS.launch_tests()
  end

let () =
  begin
    TS.new_testfile testname lastupdated;
    check_safe ();
    check_violation ();
    TS.exit_file ()
  end

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


let testname = "cCHPOCheckInitializedTest"
let lastupdated = "2025-11-10"


let po_filter (po: proof_obligation_int): proof_obligation_int option =
  match po#get_predicate with
  | PInitialized _ -> Some po
  | _ -> None


(* See CHT/CHC_tests/cchanalyze_tests/tcchanalyze/tCHCchanalyzeUtils.mli
   for a description and example of how to specify the tests.

   Tests:

   Test: gl-inv-001:
   =================
   int gl_inv_001(void) {

     int i = 5;

     return i;
   }

   Test: gl-inv-002:
   =================
   typedef struct mystruct_s {
     int fld1;
     int fld2;
   } mystruct;


   int gl_inv_002(void) {

     mystruct s = {.fld1 = 5, .fld2 = 3 };

     return s.fld1;
   }

   Test: gl-inv-003:
   =================
   int gl_inv_003(int k) {

     int i;

     if (k > 0) {
       i = 5;
     } else {
       i = 3;
     }

     return i;
   }

   Test gl-inv-xpr-001:
   ====================
   int gl_inv_xpr_001(void) {

     int i = 5;

     int *p = &i;

     return *p;
   }


 *)
let check_safe () =
  let tests = [
      ("gl-inv-001",
       "gl_inv_001", "gl_inv_001",
       [], -1, -1,
       "inv_implies_safe", "assignedAt#5");
      ("gl-inv-002",
       "gl_inv_002", "gl_inv_002",
       [], -1, -1,
       "inv_implies_safe", "assignedAt#11");
      ("gl-inv-003",
       "gl_inv_003", "gl_inv_003",
       [], 14, -1,
       "inv_implies_safe", "");
      ("gl-inv-xpr-001",
       "gl_inv_xpr_001", "gl_inv_xpr_001",
       ["(*p)"], -1, -1,
       "inv_xpr_implies_safe", "variable (*p) has the value 5");
      ("gl-inv-xpr-002",
       "gl_inv_xpr_002", "gl_inv_xpr_002",
       ["(*p)"], -1, -1,
       "inv_xpr_implies_safe", "variable (*p) has the value 8");
      ("gl-inv-xpr-003",
       "gl_inv_xpr_003", "gl_inv_xpr_003",
       [], 11, -1,
       "inv_xpr_implies_safe", "variable i has the value 8");
      ("gl-inv-bounded-xpr-001",
       "gl_inv_bounded_xpr_001", "gl_inv_bounded_xpr_001",
       ["(*p)"], 14, -1,
       "inv_bounded_xpr_implies_safe", "variable (*p) is bounded by LB: 3 and UB: 5");
      ("gl-stackvar-001",
       "gl_stackvar_001", "gl_stackvar_001",
       ["(*p)"], 14, -1,
       "memlval_vinv_memref_stackvar_implies_safe",
       "assignment(s) to i: assignedAt#11_xx_assignedAt#9")
    ] in
  begin
    TS.new_testsuite (testname ^ "_check_safe") lastupdated;
    CHTiming.disable_timing ();

    List.iter
      (fun (title, filename, funname, reqargs, line, byte, xdetail, expl) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let _ = CCHSettings.system_settings#set_undefined_behavior_analysis in
            let _ = CU.analysis_setup "PInitialized" filename in
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


let () =
  begin
    TS.new_testfile testname lastupdated;
    check_safe ();
    TS.exit_file ()
  end

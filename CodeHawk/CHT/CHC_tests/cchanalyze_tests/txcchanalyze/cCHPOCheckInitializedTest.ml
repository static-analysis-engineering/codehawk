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


let testname = "bCHPOCheckInitializedTest"
let lastupdated = "2025-11-10"


let po_filter (po: proof_obligation_int): proof_obligation_int option =
  match po#get_predicate with
  | PInitialized _ -> Some po
  | _ -> None


(* Test specifications contain the following information:
   title: name of the test

   - file/function identification
   ------------------------------
   filename: name of the c-file to be loaded
   funname: name of the function to be checked

   - selection of proof obligation to check
   ----------------------------------------
   reqargs: list of strings that represent the arguments to the
     proof obligation predicate; this may be an empty list or a list
     that has the right length, but individual arguments may be omitted
     by specifying the empty string ("")
   line: the line number to which the proof obligation applies (can be
     left unspecified by giving -1)
   byte: the byte number at which the proof obligation is located (can
     be left unspecified by giving -1)

   - check that proof obligation is discharged as expected
   -------------------------------------------------------
   xdetail: identification of the discharge method in the checker
   expl: explanation given for the discharge (can be left unspecified
      by giving the empty string)

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
       "inv_implies_safe", "")
    ] in
  begin
    TS.new_testsuite (testname ^ "_check_safe") lastupdated;
    CHTiming.disable_timing ();

    List.iter
      (fun (title, filename, funname, reqargs, line, byte, xdetail, expl) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let _ = CU.analysis_setup filename in
            let po_s = proof_scaffolding#get_proof_obligations funname in
            let po_s = List.filter_map po_filter po_s in
            let (tgtpo_o, other_po_s) =
              CU.select_target_po ~reqargs ~line ~byte po_s in
           match tgtpo_o with
            | Some po -> CA.expect_safe_detail ~po ~xdetail ~expl ()
            | _ ->
               A.fail_msg
                 ("Unable to uniquely select target proof obligation: "
                  ^ "["
                  ^ (String.concat "; " other_po_s)
                  ^ "]")
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

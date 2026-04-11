(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Alexander Bakst
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026  Aarno Labs LLC

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


let testname = "cCHPOCheckErrnoWrittenTest"
let lastupdated = "2026-04-06"


let po_filter (po: proof_obligation_int): proof_obligation_int option =
  match po#get_predicate with
  | PErrnoWritten -> Some po
  | _ -> None

let summaries_jar = Some "testinputs/PErrnoWritten/cchsummaries.jar"

(* See CHT/CHC_tests/cchanalyze_tests/tcchanalyze/tCHCchanalyzeUtils.mli
   for a description and example of how to specify the tests.
 *)
let check_safe () =
  let tests = [
      ("strtoul_errno",
       "errno_written_strtoul", "main_strtoul",
       [], -1, -1,
       None, "");

      ("fopen_errno",
       "errno_written_fopen", "main_fopen",
       [], -1, -1,
       None, "");

      ("fclose_errno",
       "errno_written_fclose", "main_fclose",
       [], -1, -1,
       None, "");

      ("fseek_errno",
       "errno_written_fseek", "main_fseek",
       [], -1, -1,
       None, "");
    ] in
  begin
    TS.new_testsuite (testname ^ "_check_safe") lastupdated;
    CHTiming.disable_timing ();
    CHLogger.activate_diagnostics();

    List.iter
      (fun (title, filename, funname, reqargs, line, byte, xdetail, expl) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let _ = CCHSettings.system_settings#set_errno_written_analysis in
            let _ = CU.analysis_setup ~summaries_jar "PErrnoWritten" filename in
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


let check_not_safe () =
  let tests = [
      ("not_proveable",
       "errno_written_unsafe", "main_unsafe",
       [], -1, -1)
    ] in
  begin
    TS.new_testsuite (testname ^ "_check_open") lastupdated;
    CHTiming.disable_timing ();

    List.iter
      (fun (title, filename, funname, reqargs, line, byte) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let _ = CCHSettings.system_settings#set_errno_written_analysis in
            let _ = CU.analysis_setup ~summaries_jar "PErrnoWritten" filename in
            let po_s = proof_scaffolding#get_proof_obligations funname in
            let po_s = List.filter_map po_filter po_s in
            let tgtpo_o = CU.select_target_po ~reqargs ~line ~byte po_s in
            begin
              CU.analysis_take_down filename;
              match tgtpo_o with
              | Some po when po#get_status <> Green -> ()
              | Some po -> 
                A.fail_msg ("Expected proof obligation should not valid, but got "
                         ^ (CCHPreSumTypeSerializer.po_status_mfts#ts po#get_status))
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
    CHLogger.activate_diagnostics();
    TS.new_testfile (testname ^ "0") lastupdated;
    check_safe ();
    check_not_safe ();
    TS.exit_file ();
    ()
    (* check_open (); *)
  end

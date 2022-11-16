(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
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
open CHCommon
open CHPretty

(* chutil *)
open CHFileIO
open CHPrettyUtil
open CHXmlDocument

(* tchlib *)
open TCHTestApi


module H = Hashtbl


let print_exception e =
  match e with
  | CHFailure p -> p
  | _ -> STR (Printexc.to_string e)


let print_result (len:int) (index:int) (name:string) (result:testresult_t) =
  match result with
  | Passed t ->
     pr_debug [
         fixed_length_pretty ~alignment:StrRight (INT index) 3;
         STR "  ";
         fixed_length_pretty (STR name) len;
         STR " [ ... passed (";
         STR (Printf.sprintf "%f" t);
         STR " secs) ]";
         NL]
  | Failed { expected_value; actual_value; fmessage } ->
     if expected_value != actual_value then
       pr_debug [
           fixed_length_pretty ~alignment:StrRight (INT index) 3;
           STR "  ";
           fixed_length_pretty (STR name) len;
           STR " [ ... failed ";
           STR fmessage;
           NL;
           STR "     expected ";
           STR expected_value;
           STR " but received ";
           STR actual_value;
           STR " ]";
           NL]
     else
       pr_debug [
           STR name;
           STR " ... failed ";
           STR fmessage;
           NL;
           STR "     expected anything excluding ";
           STR expected_value;
           STR " but received ";
           STR actual_value;
           NL]
  | Uncaught (e, bt) ->
     pr_debug [
         fixed_length_pretty ~alignment:StrRight (INT index) 3;
         STR "  ";
         fixed_length_pretty (STR name) len;
         STR " [ ... raised an exception";
         NL;
         STR "     ";
         print_exception e;
         NL;
         STR bt;
         STR "]";
         NL]
  | Report (valid, total, uncaught, counterexamples, categories, timeused) ->
     pr_debug [
         fixed_length_pretty ~alignment:StrRight (INT index) 3;
         STR "  ";
         fixed_length_pretty (STR name) len;
         STR " [ ... passed ";
         INT valid;
         STR "/";
         INT total;
         STR " (";
         STR (Printf.sprintf "%f" timeused);
         STR " secs) ]";
         NL;
         (match counterexamples with
          | [] -> STR ""
          | l ->
             LBLOCK [
                 STR "    counterexamples: ";
                 pretty_print_list counterexamples (fun s -> STR s) "" ", " "";
                 NL]);
         (match categories with
          | [] -> STR ""
          | [("", _)] -> STR ""
          | _ ->
             LBLOCK [
                 STR "    categories: ";
                 pretty_print_list
                   categories
                   (fun (s, i) -> LBLOCK [STR s; STR ": "; INT i])
                   "" "; " "";
                 NL])]
  | Exit_code _ -> ()


let print_totals
      (name: string) (passed: int) (failed: int) (uncaught: int) (total: int) =
  pr_debug [
      STR (string_repeat "-" 80);
      NL;
      STR "Summary for ";
      STR name;
      STR ":";
      NL;
      STR "Passed   : ";
      INT passed;
      STR "/";
      INT total;
      NL;
      STR "Failed   : ";
      INT failed; STR "/";
      INT total;
      NL;
      STR "Uncaught : ";
      INT uncaught;
      STR "/";
      INT total;
      NL;
      STR (string_repeat "=" 80);
      NL]


let default_classifier _ = ""


let default_reducer _ = []


let default_smaller _ _ = true


let tests = H.create 3
let counter = ref 0
let testcounter = ref 0
let testsuitename = ref "testsuite"
let testsuitedate = ref "2022-11-13"


let get_title () =
  begin
    testcounter := !testcounter + 1;
    "test-" ^ (string_of_int !testcounter)
  end


let get_seqnumber () =
  begin counter := !counter + 1; !counter end


let add_simple_test ?(title=get_title ()) (f: unit -> unit) =
  let (name, test) = TCHTest.make_simple_test ~title f in
  H.add tests name (get_seqnumber (), test)


let add_random_test
      ?(title=get_title ())
      ?(nb_runs=100)
      ?(nb_tries=10*nb_runs)
      ?(classifier=default_classifier)
      ?(reducer=default_reducer)
      ?(reduce_depth=4)
      ?(reduce_smaller=default_smaller)
      ?(random_src=TCHGenerator.make_random ())
      ((gen, prn): 'a generator_t)
      (f:'a -> 'b)
      (spec:(('a, 'b) specification_t) list) =
  let (name, test) =
    TCHTest.make_random_test
      ~title
      ~nb_runs
      ~nb_tries
      ~classifier
      ~reducer
      ~reduce_depth
      ~reduce_smaller
      ~random_src
      (gen, prn)
      f
      spec in
  H.add tests name (get_seqnumber (), test)


let new_testsuite (name: string) (date: string) =
  begin
    testsuitename := name;
    testsuitedate := date;
    H.clear tests
  end


let run_tests (names: string list) =
  let passed = ref 0 in
  let failed = ref 0 in
  let uncaught = ref 0 in
  let total = ref 0 in
  let lst = ref [] in
  let namelen =
    List.fold_left (fun m name ->
        let len = String.length name in
        if len > m then len else m) 0 names in
  let _ =
    List.iter (fun name ->
        if H.mem tests name then
          lst := (H.find tests name) :: !lst) (List.rev names) in
  begin
    pr_debug [
        STR "Test suite ";
        STR !testsuitename;
        STR " (last updated: ";
        STR !testsuitedate;
        STR ")";
        NL;
        STR (string_repeat "=" 80);
        NL];
    List.iter (fun name ->
        let (index, testf) = H.find tests name in
        let result = testf () in
        begin
          (match result with
           | Passed _ -> begin incr passed; incr total end
           | Failed _ -> begin incr failed; incr total end
           | Uncaught _ -> begin incr uncaught; incr total end
           | Report (pass, tot, unc, _, _, _) ->
              begin
                passed := !passed + pass;
                failed := !failed + ((tot - pass) - unc);
                uncaught := !uncaught + unc;
                total := !total + tot
              end
           | Exit_code c ->
              begin
                incr (if c = 0 then passed else failed);
                incr total
              end);
          print_result namelen index name result
        end) names;
    print_totals !testsuitename !passed !failed !uncaught !total
  end


let launch_tests () =
  let lst = ref [] in
  let _ = H.iter (fun name (index, _) -> lst := (index, name) :: !lst) tests in
  let lst = List.map snd (List.sort (fun (i1, _) (i2, _) -> Stdlib.compare i1 i2) !lst) in
  begin
    run_tests lst
  end
                          

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

(* cchlib *)
open CCHBasicTypes
open CCHSettings
open CCHTypesToPretty

(* cchpre *)
open CCHPreTypes


let p2s = CHPrettyUtil.pretty_to_string


let default_domains = [
    CCHInvariantFact.linear_equalities_domain;
    CCHInvariantFact.pepr_domain;
    CCHInvariantFact.valueset_domain;
    CCHInvariantFact.intervals_domain;
    CCHInvariantFact.symbolic_sets_domain;
    CCHInvariantFact.sym_pointersets_domain
  ]


let unpack_tar_gz (predicate: string) (filename: string) =
  let subdir = Filename.concat "testinputs" predicate in
  let targzname = Filename.concat subdir (filename ^ ".cch.tar.gz") in
  let cchdirname = filename ^ ".cch" in
  let rmcmd = Filename.quote_command "rm" ["-rf"; cchdirname] in
  let xtarcmd = Filename.quote_command "tar" ["xfz"; targzname] in
  let _ = Sys.command rmcmd in
  let _ = Sys.command xtarcmd in
  ()


let analysis_setup ?(domains=default_domains) (predicate: string) (filename: string) =
  begin
    unpack_tar_gz predicate filename;
    system_settings#set_projectname filename;
    system_settings#set_cfilename filename;
    (if system_settings#is_output_parameter_analysis then
       CCHCreateOutputParameterPOs.output_parameter_po_process_file ()
     else
       CCHCreatePrimaryProofObligations.primary_process_file ());
    CCHProofScaffolding.proof_scaffolding#reset;
    CCHGenerateAndCheck.generate_and_check_process_file domains
  end


let analysis_take_down (filename: string) =
  let cchdirname = filename ^ ".cch" in
  let rmcmd = Filename.quote_command "rm" ["-rf"; cchdirname] in
  let _ = Sys.command rmcmd in
  ()


let exp_to_string (exp: exp) = p2s (exp_to_pretty exp)


let located_po_to_string (po: proof_obligation_int) =
  let loc = po#get_location in
  "("
  ^ (string_of_int loc.line)
  ^ ", "
  ^ (string_of_int loc.byte)
  ^ ") "
  ^ (p2s (CCHPOPredicate.po_predicate_to_pretty po#get_predicate))
  ^ ": "
  ^ (match po#get_explanation with
     | Some smsg -> smsg.smsg_msg | _ -> "no explanation")


let select_target_po
      ?(reqargs:string list = [])
      ?(line:int = -1)
      ?(byte:int = -1)
      (po_s: proof_obligation_int list):
      proof_obligation_int option =
  let po_match =
    List.fold_left (fun po_match po ->
        let p = po#get_predicate in
        let p_args = CCHPOPredicate.collect_indexed_predicate_expressions p in
        let p_args = List.map snd p_args in
        let p_args = List.map exp_to_string p_args in
        let reqargs =
          match reqargs with
          | [] -> List.init (List.length p_args) (fun _ -> "")
          | _ -> reqargs in
        let pomatch =
          List.fold_left2
            (fun acc actual req -> acc && (req = "" || actual = req))
            true p_args reqargs in
        let pomatch = pomatch && (line = (-1) || line = po#get_location.line) in
        let pomatch = pomatch && (byte = (-1) || byte = po#get_location.byte) in
        if pomatch then
          po :: po_match
        else
          po_match) [] po_s in
  match po_match with
  | [po] -> Some po
  | _ -> None

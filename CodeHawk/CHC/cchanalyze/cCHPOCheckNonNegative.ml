(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify

(* cchlib *)
open CCHBasicTypes
open CCHTypesToPretty

(* cchpre *)
open CCHPOPredicate
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes


let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class non_negative_checker_t
        (poq: po_query_int)
        (e: exp)
        (invs: invariant_int list) =
object (self)

  method  private mk_predicate (a: exp): po_predicate_t =
    PNonNegative a

  (* ----------------------------- safe ------------------------------------- *)

  method private xpr_implies_safe (invindex: int) (x: xpr_t) =
    let xconstraint = XOp (XGe, [x; zero_constant_expr ]) in
    let sconstraint = simplify_xpr xconstraint in
    if is_true sconstraint then
      let deps = DLocal [invindex] in
      let msg =
        Printf.sprintf
          "value: %s satisfies constraint %s" (x2s x) (x2s xconstraint) in
      Some (deps, msg)
    else
      None

  method private inv_implies_safe (inv: invariant_int) =
    match inv#lower_bound_xpr with
    | Some x -> self#xpr_implies_safe inv#index x
    | _ -> None

  method check_safe =
    match invs with
    | [] ->
       begin
         poq#set_diagnostic ("no invariants found for " ^ (e2s e));
         false
       end
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_safe inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)

  method private xpr_implies_delegation (invindex: int) (x: xpr_t) =
    if poq#is_api_expression x then
      let pred = self#mk_predicate (poq#get_api_expression x) in
      let deps = DEnvC ([invindex], [ApiAssumption pred]) in
      let msg =
        Printf.sprintf
          "condition %s delegated to the api"
          (p2s (po_predicate_to_pretty pred)) in
      Some (deps, msg)
    else
      None

  method private inv_implies_delegation (inv: invariant_int) =
    match inv#lower_bound_xpr with
    | Some x -> self#xpr_implies_delegation inv#index x
    | _ -> None

  method check_delegation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_delegation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs
end


let check_non_negative (poq: po_query_int) (e: exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new non_negative_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

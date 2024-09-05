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


class index_upper_bound_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list) =
object (self)

  method private mk_predicate a1 a2 = PIndexUpperBound (a1,a2)

  method private mk_safe_constraint x1 x2 = XOp (XLt, [x1; x2])

  method private mk_violation_constraint x1 x2 = XOp (XGe, [x1; x2])

  (* ----------------------------- safe ------------------------------------- *)

  method private global_implies_safe inv1index inv2index g1 g2 =
    let pred = self#mk_predicate g1 g2 in
    match poq#check_implied_by_assumptions  pred with
    | Some pred ->
       let deps = DEnvC ([inv1index; inv2index],[GlobalApiAssumption pred]) in
       let msg = "index upper bound implied by global assumption: "
                   ^ (p2s (po_predicate_to_pretty pred)) in
       Some (deps,msg)
    | _ ->
       let xpred = po_predicate_to_xpredicate poq#fenv pred in
       begin
         poq#mk_global_request xpred;
         None
       end

  method private xpr_implies_safe inv1index inv2index x1 x2 =
    let xconstraint = XOp (XLt, [x1; x2]) in
    let sconstraint = simplify_xpr xconstraint in
    if is_true sconstraint then
      let deps = DLocal [inv1index; inv2index] in
      let msg = "index: " ^  (x2s x1) ^ " and bound: "  ^ (x2s x2)
                ^ " satisfy constraint: " ^  (x2s xconstraint) in
      Some (deps,msg)
    else
      match (poq#x2global x1, poq#x2global x2) with
      | (Some g1,Some g2)
           when poq#is_global_expression x1 || poq#is_global_expression x2 ->
         begin
           match self#global_implies_safe inv1index inv2index g1 g2 with
           | Some r -> Some r
           | _ ->
              begin
                poq#set_diagnostic ("remaining constraint: " ^ (x2s sconstraint));
                None
              end
         end
      | _ ->
         begin
           poq#set_diagnostic ("remaining constraint: " ^ (x2s sconstraint));
           None
         end

  method private inv_implies_safe inv1 inv2 =
    match (inv1#upper_bound_xpr, inv2#lower_bound_xpr) with
    | (Some x1, Some x2) -> self#xpr_implies_safe inv1#index inv2#index x1 x2
    | _ -> None

  method check_safe =
    match (invs1, invs2) with
    | ([], []) ->
       begin
         poq#set_diagnostic
           ("no invariants for " ^ (e2s e1) ^ " and " ^ (e2s e2));
         false
       end
    | ([], _) ->
       begin
         poq#set_diagnostic ("no invariants for expression " ^ (e2s e1));
         false
       end
    | (_, []) ->
       begin
         poq#set_diagnostic ("no invariants for bound " ^ (e2s e2));
         false
       end
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_safe inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1

  (* ----------------------- violation -------------------------------------- *)

  method private xpr_implies_universal_violation invindices x1 x2 =
    let xconstraint = XOp (XGe, [x1; x2]) in
    let sconstraint = simplify_xpr xconstraint in
    if is_true sconstraint then
      let safeconstraint = XOp (XLt, [x1; x2]) in
      let deps = DLocal invindices in
      let msg =
        "index: " ^ (x2s x1)  ^ " and bound: " ^ (x2s x2)
        ^ " violate safety constraint: " ^ (x2s safeconstraint) in
      Some (deps, msg)
    else
      None

  method private var1_implies_existential_violation invindices v1 x2 =
    if poq#env#is_tainted_value v1 then
      let safeconstraint = self#mk_safe_constraint (XVar v1) x2 in
      let vconstraint = self#mk_violation_constraint (XVar v1) x2 in
      match poq#get_witness vconstraint v1 with
      | Some violationvalue ->
         let (s, callee, pc) = poq#get_tainted_value_origin v1 in
         let deps = DEnvC ( invindices, [PostAssumption (callee.vid,pc)]) in
         let msg =
           s ^ " choose value: " ^ (x2s violationvalue)
           ^ " to violate safety constraint: " ^ (x2s safeconstraint) in
         Some (deps, msg)
      | _ -> None
    else
      None

  method private xpr1_implies_existential_violation invindices x1 x2 =
    match x1 with
    | XVar v -> self#var1_implies_existential_violation invindices v x2
    | _ -> None

  method private xprlist_implies_existential_violation invindices xl x2 =
    List.fold_left (fun acc x1 ->
        match acc with
        | Some _ -> acc
        | _ ->
           match self#xpr_implies_universal_violation invindices x1 x2 with
           | Some r -> Some r
           | _ -> self#xpr1_implies_existential_violation invindices x1 x2) None xl

  method private inv_implies_violation inv1 inv2 =
    let invindices = [inv1#index; inv2#index] in
    match (inv1#lower_bound_xpr, inv2#upper_bound_xpr) with
    | (Some x1, Some x2) ->
       begin
         match self#xpr_implies_universal_violation invindices x1 x2 with
         | Some r -> Some r
         | _ ->
            match self#xpr1_implies_existential_violation invindices x1 x2 with
            | Some r -> Some r
            | _ ->
               match (inv1#upper_bound_xpr_alternatives, inv2#upper_bound_xpr) with
               | (Some [], _) -> None
               | (Some xl, Some x2) ->
                  self#xprlist_implies_existential_violation invindices xl x2
               | _ -> None
       end
    | _ ->
       match (inv1#upper_bound_xpr_alternatives, inv2#upper_bound_xpr) with
       | (Some [], _) -> None
       | (Some xl, Some x2) ->
          self#xprlist_implies_existential_violation invindices xl x2
       | _ -> None

  method check_violation =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _  ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_violation inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_violation_result deps msg;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1

  (* ----------------------- delegation ------------------------------------- *)

  method private inv_implies_delegation inv1 inv2 =
    match (inv1#expr, inv2#expr) with
    | (Some x1, Some x2) ->
       begin
         match (poq#x2api x1, poq#x2api x2) with
         | (Some a1, Some a2)
              when poq#is_api_expression x1 || poq#is_api_expression x2 ->
            let pred = self#mk_predicate a1 a2 in
            let deps = DEnvC ([inv1#index; inv2#index], [ApiAssumption pred]) in
            let msg =
              "condition " ^ (p2s (po_predicate_to_pretty pred))
              ^ " delegated to the api" in
            Some (deps,msg)
         | _ -> None
       end
    | _ -> None

  method check_delegation =
    match (invs1, invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_delegation inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1
end


let check_index_upper_bound (poq:po_query_int) (e1:exp) (e2:exp) =
  let invs1 = poq#get_invariants 1 in
  let invs2 = poq#get_invariants 2 in
  let _ = poq#set_diagnostic_invariants 1 in
  let _ = poq#set_diagnostic_invariants 2 in
  let checker = new index_upper_bound_checker_t poq e1 e2 invs1 invs2 in
  checker#check_safe || checker#check_violation || checker#check_delegation

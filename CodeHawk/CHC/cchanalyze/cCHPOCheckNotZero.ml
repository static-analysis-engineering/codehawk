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
open CHNumerical

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty

(* cchpre *)
open CCHPOPredicate
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes


let p2s = pretty_to_string
let e2s e = p2s (exp_to_pretty e)


class not_zero_checker_t
        (poq: po_query_int) (e: exp) (invs: invariant_int list) =
object (self)

  (* ----------------------------- safe ------------------------------------- *)

  method private inv_implies_safe (inv: invariant_int) =
    match inv#expr with
    | Some (XConst (IntConst n)) when n#gt numerical_zero ->
       let deps = DLocal [inv#index] in
       let msg = "value: " ^ n#toString ^ " is greater than zero" in
       Some (deps, msg)
    | Some (XConst (IntConst n)) when n#lt numerical_zero ->
       let deps = DLocal [inv#index] in
       let msg = "value: " ^ n#toString ^ " is less than zero" in
       Some (deps, msg)
    | Some (XVar v) when poq#env#is_function_return_value v ->
       let callee = poq#env#get_callvar_callee v in
       let (pcs, epcs) = poq#get_postconditions v in
       begin
         match (pcs,epcs) with
         | ([],_) ->
            let xpred = XNotZero ReturnValue in
            begin
              poq#mk_postcondition_request xpred callee;
              None
            end
         | (_,[]) ->
            List.fold_left (fun facc (pc, _) ->
                match facc with
                | Some _ -> facc
                | _ ->
                   match pc with
                   | XNotZero ReturnValue ->
                      let deps =
                        DEnvC ( [inv#index], [PostAssumption (callee.vid, pc)]) in
                      let msg =
                        Printf.sprintf
                          "return value from %s is guaranteed to be non-zero"
                          callee.vname in
                      Some (deps, msg)
                   | _ -> None) None pcs
         | _ -> None
       end
    | _ ->
       match inv#lower_bound_xpr with
       | Some (XConst (IntConst n)) when n#gt numerical_zero ->
          let deps = DLocal [inv#index] in
          let msg = "LB: " ^ n#toString ^ " is greater than zero" in
          Some (deps, msg)
       | _ ->
          match inv#upper_bound_xpr with
          | Some (XConst (IntConst n)) when n#lt numerical_zero ->
             let deps = DLocal [inv#index] in
             let msg = "UB: " ^ n#toString ^ " is less than zero" in
             Some (deps, msg)
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

  method private inv_implies_universal_violation (inv: invariant_int) =
    match inv#expr with
    | Some (XConst (IntConst n)) when n#equal numerical_zero ->
       let deps = DLocal [inv#index] in
       let msg = "value is zero" in
       Some (deps, msg)
    | _ -> None

  method private xpr_implies_existential_violation (invindex: int) (x: xpr_t) =
    match x with
    | XConst (IntConst n) when n#equal numerical_zero ->
       let deps = DLocal [invindex] in
       let msg = "value can be zero" in
       Some (deps, msg)
    | XVar v when poq#env#is_function_return_value v ->
       let callee = poq#env#get_callvar_callee v in
       let (pcs,epcs) = poq#get_postconditions v in
       List.fold_left (fun acc (pc, _) ->
           match acc with
           | Some _ -> acc
           | _ ->
              match pc with
              | XRelationalExpr (Eq, ReturnValue, NumConstant n)
                | XRelationalExpr (Eq, NumConstant n, ReturnValue)
                   when n#equal numerical_zero ->
                 let deps =
                   DEnvC ([invindex], [PostAssumption (callee.vid, pc)]) in
                 let msg =
                   Printf.sprintf
                     "return value from %s may be zero (perhaps an error value)"
                     callee.vname in
                 Some (deps,msg)
              | XTainted (ReturnValue, Some (NumConstant lb), Some (NumConstant ub))
                   when lb#leq numerical_zero && ub#geq numerical_zero ->
                 let deps =
                   DEnvC ([invindex], [PostAssumption (callee.vid, pc)]) in
                 let msg =
                   Printf.sprintf
                     ("return value from %s may be tainted: choose zero to "
                      ^^ "violate non-zero condition")
                     callee.vname in
                 Some (deps, msg)
              | _ -> None) None (pcs @ epcs)
    | _ -> None


  method private inv_implies_existential_violation (inv: invariant_int) =
    match inv#expr with
    | Some (XVar v) when poq#env#is_function_return_value v ->
       self#xpr_implies_existential_violation inv#index (XVar v)
    | _ ->
       match inv#lower_bound_xpr_alternatives with
       | Some l ->
          List.fold_left (fun acc x ->
              match acc with
              | Some _ -> acc
              | _ -> self#xpr_implies_existential_violation inv#index x) None l
    | _ -> None

  method check_violation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_universal_violation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_violation_result deps msg;
                  true
                end
             | _ ->
                match self#inv_implies_existential_violation inv with
                | Some (deps,msg) ->
                   begin
                     poq#record_violation_result deps msg;
                     true
                   end
                | _ -> false) false invs


  (* ----------------------- delegation ------------------------------------- *)

  method private inv_implies_delegation (inv: invariant_int) =
    match inv#expr with
    | Some x when poq#is_api_expression x ->
       let pred = PNotZero (poq#get_api_expression x) in
       let deps = DEnvC ( [inv#index], [ApiAssumption pred]) in
       let msg =
         Printf.sprintf
           "condition %s delegated to api" (p2s (po_predicate_to_pretty pred)) in
       Some (deps, msg)
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


let check_not_zero (poq: po_query_int) (e: exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new not_zero_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

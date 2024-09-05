(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023-2024 Aarno Labs LLC

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
open Xprt
open XprTypes
open XprToPretty
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty

(* cchpre *)
open CCHPOPredicate
open CCHPreTypes
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes


let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class index_lower_bound_checker_t
        (poq:po_query_int)
        (e:exp)
        (invs:invariant_int list) =
object (self)

  method private mk_predicate a = PIndexLowerBound a

  method mk_safe_constraint x = XOp (XGe, [x; zero_constant_expr])

  method mk_violation_constraint x = XOp (XLt, [x; zero_constant_expr])
                                 
  (* ----------------------------- safe ------------------------------------- *)
  method  private global_implies_safe invindex g =
    let pred = self#mk_predicate g in
    match poq#check_implied_by_assumptions pred with
    | Some pred ->
       let deps = DEnvC ([invindex], [GlobalApiAssumption pred]) in
       let msg =
         "index lower bound implied by global assumption: "
         ^ (p2s (po_predicate_to_pretty pred)) in
       Some (deps, msg)
    | _ ->
       let xpred = po_predicate_to_xpredicate poq#fenv pred in
       begin
         poq#mk_global_request xpred;
         None
       end

  method private var_implies_safe invindex v =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs, epcs) = poq#get_postconditions v in
      let _ = poq#set_diagnostic ("return value from " ^ callee.vname) in
      let r =
        match epcs with
        | [] ->
           List.fold_left (fun acc (pc, _) ->
               match acc with
               | Some _ ->  acc
               | _ ->
                  match pc with
                  | XRelationalExpr (Ge, ReturnValue, NumConstant n)
                    | XRelationalExpr (Eq, ReturnValue, NumConstant n)
                       when n#geq numerical_zero ->
                     let deps =
                       DEnvC ([invindex], [PostAssumption (callee.vid, pc)]) in
                     let msg =
                       "return value from " ^ callee.vname ^ " is non-negative" in
                     Some (deps,msg)
                  | _ -> None) None pcs
        | _ -> None in
      match r with
      | Some  _ -> r
      | _ ->
         let pc = XRelationalExpr (Ge, ReturnValue, NumConstant numerical_zero) in
         begin
           poq#mk_postcondition_request pc callee;
           None
         end
    else
      None

  method private xpr_implies_safe invindex x =
    let xconstraint = XOp (XGe, [x; zero_constant_expr]) in
    let sconstraint = simplify_xpr xconstraint in
    if is_true sconstraint then
      let deps = DLocal [invindex] in
      let msg =
        "index: "  ^ (x2s x) ^ " satisfies constraint: " ^ (x2s xconstraint) in
      Some (deps, msg)
    else if poq#is_global_expression x then
      match self#global_implies_safe invindex (poq#get_global_expression x) with
      | Some r -> Some r
      | _ ->
         begin
           poq#set_diagnostic ("remaining constraint: " ^ (x2s sconstraint));
           None
         end
    else
      match x with
      | XVar v -> self#var_implies_safe invindex v
      | _ ->
         None
    
  method private inv_implies_safe inv =
    match inv#lower_bound_xpr with
    | Some x -> self#xpr_implies_safe inv#index x
    | _ -> None
         
  method check_safe =
    match invs with
    | [] ->
       begin
         poq#set_diagnostic ("no invariants for " ^ (e2s e));
         false;
       end
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_safe inv with
             | Some (deps, msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs
      
  (* ----------------------- violation -------------------------------------- *)

  method private var_implies_violation invindex v xincr =
    if poq#env#is_tainted_value v then
      let xpr = XOp (XPlus, [XVar v; xincr]) in
      let vconstraint = self#mk_violation_constraint xpr in
      match poq#get_witness vconstraint v with
      | Some violationvalue -> 
         let (s, callee, pc) = poq#get_tainted_value_origin v in
         let deps = DEnvC ([invindex],[PostAssumption (callee.vid,pc)]) in
         let msg =
           s
           ^ " choose value: "
           ^ (x2s violationvalue)
           ^ " to violate the zero lower bound" in
         Some (deps, msg)
      | _ -> None
    else
      None

  method private xpr_implies_violation invindex x =
    match x with
    | XConst (IntConst n) when n#lt numerical_zero ->
       let deps = DLocal [invindex] in
       let msg  = "upper bound on index value is negative: " ^ n#toString in
       Some (deps, msg)
    | XVar v ->
       self#var_implies_violation invindex v zero_constant_expr
    | XOp (XPlus, [XVar v; xincr]) ->
       self#var_implies_violation invindex v xincr
    | XOp (XMinus, [XVar v; xdecr]) ->
       let xincr = simplify_xpr (XOp (XMinus, [zero_constant_expr; xdecr])) in
       self#var_implies_violation invindex v xincr
    | _ -> None

  (* conjunctive list of bounds; only  one needs to produce a violation *)
  method private xprlist_implies_violation invindex (xl:xpr_t list) =
    List.fold_left (fun acc x ->
        match acc with
        | Some _ -> acc
        | _ -> self#xpr_implies_violation invindex x)  None xl

  method private inv_implies_universal_violation inv =
    match inv#upper_bound_xpr with
    | Some x ->
       self#xpr_implies_violation inv#index x
    | _ ->
       match inv#upper_bound_xpr_alternatives with
       | Some  [] -> None
       | Some (h::tl) ->
          begin
            match self#xpr_implies_violation inv#index h with
            | Some r ->
               List.fold_left (fun acc x ->
                   match acc with
                   | None -> None
                   | Some (deps, msg) ->
                      match self#xpr_implies_violation inv#index x with
                      | Some (d, m) ->
                         let deps = join_dependencies deps d in
                         let msg = msg ^ ": " ^ m in
                         Some (deps, msg)
                      | _ -> None) (Some r) tl
            | _ -> None
          end
       | _ ->
          match inv#pepr_upper_bound with
          | Some [] -> None
          | Some (h::tl) ->
             begin
               match self#xprlist_implies_violation inv#index h with
               | Some r ->
                  List.fold_left (fun acc xl ->
                      match acc with
                      | None -> None
                      | Some (deps,msg) ->
                         match self#xprlist_implies_violation inv#index xl with
                         | Some (d, m) ->
                            let deps = join_dependencies deps d in
                            let msg = msg ^ "; " ^ m in
                            Some (deps, msg)
                         | _ -> None) (Some r) tl
               | _ -> None
             end
          | _ -> None
                  

  method private inv_implies_violation inv =
    match self#inv_implies_universal_violation inv with
    | Some r -> Some r
    | _ ->  None
          
  method check_violation =
    match invs with
    | [] -> false
    |  _ ->
        List.fold_left (fun acc inv ->
            acc ||
              match self#inv_implies_violation inv with
              | Some (deps, msg) ->
                 begin
                   poq#record_violation_result deps msg;
                   true
                 end
              | _ -> false) false invs

  (* ----------------------- delegation ------------------------------------- *)

  method private xpr_implies_delegation invindex x =
    if poq#is_api_expression x then
      let pred = self#mk_predicate (poq#get_api_expression x) in
      let deps = DEnvC ([invindex], [ApiAssumption pred]) in
      let msg =
        "condition "
        ^ (p2s (po_predicate_to_pretty pred))
        ^ " delegated to the api" in
      Some (deps, msg)
    else
      None

  method private inv_implies_delegation inv =
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
             | Some (deps, msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs
end


let check_index_lower_bound (poq:po_query_int) (e:exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new index_lower_bound_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

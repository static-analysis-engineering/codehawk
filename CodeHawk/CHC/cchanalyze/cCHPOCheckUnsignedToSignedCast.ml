(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHPretty
   
(* chutil *)
open CHPrettyUtil
   
(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify   
open XprUtil
   
(* cchlib *)
open CCHBasicTypes
open CCHTypesUtil

(* cchpre *)
open CCHPOPredicate
open CCHPreTypes
open CCHTypesToPretty
   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)

class unsigned_to_signed_cast_checker_t
      (poq:po_query_int)
      (kfrom:ikind)
      (kto:ikind)
      (exp:exp)
      (invs:invariant_int list) =
object (self)

  val safeub = get_safe_upperbound kto
  val xsafeub = num_constant_expr (get_safe_upperbound kto)

  method private mk_safe_constraint x = XOp (XLe, [ x ; xsafeub ])

  method private mk_violation_constraint x = XOp (XGt, [ x ; xsafeub ])

  method private get_predicate e = PUnsignedToSignedCast (kfrom,kto,e)

  (* ----------------------------- safe ------------------------------------- *)

  method private xpr_implies_safe_ub invindex x =
    match x with
    | XConst (IntConst n) when n#leq safeub ->
       let deps = DLocal [ invindex ] in
       let msg = "UB: " ^ n#toString ^ " satisfies safe UB: " ^ safeub#toString in
       Some (deps,msg)
    | x when poq#is_global_expression x ->
       let pred = self#get_predicate (poq#get_global_expression x) in
       begin
         match poq#check_implied_by_assumptions pred with
         | Some pred ->
            let deps = DEnvC ( [ invindex ],[ GlobalApiAssumption pred ]) in
            let msg =
              "safe UB: " ^ safeub#toString
              ^ " is implied by global assumption: "
              ^ (p2s (po_predicate_to_pretty pred)) in
            Some (deps,msg)
         | _ ->
            let xpred = po_predicate_to_xpredicate poq#fenv pred in
            begin
              poq#mk_global_request xpred ;
              None
            end
       end
    | _ -> None

  method private inv_implies_safe_ub inv =
    match inv#upper_bound_xpr with
    | Some x -> self#xpr_implies_safe_ub inv#index x
    | _ -> None

  method check_safe =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_safe_ub inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg ;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- violation ------------------------------------- *)

  method private inv_implies_universal_violation inv =
    match inv#lower_bound_xpr with
    | Some (XConst (IntConst n)) when n#gt safeub ->
       let deps = DLocal [ inv#index ] in
       let msg =
         "LB: " ^ n#toString ^ " violates safe UB: " ^ safeub#toString
         ^ " (universal)" in
       Some (deps,msg)
    | _ -> None

  method private inv_implies_existential_violation inv =
    let result =
      match inv#upper_bound_xpr with
      | Some (XVar v) when poq#env#is_tainted_value v ->
         let vconstraint = self#mk_violation_constraint (XVar v) in
         begin
           match poq#get_witness vconstraint v with
           | Some violationvalue -> Some (v,(XVar v),violationvalue)
           | _ -> None
         end
      | Some (XOp (op, [ XVar v ;  x2 ]) as x) when not (occurs_check v x2) ->
         let vconstraint = self#mk_violation_constraint x in
         begin
           match poq#get_witness vconstraint v with
           | Some violationvalue -> Some (v,x,violationvalue)
           | _ -> None
         end
      | Some (XOp (op, [ x2 ; XVar v ]) as x) when not (occurs_check v x2) ->
         let vconstraint = self#mk_violation_constraint x in
         begin
           match poq#get_witness vconstraint v with
           | Some violationvalue -> Some (v,x,violationvalue)
           | _ -> None
         end
      | Some x ->
         let vconstraint = self#mk_violation_constraint x in
         begin
           poq#set_diagnostic ("violation target: " ^ (x2s vconstraint)) ;
           None
         end
      | _ -> None in
    match result with
    | Some (v,x,violationvalue) ->
       let safeconstraint = self#mk_safe_constraint x in
       let (s,callee,pc) = poq#get_tainted_value_origin v in
       let deps = DEnvC ([ inv#index ],[ PostAssumption (callee.vid,pc) ]) in
       let msg =
         s ^ " choose value: " ^ (x2s violationvalue)
         ^ " to violate the safety constraint: "
         ^ (x2s safeconstraint) in
       Some (deps,msg)
    | _ -> None
        
  method private inv_implies_violation inv =
    match self#inv_implies_universal_violation inv with
    | Some r -> Some r
    | _ -> self#inv_implies_existential_violation inv

  method check_violation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_violation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_violation_result deps msg ;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- delegation ------------------------------------- *)

  method private inv_implies_delegation inv =
    match inv#upper_bound_xpr with
    | Some x when poq#is_api_expression x ->
       let pred = self#get_predicate (poq#get_api_expression x) in
       let deps  = DEnvC ( [ inv#index ], [ ApiAssumption pred ]) in
       let msg =
         "condition " ^ (p2s (po_predicate_to_pretty pred))
         ^ " delegated to api" in
       Some (deps,msg)
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
                   poq#record_safe_result deps msg ;
                   true
                 end
              | _ -> false) false invs
end

let check_unsigned_to_signed_cast
      (poq:po_query_int)
      (kfrom:ikind)
      (kto:ikind)
      (e:exp) =
  let invs = poq#get_invariants 3 in
  let _ = poq#set_diagnostic_invariants 3 in
  let checker = new unsigned_to_signed_cast_checker_t poq kfrom kto e invs in
  checker#check_safe  || checker#check_violation || checker#check_delegation
         

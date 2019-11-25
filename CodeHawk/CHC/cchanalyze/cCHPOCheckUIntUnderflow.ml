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
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHSumTypeSerializer
open CCHTypesToPretty
open CCHTypesUtil

(* cchpre *)
open CCHInvariantFact
open CCHPreTypes
open CCHPOPredicate
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes
open CCHPOCheckIntUtil

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)

let nonneg (x:xpr_t) =
  match x with
  | XConst (IntConst n) -> n#geq numerical_zero
  | _ -> false    

let nonpos (x:xpr_t) =
  match x with
  | XConst (IntConst n) -> n#leq numerical_zero
  | _ -> false
     

(* ========================================================================== *)
(* ===================================== PlusA ============================== *)
(* ========================================================================== *)
class plus_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list)
        (k:ikind) =
object (self)

  (* ----------------------------- safe ------------------------------------- *)
  method check_safe = false
                    
  (* ----------------------- violation ------------------------------------- *)
  method check_violation = false
       
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end

(* ========================================================================== *)
(* ===================================== Mult =============================== *)
(* ========================================================================== *)

class mult_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list)
        (k:ikind) =
object (self)
         
  (* ----------------------------- safe ------------------------------------- *)
  method check_safe = false

  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false

  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false

end

(* ========================================================================== *)
(* ===================================== MinusA ============================= *)
(* ========================================================================== *)

class minus_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list)
        (k:ikind) =
object (self)

  val safelb = numerical_zero
  val xsafelb = num_constant_expr numerical_zero

  method private global_str x =
    match x with
    | XVar v when poq#env#is_initial_global_value v -> " (global)"
    | _ -> ""

  method private inv_implies_non_negative e inv =
    match inv#lower_bound_xpr with
    | Some (XConst (IntConst n)) when n#geq numerical_zero ->
       let deps = DLocal [ inv#index ] in
       let msg = "value of " ^ (e2s e) ^ " is non-negative: " ^ n#toString in
       Some (deps,msg)
    | _ -> None

  method private inv_implies_non_positive e inv =
    match inv#upper_bound_xpr with
    | Some (XConst (IntConst n)) when n#leq numerical_zero ->
       let deps = DLocal [ inv#index ] in
       let msg = "value of " ^ (e2s e) ^ " is non-positive: " ^ n#toString in
       Some (deps,msg)
    | _ -> None

  method private mk_safe_constraint (x1:xpr_t) (x2:xpr_t) =
    let xresult = XOp (XMinus, [ x1 ; x2 ]) in
    XOp (XGe, [ xresult ; xsafelb ])

  method private mk_violation_constraint (x1:xpr_t) (x2:xpr_t) =
    let xresult = XOp (XMinus, [ x1 ; x2 ]) in
    XOp (XLt, [ xresult ; xsafelb ])

  method private get_predicate e1 e2 = PUIntUnderflow (MinusA, e1, e2, k)
              
  (* ----------------------------- safe ------------------------------------- *)

  method private inv_implies_safe inv1 inv2 =
    match (inv1#lower_bound_xpr, inv2#upper_bound_xpr) with
    | (Some x1, Some x2) ->
       let safeconstraint = self#mk_safe_constraint x1 x2 in
       let simconstraint = simplify_xpr safeconstraint in
       let _ = poq#set_diagnostic_arg 2 ("LB: " ^ (x2s x1) ^ (self#global_str x1)) in
       let _ = poq#set_diagnostic_arg 3 ("UB: " ^ (x2s x1) ^ (self#global_str x2)) in
       if is_true simconstraint then
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "result of subtraction  satisfies constraint " ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         let xresult = XOp  (XMinus, [ x1 ; x2 ]) in
         begin
           match simplify_xpr xresult with
           | XVar v when poq#env#is_fixed_value v ->
              let deps = DLocal [ inv1#index ; inv2#index ] in
              let msg = "result of subtraction is equal to external value: "
                        ^ (x2s xresult) ^ " = " ^ v#getName#getBaseName in
              Some (deps,msg)
           | _ ->
              if poq#is_global_expression x1 then
                match x2 with
                | XConst (IntConst n) ->
                   let gx = poq#get_global_expression x1 in
                   let pred = self#get_predicate gx (make_constant_exp n) in
                   begin
                     match poq#check_implied_by_assumptions pred with
                     | Some pred ->
                        let deps = DEnvC ( [ inv1#index ; inv2#index ],
                                           [ GlobalApiAssumption pred ]) in
                        let msg = "safety constraint " ^ (x2s safeconstraint)
                                  ^ " implied by global assumption: "
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
              else
                begin
                  poq#set_diagnostic
                    ("remaining constraint: " ^ (x2s simconstraint)) ;
                  None
                end
         end
    | (Some x1, _) ->
       let _ = poq#set_diagnostic_arg 2 ("LB: " ^ (x2s x1) ^ (self#global_str x1)) in
       self#inv_implies_non_negative e1 inv1
    | (_, Some x2) ->
       let _ = poq#set_diagnostic_arg 3 ("UB: " ^ (x2s x2) ^ (self#global_str x2)) in
       self#inv_implies_non_positive e2 inv2
    | _ -> None
         
  method check_safe =
    match invs1 with
    | [] ->
       begin
         match invs2 with
         | [] -> false
         | _ ->
            List.fold_left (fun acc inv ->
                acc ||
                  match self#inv_implies_non_positive e2 inv with
                  | Some (deps,msg) ->
                     begin
                       poq#record_safe_result deps msg ;
                       true
                     end
                  | _ -> false) false invs2
       end
    | _ ->
       match invs2 with
       | [] ->
          List.fold_left (fun acc inv ->
              acc ||
                match self#inv_implies_non_negative e1 inv with
                | Some (deps,msg) ->
                   begin
                     poq#record_safe_result deps msg ;
                     true
                   end
                | _ -> false) false invs1
       | _ ->
          List.fold_left (fun acc1 inv1 ->
              acc1 ||
                List.fold_left (fun acc2 inv2 ->
                    acc2 ||
                      match self#inv_implies_safe inv1 inv2 with
                      | Some (deps,msg) ->
                         begin
                           poq#record_safe_result deps msg ;
                           true
                         end
                      | _ -> false) acc1 invs2) false invs1
                  

  (* ----------------------- violation ------------------------------------- *)

  method private universal_violation inv1 inv2 =
    match (inv1#upper_bound_xpr, inv2#upper_bound_xpr) with
    | (Some x1, Some x2) ->
       let safeconstraint = self#mk_safe_constraint x1 x2 in
       let violationconstraint = self#mk_violation_constraint x1 x2 in
       let simconstraint = simplify_xpr violationconstraint in
       if is_true simconstraint then
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "UB on result of subtraction violates condition "
                   ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         None
    | _ -> None

  method private existential_violation inv1 inv2 =
    match (get_existential_min_values poq inv1, get_existential_max_values poq inv2) with
    | ([],_) | (_,[]) -> None
    | (vl1,vl2) ->
       List.fold_left (fun acc1 (b1,deps1,msg1) ->
           match acc1 with
           | Some _ -> acc1
           | _ ->
              List.fold_left (fun acc2 (b2,deps2,msg2) ->
                  match acc2 with
                  | Some _ -> acc2
                  | _ ->
                     if (b1#sub b2)#lt safelb then
                       let deps = join_dependencies deps1 deps2 in
                       let msg = "result of subtraction: "
                                 ^ (b1#sub b2)#toString
                                 ^ " violates safe LB: " ^ safelb#toString
                                 ^ " (" ^ msg1 ^  "; " ^ msg2 ^ ")" in
                       Some (deps,msg)
                     else
                       None) acc1 vl2) None vl1
      
  method check_violation =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _  ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#universal_violation inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_violation_result deps msg ;
                        true
                      end
                   | _ ->
                      match self#existential_violation inv1 inv2 with
                      | Some (deps,msg) ->
                         begin
                           poq#record_violation_result deps msg ;
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
            let pred = self#get_predicate a1 a2 in
            let deps = DEnvC ([ inv1#index ; inv2#index ],[ ApiAssumption pred]) in
            let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
                      ^ " delegated to api" in
            Some (deps,msg)
         | _ -> None
       end
    | _ -> None
         
  method check_delegation =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_delegation inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg ;
                        true
                      end
                   | _ -> false ) acc1 invs2) false invs1
                      
end

class div_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list)
        (k:ikind) =
object
  method check_safe = false
  method check_violation = false
  method check_delegation = false
end

class generic_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list)
        (k:ikind) =
object
  method check_safe = false
  method check_violation = false
  method check_delegation = false
end


let check_unsigned_int_underflow
      (poq:po_query_int)
      (op:binop)
      (e1:exp)
      (e2:exp)
      (k:ikind) =
  let values2 = poq#get_invariants 2 in
  let values3 = poq#get_invariants 3 in
  let _ = poq#set_diagnostic_invariants 2 in
  let _ = poq#set_diagnostic_invariants 3 in
  let checker =
    match op with
    | PlusA -> new plus_checker_t poq e1 e2 values2 values3 k
    | Mult -> new mult_checker_t poq e1 e2 values2 values3 k
    | MinusA -> new minus_checker_t poq e1 e2 values2 values3 k
    | Div -> new div_checker_t poq e1 e2 values2 values3 k
    | _ -> new generic_checker_t poq e1 e2 values2 values3 k in
  checker#check_safe || checker#check_violation || checker#check_delegation

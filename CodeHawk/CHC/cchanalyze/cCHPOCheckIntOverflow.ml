(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
open CCHUtilities

(* cchpre *)
open CCHInvariantFact
open CCHPreTypes
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes
open CCHPOCheckIntUtil
open CCHPOPredicate

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)

          
class type int_overflow_checker_int =
  object
    method check_safe: bool
    method check_violation: bool
    method check_delegation: bool
  end

(* ========================================================================== *)
(* ===================================== PlusA ============================== *)
(* ========================================================================== *)
class plus_checker
        ?(unsigned=false)
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list)
        (k:ikind) =
object (self)

  val safeub = get_safe_upperbound k
  val xsafeub = num_constant_expr (get_safe_upperbound k)

  method private global_str x =
    match x with
    | XVar v when poq#env#is_initial_global_value v -> " (global)"
    | _ -> ""

  method private inv_implies_non_positive e inv =
    match inv#upper_bound_xpr with
    | Some (XConst (IntConst n)) when n#leq numerical_zero ->
       let deps = DLocal [ inv#index ] in
       let msg = "value of " ^ (e2s e) ^ " is non-positive: " ^ n#toString in
       Some (deps,msg)
    | _ -> None

  method private mk_safe_constraint (x1:xpr_t) (x2:xpr_t) =
    let xresult = XOp (XPlus, [ x1 ; x2 ]) in
    XOp (XLe, [ xresult ; xsafeub ])

  method private mk_violation_constraint (x1:xpr_t) (x2:xpr_t) =
    let xresult = XOp (XPlus, [ x1 ; x2 ]) in
    XOp (XGt, [ xresult ; xsafeub ])

  method private get_predicate e1 e2 =
    if unsigned then
      PUIntOverflow (PlusA, e1, e2, k)
    else
      PIntOverflow (PlusA, e1, e2, k)

  method private get_base_invariants e =
    match e with
    | Lval (Mem e, _) -> poq#get_exp_invariants e
    | _ -> []

  method private get_struct_field e =
    match e with
    | Lval (Mem e, Field ((name,_),NoOffset)) -> Some name
    | _ -> None

  method private get_struct_field_upper_bound arg v name =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,epcs) = poq#get_postconditions v in
      match epcs with
      | [] | [ (XNull _,_) ]  ->
         List.fold_left
           (fun acc (pc,_) ->
             match acc with
             | Some _ -> acc
             | _ ->
                match pc with
                | XTainted
                  (ArgAddressedValue
                     (ReturnValue,ArgFieldOffset (fname,ArgNoOffset)), lb, ub)
                     when name = fname ->
                   let _ = poq#set_diagnostic_arg arg ("tainted field value: " ^ fname) in      
                   (match ub with
                    | Some (NumConstant n) ->
                       let msg =
                         "field " ^ name ^ " returned by " ^ callee.vname
                         ^ " is tainted with upperbound " ^ n#toString in
                       Some ([],msg,num_constant_expr n)
                    | _ -> None)
                | _ -> None) None pcs
      | _ ->
         let _ =
           poq#set_diagnostic_arg arg ("error postconditions on " ^ (p2s v#toPretty)) in
         None
    else
      None

  method private get_deref_field_upper_bound arg e name =
    let invs = self#get_base_invariants e in
    List.fold_left
      (fun acc inv ->
        match acc with
        | Some _ -> acc
        | _ ->
           match inv#symbolic_expr with
           | Some (XVar v) when poq#env#is_memory_address v ->
              let (memref,offset) = poq#env#get_memory_address v in
              begin
                match memref#get_base with
                | CBaseVar bv ->
                   let _ = poq#set_diagnostic_arg arg ("base var: " ^ (p2s bv#toPretty)) in
                   begin
                     match self#get_struct_field_upper_bound arg bv name with
                     | Some (deps,msg,ub) ->
                        let deps = deps @ [ inv#index ] in
                        Some (deps,msg,ub)
                     | _ -> None
                   end
                | _ -> None
              end
           | _ -> None) None invs


  (* ----------------------------- safe ------------------------------------- *)

  method private check_struct_field_invariants_1 inv2 =
    match self#get_struct_field e1 with
    | Some name ->
       begin
         match (self#get_deref_field_upper_bound 2 e1 name,inv2#upper_bound_xpr) with
         | (Some (fdeps,fmsg,ub1), Some ub2) ->
            let safeconstraint = self#mk_safe_constraint ub1 ub2 in
            let simconstraint = simplify_xpr safeconstraint in
            let _ = poq#set_diagnostic_arg 2 ("UB: " ^ (x2s ub1) ^ (self#global_str ub1)) in
            let _ = poq#set_diagnostic_arg 3 ("UB: " ^ (x2s ub2) ^ (self#global_str ub2)) in
            if is_true simconstraint then
              let deps = DLocal (fdeps @ [ inv2#index ]) in
              let msg2 = "upper bound on " ^ (e2s e2) ^ ": " ^ (x2s ub2) in
              let msg = fmsg ^ "; " ^ msg2 ^ "; " ^ (x2s safeconstraint) in
              Some (deps,msg)
            else
              None
         | _ -> None
       end
    | _ -> None

  method private inv_implies_safe inv1 inv2 =
    match (inv1#upper_bound_xpr, inv2#upper_bound_xpr) with
    | (Some ub1, Some ub2) ->
       let safeconstraint = self#mk_safe_constraint ub1 ub2 in
       let simconstraint = simplify_xpr safeconstraint in
       let _ = poq#set_diagnostic_arg 2 ("UB: " ^ (x2s ub1) ^ (self#global_str ub1)) in
       let _ = poq#set_diagnostic_arg 3 ("UB: " ^ (x2s ub2) ^ (self#global_str ub2)) in
       if is_true simconstraint then
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "result of addition satisfies constraint " ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         let xresult = XOp (XPlus, [ ub1 ; ub2 ]) in
         begin
           match simplify_xpr xresult with
           | XVar v when poq#env#is_fixed_value v ->
              let deps = DLocal [ inv1#index ; inv2#index ] in
              let msg  = "result of addition is equal to external value: "
                         ^ (x2s xresult) ^ " = " ^ v#getName#getBaseName in
              Some (deps,msg)
           | _ ->
              if poq#is_global_expression ub1 then
                match ub2 with
                | XConst (IntConst n) ->
                   let gx = poq#get_global_expression ub1 in
                   let pred = self#get_predicate gx (make_constant_exp n) in
                   begin
                     match poq#check_implied_by_assumptions pred with
                     | Some pred ->
                        let deps = DEnvC ([inv1#index ; inv2#index ],
                                          [GlobalApiAssumption  pred ]) in
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
    | (Some ub1,_) ->
       let _ = poq#set_diagnostic_arg 2 ("UB: " ^ (x2s ub1) ^ (self#global_str ub1)) in
       self#inv_implies_non_positive e1 inv1
    | (_, Some ub2) ->
       let _ = poq#set_diagnostic_arg 3 ("UB: " ^ (x2s ub2) ^ (self#global_str ub2)) in
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
                  | _ ->
                     match self#check_struct_field_invariants_1 inv with
                     | Some (deps,msg) ->
                        begin
                          poq#record_safe_result deps msg;
                          true;
                        end
                     | _ -> false) false invs2
       end
    | _ ->
       match invs2 with
       | [] ->
          List.fold_left (fun acc inv ->
              acc ||
                match self#inv_implies_non_positive e1 inv with
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
    match (inv1#lower_bound_xpr, inv2#lower_bound_xpr) with
    | (Some lb1, Some lb2) ->
       let safeconstraint = self#mk_safe_constraint lb1 lb2 in
       let violationconstraint = self#mk_violation_constraint lb1 lb2 in
       let simconstraint = simplify_xpr violationconstraint in
       if is_true simconstraint then
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "LB on result of addition violates condition "
                   ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         None
    | _ -> None

  method private existential_violation inv1 inv2 =
    match (get_existential_max_values poq inv1, get_existential_max_values poq inv2) with
    | ([],_) | (_, []) -> None
    | (vl1,vl2) ->
       List.fold_left (fun acc1 (ub1,deps1,msg1) ->
           match acc1 with
           | Some _ -> acc1
           | _ ->
              List.fold_left (fun acc2 (ub2,deps2,msg2) ->
                  match acc2 with
                  | Some _ -> acc2
                  | _ ->
                     if (ub1#add ub2)#gt safeub then
                       let deps = join_dependencies deps1 deps2 in
                       let msg = "result of addition: "
                                 ^ (ub1#add ub2)#toString
                                 ^ " violates safe UB: " ^ safeub#toString
                                 ^ " (" ^ msg1 ^ "; " ^  msg2  ^ ")" in
                       Some (deps,msg)
                     else
                       None) acc1 vl1) None vl2
                               
  method check_violation =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2  ||
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
                      |_ -> false) acc1 invs2) false invs1

  (* ----------------------- delegation ------------------------------------- *)

  method private inv_implies_delegation inv1 inv2 =
    match (inv1#expr, inv2#expr) with
    | (Some x1, Some x2) ->
       begin
         match (poq#x2api x1, poq#x2api x2) with
         | (Some a1, Some a2) ->
            let pred = self#get_predicate a1 a2 in
            let deps = DEnvC ([ inv1#index; inv2#index ],[ApiAssumption pred ]) in
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
                   | _ -> false) acc1 invs2) false invs1
end


(* ========================================================================== *)
(* ===================================== Mult =============================== *)
(* ========================================================================== *)

class mult_checker
        ?(unsigned=false)
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list)
        (k:ikind) =
object (self)

  val safeub = get_safe_upperbound k
  val xsafeub = num_constant_expr (get_safe_upperbound k)

  method private global_str x =
    match x with
    | XVar v when poq#env#is_initial_global_value v -> " (global)"
    | _ -> ""

  method private inv_implies_non_positive e inv =
    match inv#upper_bound_xpr with
    | Some (XConst (IntConst n)) when n#leq numerical_zero ->
       let deps = DLocal [ inv#index ] in
       let msg = "value of " ^ (e2s e) ^ " is non-positive: " ^ n#toString in
       Some (deps,msg)
    | _ -> None

  method private inv_implies_non_negative e inv =
    match inv#lower_bound_xpr with
    | Some (XConst (IntConst n)) when n#geq numerical_zero ->
       let deps = DLocal [ inv#index ] in
       let msg = "value of " ^ (e2s e) ^ " is non-negative: " ^ n#toString in
       Some (deps,msg)
    | _ -> None

  method private is_positive inv =
    match inv#lower_bound_xpr with
    | Some (XConst (IntConst n)) -> n#gt numerical_zero
    | _ -> false

  method private is_negative inv =
    match inv#upper_bound_xpr with
    | Some (XConst (IntConst n)) -> n#lt numerical_zero
    | _ -> false                 

  method private mk_safe_constraint (x1:xpr_t) (x2:xpr_t) =
    let xresult = XOp (XMult, [ x1 ; x2 ]) in
    XOp (XLe, [ xresult ; xsafeub ])

  method private mk_violation_constraint (x1:xpr_t) (x2:xpr_t) =
    let xresult = XOp (XMult, [ x1 ; x2 ]) in
    XOp (XGt, [ xresult ; xsafeub ])

  method private get_predicate e1 e2 =
    if unsigned then
      PUIntOverflow (Mult, e1, e2, k)
    else
      PIntOverflow (Mult, e1, e2, k)

  (* ----------------------------- safe ------------------------------------- *)

  method private inv_implies_safe_pp inv1 inv2 =
    match (inv1#upper_bound_xpr, inv2#upper_bound_xpr) with
    | (Some x1, Some x2) ->
       let safeconstraint = self#mk_safe_constraint x1 x2 in
       let simconstraint = simplify_xpr safeconstraint in
       let _ = poq#set_diagnostic_arg 2 ("LB: " ^ (x2s x1) ^ (self#global_str x1)) in
       let _ = poq#set_diagnostic_arg 3 ("LB: " ^ (x2s x2) ^ (self#global_str x2)) in
       if is_true simconstraint then
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "result of upper-bound multiplication satisfies constraint "
                   ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         if poq#is_global_expression x1 then
           match x2 with
           | XConst  (IntConst n) ->
              let gx = poq#get_global_expression x1 in
              let pred = self#get_predicate gx (make_constant_exp n) in
              begin
                match poq#check_implied_by_assumptions pred with
                | Some pred ->
                   let deps = DEnvC( [ inv1#index ; inv2#index ],[GlobalApiAssumption pred ]) in
                   let msg = "safety constraint " ^  (x2s safeconstraint)
                             ^  " implied by  global assumption: "
                             ^ (p2s (po_predicate_to_pretty  pred)) in
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
           None
    | (Some x1, _) ->
       let _ = poq#set_diagnostic_arg 2 ("UB: " ^ (x2s x1) ^ (self#global_str x1)) in       
       self#inv_implies_non_positive e1 inv1
    | (_, Some x2) ->
       let _ = poq#set_diagnostic_arg 3 ("UB: " ^ (x2s x2) ^ (self#global_str x2)) in
       self#inv_implies_non_positive e2 inv2
    | _ ->  None

  method private inv_implies_safe_nn inv1 inv2 =
    match (inv1#lower_bound_xpr, inv2#lower_bound_xpr) with
    | (Some x1, Some x2) ->
       let safeconstraint = self#mk_safe_constraint x1 x2 in
       let simconstraint = simplify_xpr safeconstraint in
       let _ = poq#set_diagnostic_arg 2 ("LB: " ^ (x2s x1) ^ (self#global_str x1)) in
       let _ = poq#set_diagnostic_arg 3 ("LB: " ^ (x2s x2) ^ (self#global_str x2)) in
       if is_true simconstraint then
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "result of lower-bound multiplication satisfies constraint "
                   ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         if poq#is_global_expression x1 then
           match x2 with
           | XConst  (IntConst n) ->
              let gx = poq#get_global_expression x1 in
              let pred = self#get_predicate gx (make_constant_exp n) in
              begin
                match poq#check_implied_by_assumptions pred with
                | Some pred ->
                   let deps = DEnvC( [ inv1#index ; inv2#index ],[GlobalApiAssumption pred ]) in
                   let msg = "safety constraint " ^  (x2s safeconstraint)
                             ^  " implied by  global assumption: "
                             ^ (p2s (po_predicate_to_pretty  pred)) in
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
           None
    | (Some x1, _) ->
       let _ = poq#set_diagnostic_arg 2 ("LB: " ^ (x2s x1) ^ (self#global_str x1)) in       
       self#inv_implies_non_negative e1 inv1
    | (_, Some x2) ->
       let _ = poq#set_diagnostic_arg 3 ("LB: " ^ (x2s x2) ^ (self#global_str x2)) in
       self#inv_implies_non_negative e2 inv2
    | _ -> None
         
  method private check_safe_pp =
    match invs1 with
    | [] ->
       begin
         match invs2 with
         | [] -> None
         | _ ->
            List.fold_left  (fun acc inv ->
                match acc with
                | Some _ -> acc
                | _ -> self#inv_implies_non_positive e2 inv) None invs2
       end
    | _ ->
       match invs2 with
       | [] ->
          List.fold_left (fun acc inv ->
              match acc with
              | Some _ -> acc
              | _ -> self#inv_implies_non_positive e1 inv) None invs1
       | _ ->
          List.fold_left (fun acc1 inv1 ->
              match acc1 with
              | Some _ -> acc1
              | _ ->
                 List.fold_left (fun acc2 inv2 ->
                     match acc2 with
                     | Some _ -> acc2
                     | _ -> self#inv_implies_safe_pp inv1 inv2) acc1 invs2) None invs1
         
  method private check_safe_nn =
    match invs1 with
    | [] ->
       begin
         match invs2 with
         | [] -> None
         | _ ->
            List.fold_left  (fun acc inv ->
                match acc with
                | Some _ -> acc
                | _ -> self#inv_implies_non_negative e2 inv) None invs2
       end
    | _ ->
       match invs2 with
       | [] ->
          List.fold_left (fun acc inv ->
              match acc with
              | Some _ -> acc
              | _ -> self#inv_implies_non_negative e1 inv) None invs1
       | _ ->
          List.fold_left (fun acc1 inv1 ->
              match acc1 with
              | Some _ -> acc1
              | _ ->
                 List.fold_left (fun acc2 inv2 ->
                     match acc2 with
                     | Some _ -> acc2
                     | _ -> self#inv_implies_safe_nn inv1 inv2) acc1 invs2) None invs1
         
  method check_safe =  (* safe if ub * ub <= MAX and lb * lb <= MAX *)
    match (self#check_safe_nn, self#check_safe_pp) with
    | (Some (deps1,msg1),  Some (deps2,msg2)) ->
       let deps = join_dependencies deps1 deps2 in
       let msg = "LB*LB: " ^ msg1 ^ "; UB*UB: " ^ msg2 in
       begin
         poq#record_safe_result deps msg ;
         true
       end
    | (Some (deps1,msg1), _ ) ->
       begin
         poq#set_diagnostic ("LB*LB: " ^ msg1) ;
         false
       end
    | (_, Some (deps2,msg2)) ->
       begin
         poq#set_diagnostic ("UB*UB: " ^ msg2) ;
         false
       end
    | _ -> false

  (* ----------------------- violation -------------------------------------- *)

  method private inv_implies_universal_violation_pp inv1 inv2 =
    match (inv1#lower_bound_xpr, inv2#lower_bound_xpr) with
    | (Some x1, Some x2) when self#is_positive inv1 && self#is_positive inv2 ->
       let violationconstraint = self#mk_violation_constraint x1 x2 in
       let simconstraint = simplify_xpr violationconstraint in
       if is_true simconstraint then
         let safeconstraint = self#mk_safe_constraint x1 x2 in
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "pos_LB*pos_LB result of multiplication violates constraint "
                   ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         None
    | _ -> None

  method private universal_violation_pp =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_universal_violation_pp inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_violation_result deps msg ;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1

  method private inv_implies_universal_violation_nn inv1 inv2 =
    match (inv1#upper_bound_xpr, inv2#upper_bound_xpr) with
    | (Some x1, Some x2) when self#is_negative inv1 && self#is_negative inv2 ->
       let violationconstraint = self#mk_violation_constraint x1 x2 in
       let simconstraint = simplify_xpr violationconstraint in
       if is_true simconstraint then
         let safeconstraint = self#mk_safe_constraint x1 x2 in
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "neg_UB*neg_UB result of multiplication violates constraint "
                   ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         None
    | _ -> None

  method private universal_violation_nn =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_universal_violation_nn inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_violation_result deps msg ;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1
      
  method private inv_implies_existential_violation xsl1 xsl2 =
    match (xsl1,xsl2) with
    | ([],_) | (_,[]) -> None
    | _ ->
       List.fold_left (fun acc1 (b1,deps1,msg1) ->
           match acc1 with
           | Some _ -> acc1
           | _ ->
              List.fold_left (fun acc2 (b2,deps2,msg2) ->
                  match acc2 with
                  | Some _ -> acc2
                  | _ ->
                     if (b1#mult b2)#gt safeub then
                       let deps = join_dependencies deps1 deps2 in
                       let msg = "result of multiplication: " ^ (b1#mult b2)#toString
                                 ^ " violates safe UB: " ^ safeub#toString
                                 ^  " (" ^  msg1 ^  "; " ^ msg2 ^ ")"  in
                       Some (deps,msg)
                     else
                       None) acc1 xsl2) None xsl1

  method private existential_violation_pp =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   (let xsl1 = get_existential_max_values poq inv1 in
                    let xsl2 = get_existential_max_values poq inv2 in
                    match self#inv_implies_existential_violation xsl1 xsl2 with
                    | Some (deps,msg) ->
                       begin
                         poq#record_violation_result deps msg ;
                         true
                       end
                    | _ -> false)) acc1 invs2) false invs1

  method private existential_violation_nn =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   (let xsl1 = get_existential_min_values poq inv1 in
                    let xsl2 = get_existential_min_values poq inv2 in
                    match self#inv_implies_existential_violation xsl1 xsl2 with
                    | Some (deps,msg) ->
                       begin
                         poq#record_violation_result deps msg ;
                         true
                       end
                    | _ -> false)) acc1 invs2) false invs1
    

  method check_violation =
    self#universal_violation_nn        (* ub1 * ub2 > MAX, ub1, ub2 < 0 *)
    || self#universal_violation_pp     (* lb1 * lb2 > MAX, lb1, lb2 > 0 *)
    || self#existential_violation_nn   
    || self#existential_violation_pp

  (* ----------------------- delegation ------------------------------------- *)

  method private inv_implies_delegation inv1 inv2 =
    match (inv1#expr,  inv2#expr) with
    | (Some x1, Some x2) ->
       begin
         match (poq#x2api x1, poq#x2api x2) with
         | (Some a1, Some a2)
              when poq#is_api_expression x1 || poq#is_api_expression x2 ->
            let pred = self#get_predicate a1 a2 in
            let deps = DEnvC ([ inv1#index ; inv2#index ],[ApiAssumption pred]) in
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
                   match self#inv_implies_delegation inv1 inv2  with
                   | Some (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg ;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1
                        
end

(* ========================================================================== *)
(* ===================================== MinusA ============================= *)
(* ========================================================================== *)

class minus_checker
        ?(unsigned=false)
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list)
        (k:ikind) =
object (self)

  val safeub = get_safe_upperbound k
  val xsafeub = num_constant_expr (get_safe_upperbound k)

  method private global_str x =
    match x with
    | XVar v when poq#env#is_initial_global_value v -> " (global)"
    | _ -> ""

  method private inv_implies_non_positive e inv =
    match inv#upper_bound_xpr with
    | Some (XConst (IntConst n)) when n#leq numerical_zero ->
       let deps = DLocal [ inv#index ] in
       let msg = "value of " ^ (e2s e) ^ " is non-positive: " ^ n#toString in
       Some (deps,msg)
    | _ -> None
         
  method private inv_implies_non_negative e inv =
    match inv#upper_bound_xpr with
    | Some (XConst (IntConst n)) when n#geq numerical_zero ->
       let deps = DLocal [ inv#index ] in
       let msg = "value of " ^ (e2s e) ^ " is non-negative: " ^ n#toString in
       Some (deps,msg)
    | _ -> None

  method private mk_safe_constraint (x1:xpr_t) (x2:xpr_t) =
    let xresult = XOp (XMinus, [ x1 ; x2 ]) in
    XOp (XLe, [ xresult ; xsafeub ])

  method private mk_violation_constraint (x1:xpr_t) (x2:xpr_t) =
    let xresult = XOp (XMinus, [ x1 ; x2 ]) in
    XOp (XGt, [ xresult ; xsafeub ])

  method private get_predicate e1 e2 =
    if unsigned then
      PUIntOverflow (MinusA, e1, e2, k)
    else
      PIntOverflow (MinusA, e1, e2, k)
    
  (* ----------------------------- safe ------------------------------------- *)

  method private inv_implies_safe inv1 inv2 =
    match (inv1#upper_bound_xpr, inv2#lower_bound_xpr) with
    | (Some x1, Some x2) ->
       let safeconstraint = self#mk_safe_constraint x1 x2 in
       let simconstraint = simplify_xpr safeconstraint in
       let _ = poq#set_diagnostic_arg 2 ("UB: " ^ (x2s x1) ^ (self#global_str x1)) in
       let _ = poq#set_diagnostic_arg 3 ("LB: " ^ (x2s x2) ^ (self#global_str x2)) in
       if is_true simconstraint then
         let deps = DLocal [ inv1#index ; inv2#index ] in
         let msg = "result of subtraction satisfies constraint " ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         let xresult = XOp  (XMinus, [ x1 ; x2 ]) in
         begin
           match simplify_xpr xresult with
           | XVar v when poq#env#is_fixed_value v ->
              let deps = DLocal  [ inv1#index ; inv2#index ] in
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
                        let msg = "safety constraint "  ^ (x2s safeconstraint)
                                  ^ " implied by global assumption: "
                                  ^  (p2s (po_predicate_to_pretty pred)) in
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
       let _ = poq#set_diagnostic_arg 2 ("UB: " ^ (x2s x1) ^ (self#global_str x1)) in
       self#inv_implies_non_positive e1 inv1
    | (_, Some x2) ->
       let _ = poq#set_diagnostic_arg 3 ("LB: " ^ (x2s x2) ^  (self#global_str x2)) in
       self#inv_implies_non_negative e2 inv2
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
                  match self#inv_implies_non_negative e2 inv with
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
                match self#inv_implies_non_positive e1 inv with
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
    match (inv1#lower_bound_xpr, inv2#upper_bound_xpr) with
    | (Some x1, Some x2) ->
       let safeconstraint =  self#mk_safe_constraint x1 x2 in
       let violationconstraint = self#mk_violation_constraint x1 x2 in
       let simconstraint = simplify_xpr violationconstraint in
       if is_true simconstraint then
         let deps = DLocal [ inv1#index ; inv2#index ]  in
         let msg  = "LB on result of subtraction violates condition "
                    ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         None
    | _ -> None

  method private existential_violation inv1 inv2 =
    match (get_existential_max_values poq inv1, get_existential_min_values poq inv2)  with
    | ([],_) | (_,[]) -> None
    | (vl1,vl2) ->
       List.fold_left  (fun acc1 (b1,deps1,msg1) ->
           match acc1 with
           | Some _ -> acc1
           | _ ->
              List.fold_left (fun acc2 (b2,deps2,msg2) ->
                  match acc2 with
                  | Some _ -> acc2
                  | _ ->
                     if (b1#sub b2)#gt safeub then
                       let deps = join_dependencies deps1 deps2 in
                       let msg = "result of subtraction: "
                                 ^ (b1#sub b2)#toString
                                 ^ " violates safe  UB: " ^ safeub#toString
                                 ^ " (" ^ msg1  ^ ";  " ^ msg2 ^  ")" in
                       Some (deps,msg)
                     else
                       None) acc1 vl1) None vl2
             
  method check_violation =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
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
         | (Some a1, Some a2) ->
            let pred = self#get_predicate a1 a2 in
            let deps = DEnvC ([ inv1#index ; inv2#index ],[ ApiAssumption pred ]) in
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
                   | Some  (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg ;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1
end


class div_checker
        ?(unsigned=false)
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

class generic_checker
        ?(unsigned=false)
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

let check_int_overflow
      ?(unsigned=false)
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
    | PlusA -> new plus_checker ~unsigned poq e1 e2 values2 values3 k
    | Mult -> new mult_checker ~unsigned poq e1 e2 values2 values3 k
    | MinusA -> new minus_checker ~unsigned poq e1 e2 values2 values3 k
    | Div -> new div_checker ~unsigned poq e1 e2 values2 values3 k
    | _ -> new generic_checker ~unsigned poq e1 e2 values2 values3 k in
  checker#check_safe || checker#check_violation || checker#check_delegation


let check_signed_int_overflow
      (poq:po_query_int)
      (op:binop)
      (e1:exp)
      (e2:exp)
      (k:ikind) = check_int_overflow ~unsigned:false poq op e1 e2 k
                
let check_unsigned_int_overflow
      (poq:po_query_int)
      (op:binop)
      (e1:exp)
      (e2:exp)
      (k:ikind) = check_int_overflow ~unsigned:true poq op e1 e2 k

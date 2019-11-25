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
open XprUtil
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil

(* cchpre *)
open CCHPOPredicate
open CCHPreTypes
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2p   = exp_to_pretty
let e2s e = p2s (e2p e)

class value_constraint_checker_t
        (poq:po_query_int)
        (e:exp)
        (invs:invariant_int list) =
object (self)

  method private mk_safe_constraint op x1 x2 = XOp (binop_to_xop op, [ x1 ; x2 ])
                                             
  method private mk_violation_constraint op x1 x2 =
    let xop = binop_to_xop (reverse_relational_operator op) in
    XOp (xop, [ x1 ; x2 ])
    
  (* ----------------------------- safe ------------------------------------- *)

  method private inv_vc_safe op vinfo n =
    let values = poq#get_vinfo_offset_values vinfo in
    let _ = poq#set_vinfo_diagnostic_invariants vinfo in
    let r =
      List.fold_left (fun acc (inv,offset) ->
          match acc with
          | Some _ -> acc
          | _ ->
             match offset with
             | NoOffset ->
                begin
                  match op with
                  | Le | Lt ->
                     begin
                       match inv#upper_bound_xpr with
                       | Some x -> self#xpr_safe op [ inv#index ] x (num_constant_expr n)
                       | _ -> None
                     end
                  | Ge | Gt ->
                     begin
                       match inv#lower_bound_xpr with
                       | Some x -> self#xpr_safe op [ inv#index ] x (num_constant_expr n)
                       | _ -> None
                     end
                  | Eq | Ne ->
                     begin
                       match inv#expr with
                       | Some x -> self#xpr_safe op [ inv#index ] x (num_constant_expr n)
                       | _ -> None
                     end
                  | _ -> None
                end
             | _ -> None) None values in
    r

  method private xpr_safe op invindices x1 x2 =
    let xconstraint = self#mk_safe_constraint op x1 x2 in
    let sconstraint = simplify_xpr xconstraint in
    if is_true sconstraint then
      let deps = DLocal invindices in
      let msg =
        "values: " ^ (x2s x1) ^ " and: " ^ (x2s x2)
        ^ " satisfy constraint: " ^  (x2s xconstraint) in
      Some (deps,msg)
    else
      begin
        poq#set_diagnostic
          ("remaining constraint: " ^ (x2s sconstraint)) ;
        None
      end    

  method private inv_vv_safe op vinfo1 vinfo2 =
    let v1values = poq#get_vinfo_offset_values vinfo1 in
    let v2values = poq#get_vinfo_offset_values vinfo2 in
    let _ = poq#set_vinfo_diagnostic_invariants vinfo1 in
    let _ = poq#set_vinfo_diagnostic_invariants vinfo2 in
    List.fold_left (fun acc1 (inv1,offset1) ->
        match acc1 with
        | Some _ -> acc1
        | _ ->
           List.fold_left (fun acc2 (inv2,offset2)  ->
               match  (inv1#expr, inv2#expr) with
               | (Some x1, Some x2) ->
                  self#xpr_safe op [ inv1#index ; inv2#index ] x1 x2
               | _ -> None) acc1 v2values) None v1values

  method private inv_vcc_safe op1 op2 vinfo c1 c2 =
    let vvalues = poq#get_vinfo_offset_values vinfo in
    let _ = poq#set_vinfo_diagnostic_invariants vinfo in
    List.fold_left (fun acc (inv,offset) ->
        match acc with
        | Some _ -> acc
        | _ ->
           match inv#expr with
           | Some x ->
              let xpr = XOp (op2, [ x ; XConst (IntConst c1) ])  in
              self#xpr_safe op1 [ inv#index ] xpr (XConst (IntConst c2))
           | _ -> None) None vvalues
    
  method check_safe =
    match e with
    | BinOp (op, Lval (Var (vname,vid),NoOffset), Const (CInt64 (i64,_,_)),_) when vid > 0 ->
       let vinfo = poq#env#get_varinfo vid in
       let _ = poq#set_vinfo_diagnostic_invariants vinfo in
       begin
         match self#inv_vc_safe op vinfo (mkNumericalFromInt64 i64) with
         | Some (deps,msg) ->
            begin
              poq#record_safe_result deps msg ;
              true
            end
         | _ -> false
       end
    | BinOp (op1, BinOp (op2,Lval (Var (vname,vid),NoOffset),Const (CInt64 (i64_1,_,_)),_),
             Const (CInt64 (i64_2,_,_)),_) when vid > 0 ->
       let vinfo = poq#env#get_varinfo vid in
       let _ = poq#set_vinfo_diagnostic_invariants vinfo in       
       begin
         match self#inv_vcc_safe
                 op1 (binop_to_xop op2) vinfo
                 (mkNumericalFromInt64 i64_1)  (mkNumericalFromInt64 i64_2) with
         | Some (deps,msg) ->
            begin
              poq#record_safe_result deps msg ;
              true
            end
         | _ -> false
       end
    | BinOp (op, Lval (Var (vname1,vid1),NoOffset), Lval (Var (vname2,vid2),NoOffset), typ)
         when vid1 > 0 && vid2 > 0->
       let vinfo1 = poq#env#get_varinfo vid1 in
       let vinfo2 = poq#env#get_varinfo vid2 in
       let _ = poq#set_vinfo_diagnostic_invariants vinfo1 in
       let _ = poq#set_vinfo_diagnostic_invariants vinfo2 in       
       begin
         match self#inv_vv_safe op vinfo1 vinfo2 with
         | Some (deps,msg) ->
            begin
              poq#record_safe_result deps msg ;
              true
            end
         | _ -> false
       end
    | _ -> false
             
       
  (* ----------------------- violation -------------------------------------- *)

  method private xpr_implies_violation invindices op x1 x2 =
    let safeconstraint = self#mk_safe_constraint op x1 x2 in
    let vconstraint = self#mk_violation_constraint op x1 x2 in
    let sconstraint = simplify_xpr vconstraint in
    if is_true sconstraint then
      let deps = DLocal invindices in
      let msg = "values " ^  (x2s x1)  ^  " and: " ^ (x2s x2)
                ^ " violate constraint: " ^  (x2s safeconstraint) in
      Some (deps,msg)
    else
      match x1 with
      | XVar v when poq#env#is_tainted_value v && not (occurs_check v x2) ->
         begin
           match poq#get_witness vconstraint v with
           | Some violationvalue ->
              let (s,callee,pc) = poq#get_tainted_value_origin v in
              let deps = DEnvC (invindices,[ PostAssumption (callee.vid,pc) ]) in
              let msg =
                s ^ " choose value: " ^ (x2s violationvalue)
                ^ " to violate the safety constraint: "
                ^ (x2s safeconstraint) in
              Some (deps,msg)
           | _ -> None
         end
      | _ ->
         match x1 with
         | XOp (_, [ XVar v ; xx1 ])
              when poq#env#is_tainted_value v && not (occurs_check v xx1)
                   && not (occurs_check v x2) ->
            begin
              match poq#get_witness vconstraint v with
              | Some violationvalue ->
                 let (s,callee,pc) = poq#get_tainted_value_origin v in
                 let deps = DEnvC (invindices,[ PostAssumption (callee.vid,pc) ]) in
                 let msg =
                   s ^ " choose value: " ^ (x2s violationvalue)
                   ^ " to violate the safety constraint: "
                   ^ (x2s safeconstraint) in
                 Some (deps,msg)
              | _ -> None
            end
         | _ ->                           
            match x2 with
            | XVar v when poq#env#is_tainted_value v && not (occurs_check v x1) ->
               begin
                 match poq#get_witness vconstraint v with
                 | Some violationvalue ->
                    let (s,callee,pc) = poq#get_tainted_value_origin v in
                    let deps = DEnvC (invindices,[ PostAssumption (callee.vid,pc) ]) in
                    let msg =
                      s ^ " choose value: " ^ (x2s violationvalue)
                      ^ " to violate the safety constraint: "
                      ^ (x2s safeconstraint) in
                    Some (deps,msg)
                 | _ -> None
               end
            | _ -> None
                 
  method  private xpr_list_implies_violation invindices op ll xn =
    List.fold_left (fun acc x ->
        match acc with
        | Some _ -> acc
        | _ -> self#xpr_implies_violation invindices op x xn) None ll

  method private inv_vc_violation op vinfo n =
    let values = poq#get_vinfo_offset_values vinfo in
    let xn = num_constant_expr n in
    List.fold_left (fun acc (inv,offset) ->
        match acc with
        | Some _ -> acc
        | _ ->
           match offset with
           | NoOffset ->
              begin
                match inv#expr with
                | Some x ->
                   begin
                     match self#xpr_implies_violation [ inv#index ] op x xn with
                     | Some r -> Some  r
                     | _ ->
                        match inv#lower_bound_xpr_alternatives with
                        | Some [] -> None
                        | Some ll ->
                           begin
                             match self#xpr_list_implies_violation [ inv#index ] op ll xn with
                             | Some r -> Some r
                             | _ ->
                                match inv#upper_bound_xpr_alternatives with
                                | Some [] -> None
                                | Some lu ->
                                   begin
                                     match self#xpr_list_implies_violation [ inv#index ] op lu xn with
                                     | Some r -> Some r
                                     | _ -> None
                                   end
                                | _ -> None
                           end
                        | _ -> None
                   end
                | _ ->
                   match inv#lower_bound_xpr with
                   | None -> None
                   | Some x ->
                      match self#xpr_implies_violation [ inv#index ] op x xn with
                      | Some r -> Some r
                      | _ ->
                         match inv#lower_bound_xpr_alternatives with
                         | Some [] -> None
                         | Some ll ->
                            begin
                              match self#xpr_list_implies_violation [ inv#index ] op ll xn with
                              | Some r -> Some r
                              | _ ->
                                 match inv#upper_bound_xpr_alternatives with
                                 | Some [] -> None
                                 | Some lu ->
                                    begin
                                      match self#xpr_list_implies_violation [ inv#index ] op lu xn with
                                      | Some r -> Some r
                                      | _ -> None
                                    end
                                 | _ -> None
                            end
                         | _ -> None
              end
           | _ -> None) None values

  method private inv_vcc_violation op1 op2 vinfo c1 c2 =
    let vvalues = poq#get_vinfo_offset_values vinfo in
    List.fold_left  (fun acc (inv,offset) ->
        match acc with
        | Some _ ->  acc
        | _ ->
           match inv#expr with
           | Some x ->
              let xpr  = XOp (op2, [ x ; XConst (IntConst c1) ])  in
              self#xpr_implies_violation [ inv#index ] op1 xpr (XConst (IntConst c2))
           | _ -> None) None vvalues

  method private inv_cvc_violation op1 op2 vinfo c1 c2 =
    let vvalues = poq#get_vinfo_offset_values vinfo in
    List.fold_left (fun acc (inv,offset) ->
        match acc with
        | Some _ -> acc
        | _ ->
           match inv#expr with
           | Some x ->
              let xpr = XOp (op2, [ XConst (IntConst c1) ; x ]) in
              self#xpr_implies_violation [ inv#index ] op1 xpr (XConst (IntConst c2))
           | _ -> None) None vvalues
    
  method private inv_vv_violation op vinfo1 vinfo2 =
    let v1values = poq#get_vinfo_offset_values vinfo1 in
    let v2values = poq#get_vinfo_offset_values vinfo2 in
    List.fold_left (fun acc1 (inv1,offset1) ->
        match acc1 with
        | Some  _ -> acc1
        | _ ->
           match offset1 with
           | NoOffset ->
              List.fold_left (fun acc2 (inv2,offset2) ->
                  match acc2 with
                  | Some _ -> acc2
                  | _ ->
                     match offset2 with
                     | NoOffset ->
                        begin
                          match (inv1#expr,inv2#expr) with
                          | (Some x1, Some x2) ->
                             begin
                               match self#xpr_implies_violation [ inv1#index ; inv2#index ] op x1 x2 with
                               | Some r -> Some r
                               |  _ -> None
                             end
                          | _ -> None
                        end
                     | _ -> None) acc1 v2values
           | _ -> None) None v1values
  
  method check_violation =
    match e with
    | BinOp (op, Lval (Var (vname,vid),NoOffset), Const (CInt64 (i64,_,_)),_) when vid > 0 ->
       let vinfo = poq#env#get_varinfo vid in
       begin
         match self#inv_vc_violation op vinfo (mkNumericalFromInt64 i64) with
         | Some (deps,msg) ->
            begin
              poq#record_violation_result deps msg ;
              true
            end
         | _ -> false
       end
    | BinOp (op1, BinOp (op2,Lval (Var (vname,vid),NoOffset),Const (CInt64 (i64_1,_,_)),_),
             Const (CInt64 (i64_2,_,_)),_) when vid > 0 ->
       let vinfo = poq#env#get_varinfo vid in
       begin
         match self#inv_vcc_violation
                 op1 (binop_to_xop op2) vinfo
                 (mkNumericalFromInt64 i64_1)  (mkNumericalFromInt64 i64_2) with
         | Some (deps,msg) ->
            begin
              poq#record_violation_result deps msg ;
              true
            end
         | _ -> false
       end
    | BinOp (op1, BinOp (op2,Const (CInt64 (i64_1,_,_)),Lval (Var (vname,vid),NoOffset),_),
             Const (CInt64 (i64_2,_,_)),_) when vid > 0 ->
       let vinfo = poq#env#get_varinfo vid in
       begin
         match self#inv_cvc_violation
                 op1 (binop_to_xop op2) vinfo
                 (mkNumericalFromInt64 i64_1)  (mkNumericalFromInt64 i64_2) with
         | Some (deps,msg) ->
            begin
              poq#record_violation_result deps msg ;
              true
            end
         | _ -> false
       end
    | BinOp (op, Lval (Var (vname1,vid1),NoOffset), Lval (Var (vname2,vid2),NoOffset), typ)
         when vid1 > 0 && vid2 > 0 ->
       let vinfo1 = poq#env#get_varinfo vid1 in
       let vinfo2 = poq#env#get_varinfo vid2 in
       begin
         match self#inv_vv_violation op vinfo1 vinfo2 with
         | Some (deps,msg) ->
             begin
               poq#record_violation_result deps msg ;
               true
             end
         | _  -> false
       end
    | _ -> false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation =
    match e with
    | BinOp (op, e1, Const (CInt64 (i64,ik,txt)),t) ->
       let invs = poq#get_exp_invariants e1 in
       List.fold_left (fun acc inv ->
           acc ||
             match inv#expr with
             | Some x when poq#is_api_expression x ->
                let a = poq#get_api_expression x in
                let c = BinOp (op,a,Const (CInt64 (i64,ik,txt)),t) in
                let pred = PValueConstraint c in
                let deps = DEnvC ([ inv#index ],[ ApiAssumption pred ])  in
                let msg = "constraint " ^ (e2s e) ^ " delegated to the api" in
                begin
                  poq#record_safe_result deps msg ;
                  true
                end
             | _ -> false) false invs
    | _ -> false
end


let check_value_constraint (poq:po_query_int) (e:exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new value_constraint_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

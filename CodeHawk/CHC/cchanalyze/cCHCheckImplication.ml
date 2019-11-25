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

(** Check if a proof obligation is implied by assumptions *)

(* chlib *)
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify
open Xconsequence

(* cchlib *)
open CCHBasicTypes
open CCHFileEnvironment
open CCHLibTypes
open CCHExternalPredicate
open CCHPOPredicate
open CCHTypesCompare
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr

let get_formal_parameter (env:c_environment_int) (i:int) =
  let vinfo = env#get_fdecls#get_formal i in
  try
    Some (XVar (env#mk_program_var vinfo  NoOffset NUM_VAR_TYPE))
  with _ ->
    None

let get_global_variable (env:c_environment_int) (name:string) =
  let vinfo = file_environment#get_globalvar_by_name name in
  try
    Some (XVar (env#mk_program_var vinfo NoOffset NUM_VAR_TYPE))
  with _ ->
    None

let rec s_term_to_xpr (env:c_environment_int) (t:s_term_t) =
  match t with
  | ArgValue (ParFormal i,ArgNoOffset) -> get_formal_parameter env i
  | ArgValue (ParGlobal s,ArgNoOffset) -> get_global_variable env s
  | NumConstant i -> Some (num_constant_expr i)
  | ArithmeticExpr (op, t1, t2) ->
     begin
       match (s_term_to_xpr env t1, s_term_to_xpr env t2) with
       | (Some xt1, Some xt2) -> Some (XOp (binop_to_xop op, [ xt1 ; xt2 ]))
       | _ -> None
     end
  | _ -> None


(* Use Farkas Lemma to discharge:
   consequence is implied if there exists non-negative c such that
   consequence - c * antecedent <= 0 is valid *)
let ximplies (env:c_environment_int) (a:xpredicate_t)  (p:xpredicate_t) =
  let one = NumConstant numerical_one in
  let antecedent =
    match a with
    | XRelationalExpr (Lt, a1, a2) ->
       ArithmeticExpr (PlusA, ArithmeticExpr (MinusA, a1, a2),one)
    | XRelationalExpr (Le, a1, a2) ->
       ArithmeticExpr (MinusA, a1, a2)
    | XRelationalExpr (Ge, a1, a2) ->
       ArithmeticExpr (MinusA, a2, a1)
    | XRelationalExpr (Gt, a1, a2) ->
       ArithmeticExpr (PlusA, ArithmeticExpr (MinusA, a2, a1),one)
    | _ -> RuntimeValue in
  let consequence =
    match p with
    | XRelationalExpr (Lt, a1, a2) ->
       ArithmeticExpr (PlusA, ArithmeticExpr (MinusA, a1, a2),one)
    | XRelationalExpr (Le, a1, a2) ->
       ArithmeticExpr (MinusA, a1, a2)
    | XRelationalExpr (Ge, a1, a2) ->
       ArithmeticExpr (MinusA, a2, a1)
    | XRelationalExpr (Gt, a1, a2) ->
       ArithmeticExpr (PlusA, ArithmeticExpr (MinusA, a2, a1),one)
    | _ -> RuntimeValue in
  match (s_term_to_xpr env antecedent, s_term_to_xpr env consequence) with
  | (Some xa, Some xc) ->
     let result = xfimplies xa xc in
     let _ = if result then () else
               chlog#add "farkas lemma implication failed"
                         (LBLOCK [ x2p xa ; STR " ==> " ; x2p xc ]) in
     result
  | _ ->
     begin
       chlog#add "translation to xpr failed"
                 (LBLOCK [ STR "a: " ; xpredicate_to_pretty a ;
                           STR "; antecedent: " ; s_term_to_pretty antecedent ;
                           STR "; p: " ; xpredicate_to_pretty p ;
                           STR "; consequence: " ; s_term_to_pretty consequence ]);
       false
     end

let implies_upper_bound (a:po_predicate_t) (e:exp) (ub:int) =
  match a with
  | PValueConstraint (BinOp (Lt, ae, Const (CInt64 (j64,_,_)),_))
       when (exp_compare e ae) = 0 ->
     (Int64.to_int j64) <= ub
  | _ -> false

let implies (env:c_environment_int) (a:po_predicate_t) (p:po_predicate_t) =
  match p with
  | PAllocationBase (Lval (Var (vname,vid),NoOffset)) ->
     begin
       match a with
       | PAllocationBase (Lval (Var (vname2,vid2),NoOffset)) when vid = vid2 -> true
       | _ -> false
     end
  | PNotNull (Lval (Var (vname,vid),NoOffset)) ->
     begin
       match a with
       | PNotNull (Lval (Var (vname2,vid2),NoOffset)) when vid = vid2 -> true
       | _ -> false
     end
  | PValidMem (Lval (Var (vname,vid),NoOffset)) ->
     begin
       match a with
       | PValidMem (Lval (Var (vname2,vid2),NoOffset)) when vid = vid2 -> true
       | _ -> false
     end
  | PInitialized (Mem (Lval (Var (vname,vid),NoOffset)),NoOffset) ->
     begin
       match a with
       | PInitialized (Mem (Lval (Var (vname2,vid2),NoOffset)),NoOffset) when vid2 = vid -> true
       | _ -> false
     end
  | PInitialized (Mem (Lval (Var (vname,vid),NoOffset)),Field ((fname,_),NoOffset)) ->
     begin
       match a with
       | PInitialized (Mem (Lval (Var (vname2,vid2),NoOffset)),Field ((fname2,_),NoOffset))
            when vid2 = vid && fname2 = fname -> true
       | _ -> false
     end
  | _ ->
     try
       let xassumption = po_predicate_to_xpredicate env#get_fdecls a in
       let xpredicate = po_predicate_to_xpredicate env#get_fdecls p in
       ximplies env xassumption xpredicate
     with
     | CCHFailure e ->
        begin
          ch_error_log#add
            "check-implication"
            (LBLOCK [ STR "Error in converting assumption: " ;
                      po_predicate_to_pretty a ;
                      STR " or candidate consequence: " ;
                      po_predicate_to_pretty p ;
                      STR ": " ;  e ]) ;
          false
        end

let check_implied_by_assumptions
      (env:c_environment_int) (assumptions:po_predicate_t list) (p:po_predicate_t) =
  List.fold_left (fun result a ->
      match result with
      | Some _ -> result
      | _ -> if implies env a p then Some a else None) None assumptions

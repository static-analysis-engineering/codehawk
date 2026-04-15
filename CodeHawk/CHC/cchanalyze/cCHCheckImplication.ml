(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2026 Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHTraceResult

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xconsequence

(* cchlib *)
open CCHBasicTypes
open CCHFileEnvironment
open CCHLibTypes
open CCHExternalPredicate
open CCHPOPredicate
open CCHTypesCompare
open CCHTypesUtil

(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes


let (let*) x f = CHTraceResult.tbind f x


let x2p = xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)

let eloc (line: int): string = __FILE__ ^ ":" ^ (string_of_int line)
let elocm (line: int): string = (eloc line) ^ ": "


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


let rec s_term_to_xpr
          (env: c_environment_int) (t: s_term_t): xpr_t option =
  match t with
  | ArgValue (ParFormal i, ArgNoOffset) -> get_formal_parameter env i
  | ArgValue (ParGlobal s, ArgNoOffset) -> get_global_variable env s
  | NumConstant i -> Some (num_constant_expr i)
  | ArithmeticExpr (op, t1, t2) ->
     begin
       match (s_term_to_xpr env t1, s_term_to_xpr env t2) with
       | (Some xt1, Some xt2) -> Some (XOp (binop_to_xop op, [xt1; xt2]))
       | _ -> None
     end
  | _ -> None


(* Use Farkas Lemma to discharge:
   consequence is implied if there exists non-negative c such that
   consequence - c * antecedent <= 0 is valid *)
let ximplies
      (env: c_environment_int)
      (a: xpredicate_t)
      (p: xpredicate_t): bool traceresult =
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
  let consequent =
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
  match (s_term_to_xpr env antecedent, s_term_to_xpr env consequent) with
  | (Some xa, Some xc) ->
     let result = xfimplies xa xc in
     let _ =
       if result then
         ()
       else
         log_diagnostics_result
           ~tag:"ximplies"
           ~msg:env#get_functionname
           __FILE__ __LINE__
           ["Farkas Lemma implication failed: "
            ^ (x2s xa) ^ " ==> " ^ (x2s xc)] in
     Ok result
  | _ ->
     Error [
         (elocm __LINE__) ^ "ximplies";
         env#get_functionname;
         "Unable to convert antecedent and/or consequent";
         "a: " ^ (p2s (xpredicate_to_pretty a));
         "antecedent: " ^ (p2s (s_term_to_pretty antecedent));
         "p: " ^ (p2s (xpredicate_to_pretty p));
         "consequent: " ^ (p2s (s_term_to_pretty consequent))]


let _implies_upper_bound (a:po_predicate_t) (e:exp) (ub:int) =
  match a with
  | PValueConstraint (BinOp (Lt, ae, Const (CInt (j64, _, _)),_))
       when (exp_compare e ae) = 0 ->
     (Int64.to_int j64) <= ub
  | _ -> false


let implies
      (env: c_environment_int)
      (a: po_predicate_t)
      (p: po_predicate_t): bool traceresult =
  match p with
  | PAllocationBase (Lval (Var (_vname, vid), NoOffset)) ->
     begin
       match a with
       | PAllocationBase (Lval (Var (_vname2, vid2), NoOffset)) when vid = vid2 ->
          Ok true
       | _ -> Ok false
     end
  | PNotNull (Lval (Var (_vname, vid), NoOffset)) ->
     begin
       match a with
       | PNotNull (Lval (Var (_vname2, vid2), NoOffset)) when vid = vid2 -> Ok true
       | _ -> Ok false
     end
  | PValidMem (Lval (Var (_vname, vid), NoOffset)) ->
     begin
       match a with
       | PValidMem (Lval (Var (_vname2, vid2), NoOffset)) when vid = vid2 -> Ok true
       | _ -> Ok false
     end
  | PInitialized (Mem (Lval (Var (_vname, vid), NoOffset)), NoOffset) ->
     begin
       match a with
       | PInitialized (Mem (Lval (Var (_vname2,vid2), NoOffset)), NoOffset)
            when vid2 = vid ->  Ok true
       | _ ->Ok false
     end
  | PInitialized (Mem (Lval (Var (_, vid), NoOffset)),
                  Field ((fname,_), NoOffset)) ->
     begin
       match a with
       | PInitialized (Mem (Lval (Var (_, vid2), NoOffset)),
                       Field ((fname2,_), NoOffset))
            when vid2 = vid && fname2 = fname -> Ok true
       | _ -> Ok false
     end
  | _ ->
     let* xassumption = po_predicate_to_xpredicate env#get_fdecls a in
     let* xpredicate = po_predicate_to_xpredicate env#get_fdecls p in
     ximplies env xassumption xpredicate


let check_implied_by_assumptions
      (env: c_environment_int)
      (assumptions: po_predicate_t list)
      (p: po_predicate_t): po_predicate_t option =
  List.fold_left (fun result a ->
      match result with
      | Some _ -> result
      | _ ->
         match implies env a p with
         | Ok true -> Some a
         | Ok false -> None
         | Error e ->
            begin
              log_diagnostics_result
                ~tag:"check_implied_by_assumptions"
                ~msg:env#get_functionname
                __FILE__ __LINE__
                ["Error in checking assumption: "
                 ^ (p2s (po_predicate_to_pretty a));
                 (String.concat "; " e)];
              None
            end) None assumptions

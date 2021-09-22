(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHPretty
open CHLanguage
open CHNumerical
open CHNumericalConstraints

(* chutil *)
open CHUtil

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open XprUtil
open Xsimplify


class rewrite_rule_t
    (lhs:variable_t)
    (rhs:xpr_t) =
object

  val lhs = lhs
  val rhs = rhs

  method getRhsVars = variables_in_expr rhs

  method isApplicable (expr:xpr_t) =
    let rec aux x =
      match x with
	XVar v -> v#equal lhs
      | XOp (_, xl) -> List.exists aux xl
      | XAttr (_, s) -> aux s
      | _ -> false in
    aux expr

  method isConstant = match rhs with XConst _ -> true | _ -> false

  method rewrite (expr:xpr_t):xpr_t = 
    substitute_expr (fun v -> if v#equal lhs then rhs else XVar v) expr

  method toExpr = XOp (XEq, [XVar lhs; rhs])

  method toPretty =
    LBLOCK [lhs#toPretty; STR " ==> "; xpr_printer#pr_expr rhs]

end

(* variable comparator is used to rank the variables to be rewritten; the variable
   with highest rank gets rewritten. I.e. the objective is to minimize the total
   rank of the expression. E.g. with constraint x + y + z = 0 and x < y < z the
   expression z gets rewritten by -(x+y), but x or y do not get rewritten, as the
   resulting expression would involve variables with higher rank *)

let constraint_to_rule 
    (konstraint:numerical_constraint_t)
    (variable_comparator: variable_t -> variable_t -> int):rewrite_rule_t =
  let _ = konstraint#normalize () in
  let fcompare (f1,_) (f2,_) =
    variable_comparator f1#getVariable f2#getVariable in
  let factors = konstraint#getFactorsTable#listOfPairs in
  let (lhsfactor,lhscoeff) = list_maxf factors fcompare in
  let rhsfactors =
    List.filter (fun (f,_) -> not (f#equal lhsfactor)) factors in
  let konstant = konstraint#getConstant in
  let lhs = lhsfactor#getVariable in
  let rhs = 
    let (multiplier,rhsfactors,konstant) = 
      if lhscoeff#equal numerical_one then
	(None, List.map (fun (f,c) -> (f,c#neg)) rhsfactors,konstant)
      else if lhscoeff#equal numerical_one#neg then
	(None, rhsfactors,konstant#neg)
      else if lhscoeff#gt numerical_one then
	(Some (num_constant_expr lhscoeff),
         List.map (fun (f,c) -> (f,c#neg)) rhsfactors, konstant)
      else
	(Some (num_constant_expr lhscoeff#neg), rhsfactors, konstant#neg) in
    let rhs_expr = 
      List.fold_right
	(fun (f,c) a -> 
	  let term = XOp (XMult, [num_constant_expr c; XVar f#getVariable]) in
	  XOp (XPlus, [a; term])) rhsfactors (num_constant_expr konstant) in
    match multiplier with
      Some m -> XOp (XDiv, [rhs_expr; m])
    | _ -> rhs_expr in
  let rule = new rewrite_rule_t lhs rhs in
  begin
    (* pr_debug [ STR "rule: " ; rule#toPretty ; NL ] ; *)
    rule
  end

let compare_rules 
    (r1:rewrite_rule_t) 
    (r2:rewrite_rule_t) 
    (variable_comparator: variable_t -> variable_t -> int): int =
  let s1 = r1#getRhsVars in
  let s2 = r2#getRhsVars in
  let len1 = List.length s1 in
  let len2 = List.length s2 in
  if len1 < len2 then
    1
  else if len2 < len1 then
    -1
  else list_compare s1 s2 variable_comparator

let rewrite 
    (constraint_list:numerical_constraint_t list) 
    (expr:xpr_t) 
    (variable_comparator: variable_t -> variable_t -> int):(xpr_t * xpr_t list) =
  let rules =
    List.map (fun c ->
        constraint_to_rule c variable_comparator) constraint_list in
  let rec rew x evidence =
    let applicable_rules = List.filter (fun r -> r#isApplicable x) rules in
    match applicable_rules with
    | [] -> (x, evidence)
    | _ ->
       let rule =
         list_maxf
           applicable_rules
           (fun r1 r2 -> compare_rules r1 r2 variable_comparator) in
       rew (rule#rewrite x) (rule#toExpr :: evidence) in
  let (result,evidence) = rew expr [] in
  let (_,result) = simplify_expr result in
  (result, evidence)

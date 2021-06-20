(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs LLC

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
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open XprUtil
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFloc
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant
open BCHVariable

(* bchlibarm32 *)
open BCHARMAssemblyInstruction
open BCHARMTypes
open BCHARMOperand
open BCHARMOpcodeRecords

let x2p = xpr_formatter#pr_expr

let freeze_variables
      ?(unsigned=false)
      (add:variable_t -> variable_t -> unit) 
      (testloc:location_int)
      (jumploc:location_int)
      (op:arm_operand_int)  =
  let testfloc = get_floc testloc in
  let jumpfloc = get_floc jumploc in
  let env = testfloc#f#env in
  let opXpr = op#to_expr testfloc in
  let frozenVars = new VariableCollections.table_t in
  let vars = (variables_in_expr opXpr) in
  let varsKnown = ref true in
  let _ =
    List.iter (
        fun v -> 
        if v#isTmp then
          varsKnown := false
        else if env#is_local_variable v then
          if jumpfloc#inv#test_var_is_equal v testloc#ci jumploc#ci then
            ()
          else
            let fv =
              env#mk_frozen_test_value
                v testloc#ci jumploc#ci in frozenVars#set v fv
        else if env#is_unknown_memory_variable v then
          varsKnown := false) vars in
  let subst v =
    if frozenVars#has v then
      XVar (Option.get (frozenVars#get v))
    else
      XVar v in
  if !varsKnown then
    begin
      List.iter (fun (v, fv) -> add v fv) frozenVars#listOfPairs ;
      substitute_expr subst opXpr
    end
  else
    random_constant_expr


let cc_expr v vu testfloc testopc cc =
  let found = ref true in
  let iszero op =
    match testfloc#inv#rewrite_expr (op#to_expr testfloc) testfloc#env#get_variable_comparator with
    | XConst (IntConst n) -> n#equal numerical_zero
    | _ -> false in
  let gezero op =
    match testfloc#inv#rewrite_expr (op#to_expr testfloc) testfloc#env#get_variable_comparator with
    | XConst (IntConst n) -> n#gt numerical_zero
    | _ -> false in
  let expr = 
    match (testopc, cc) with
    | (Compare (ACCAlways, x, y, _), ACCEqual) -> XOp (XEq, [v x; v y])
    | (Compare (ACCAlways, x, y, _), ACCNotEqual) -> XOp (XNe, [v x; v y])
    | (Compare (ACCAlways, x, y, _), ACCSignedLE) when iszero x && iszero y ->
       true_constant_expr
    | (Compare (ACCAlways, x, y, _), ACCSignedLE) when gezero x && iszero y ->
       XOp (XGe, [v x;  int_constant_expr e31])
    | (Compare (ACCAlways, x, y, _), ACCSignedLE) when iszero y ->
       XOp (XLOr, [XOp (XEq, [v x; zero_constant_expr]); XOp (XGe, [v x; int_constant_expr e31])])
    | _ -> begin found := false; random_constant_expr end in
  let expr = simplify_xpr expr in
  if is_random expr then (!found, None) else (true, Some expr)


let arm_conditional_jump_expr
    ~(jumpopc:arm_opcode_t)
    ~(testopc:arm_opcode_t)
    ~(jumploc:location_int)
    ~(testloc:location_int) =
  let frozenVars = new VariableCollections.table_t in
  let add v fv = frozenVars#set v fv in
  let v = freeze_variables add testloc jumploc in
  let vu = freeze_variables ~unsigned:true add testloc jumploc in
  let testfloc = get_floc testloc in
  let jumpfloc = get_floc jumploc in
  let (found,optTestExpr) =
    match jumpopc with
    | Branch (c, op, _) when is_cond_conditional c && op#is_absolute_address ->
       cc_expr v vu testfloc testopc c
    | IfThen (c, _) when is_cond_conditional c ->
       cc_expr v vu testfloc testopc c
    | _ -> (false, None) in
  if found then
    match optTestExpr with
    | Some expr ->
	if is_false expr then (frozenVars#listOfValues, None) else
	begin
	  jumpfloc#set_test_expr expr ;
	  testfloc#set_test_variables frozenVars#listOfPairs ;
	  (frozenVars#listOfValues, optTestExpr)
	end
    | _ -> (frozenVars#listOfValues, None)
  else
    begin
      chlog#add
        "unused condition"
        (LBLOCK [
             jumpfloc#l#toPretty;
             STR ": "; 
	     STR (arm_opcode_to_string jumpopc);
             STR " with "; 
	     STR (arm_opcode_to_string testopc)]);
      (frozenVars#listOfValues, None)
    end
      

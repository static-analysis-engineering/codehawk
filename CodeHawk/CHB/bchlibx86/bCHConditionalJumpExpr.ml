(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
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
open CHPretty
open CHLanguage
open CHUtils

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprTypes
open XprUtil
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHFloc
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHX86OpcodeRecords


(* =============================================================================
   The implementation of the conditions is partially based on Figure 3.3 from
   the PhD Thesis: WYSINWYX: What you see is not what you execute, by Gogul
   Balakrishnan, University of Wisconsin at Madison, 2007.
   =============================================================================
 *)

(* return an expression in which all local variables are frozen; if some
   variables are unknown return a random expr; report the frozen variables
   with add *)
let freeze_variables
      ?(unsigned=false)
      (add:variable_t -> variable_t -> unit)
      (testloc:location_int)
      (jumploc:location_int)
      (op:operand_int)  =
  let testfloc = get_floc testloc in
  let jumpfloc = get_floc jumploc in
  let env = testfloc#f#env in
  let opXpr = op#to_expr ~unsigned testfloc in
  let frozenVars = new VariableCollections.table_t in
  let vars = (variables_in_expr opXpr) in
  let varsKnown = ref true in
  let _ =
    List.iter (fun v ->
        if v#isTmp then
          varsKnown := false
        else
          if env#is_local_variable v then
            if jumpfloc#inv#test_var_is_equal v testloc#ci jumploc#ci then
              () else
              let fv = env#mk_frozen_test_value v testloc#ci jumploc#ci in
              frozenVars#set v fv
          else if env#is_unknown_memory_variable v then
            varsKnown := false) vars  in
  let subst v =
    if frozenVars#has v then XVar (Option.get (frozenVars#get v)) else XVar v in
  if !varsKnown then
    begin
      List.iter (fun (v, fv) -> add v fv) frozenVars#listOfPairs;
      substitute_expr subst opXpr
    end
  else
    random_constant_expr


let cc_expr v vu testopc cc =
  let found = ref true in
  let zero = zero_constant_expr in
  let one = one_constant_expr in
  let expr =
    match (testopc, cc) with
    | (Cmp (x, y), CcCarry)        ->  XOp (XLt, [v x; v y])
    | (Cmp (x, y), CcNotCarry)     ->  XOp (XGe, [v x; v y])
    | (Cmp (x, y), CcZero)         ->  XOp (XEq, [v x; v y])
    | (Cmp (x, y), CcNotZero)      ->  XOp (XNe, [v x; v y])
    | (Cmp (x, y), CcBelowEqual)   ->  XOp (XLe, [vu x; vu y])
    | (Cmp (x, y), CcAbove)        ->  XOp (XGt, [vu x; vu y])
    | (Cmp (x, y), CcLess)         ->  XOp (XLt, [v x; v y])
    | (Cmp (x, y), CcGreaterEqual) ->  XOp (XGe, [v x; v y])
    | (Cmp (x, y), CcLessEqual)    ->  XOp (XLe, [v x; v y])
    | (Cmp (x, y), CcGreater)      ->  XOp (XGt, [v x; v y])
    | (Cmp (x, y), CcSign)         ->  XOp (XLt, [v x; v y])
    | (Cmp (x, y), CcNotSign)      ->  XOp (XGe, [v x; v y])

    | (Decrement x, CcZero)         -> XOp (XEq, [v x; one])
    | (Decrement x, CcNotZero)      -> XOp (XNe, [v x; one])
    | (Decrement x, CcSign)         -> XOp (XLe, [v x; zero])
    | (Decrement x, CcNotSign)      -> XOp (XGt, [v x; zero])
    | (Decrement x, CcLess)         -> XOp (XLe, [v x; zero])
    | (Decrement x, CcGreaterEqual) -> XOp (XGt, [v x; zero])
    | (Decrement x, CcLessEqual)    -> XOp (XLe, [v x; one])
    | (Decrement x, CcGreater)      -> XOp (XGt, [v x; one])

    | (LogicalOr(x, y), CcZero)    when x#equal y -> XOp (XEq, [v x; zero])
    | (LogicalOr(x, y), CcNotZero) when x#equal y -> XOp (XNe, [v x; zero])

    | (LogicalOr(x, y), CcZero)    -> XOp (XLAnd, [XOp (XEq, [v x; zero]);
						    XOp (XEq, [v y; zero])])
    | (LogicalOr(x, y), CcNotZero) -> XOp (XLOr,  [XOp (XNe, [v x; zero]);
						    XOp (XNe, [v y; zero])])

    | (Sub(x, y), CcCarry)        ->  XOp (XLt, [v y; v x])
    | (Sub(x, y), CcNotCarry)     ->  XOp (XGe, [v y; v x])
    | (Sub(x, y), CcZero)         ->  XOp (XEq, [v y; v x])
    | (Sub(x, y), CcNotZero)      ->  XOp (XNe, [v y; v x])
    | (Sub(x, y), CcBelowEqual)   ->  XOp (XLe, [v y; v x])
    | (Sub(x, y), CcAbove)        ->  XOp (XGt, [v y; v x])
    | (Sub(x, y), CcLess)         ->  XOp (XLt, [v y; v x])
    | (Sub(x, y), CcGreaterEqual) ->  XOp (XGe, [v y; v x])
    | (Sub(x, y), CcLessEqual)    ->  XOp (XLe, [v y; v x])
    | (Sub(x, y), CcGreater)      ->  XOp (XGt, [v y; v x])

    | (Test ( x, y), CcZero)         when x#equal y -> XOp (XEq, [v x; zero])
    | (Test ( x, y), CcNotZero)      when x#equal y -> XOp (XNe, [v x; zero])
    | (Test ( x, y), CcSign)         when x#equal y -> XOp (XLt, [v x; zero])
    | (Test ( x, y), CcNotSign)      when x#equal y -> XOp (XGe, [v x; zero])
    | (Test ( x, y), CcBelowEqual)   when x#equal y -> XOp (XEq, [v x; zero])
    | (Test ( x, y), CcAbove)        when x#equal y -> XOp (XNe, [v x; zero])
    | (Test ( x, y), CcLess)         when x#equal y -> XOp (XLt, [v x; zero])
    | (Test ( x, y), CcGreaterEqual) when x#equal y -> XOp (XGe, [v x; zero])
    | (Test ( x, y), CcLessEqual)    when x#equal y -> XOp (XLe, [v x; zero])
    | (Test ( x, y), CcGreater)      when x#equal y -> XOp (XGt, [v x; zero])

    | _ ->
       begin
         found := false;
         random_constant_expr
       end in
  let expr = simplify_xpr expr in
  if is_random expr then
    (!found, None)
  else
    (true, Some expr)


let conditional_jump_expr
    ~(jumpopc:opcode_t)
    ~(testopc:opcode_t)
    ~(jumploc:location_int)
    ~(testloc:location_int): (variable_t list * xpr_t option) =
  let frozenVars = new VariableCollections.table_t in
  let add v fv = frozenVars#set v fv in
  let v = freeze_variables add testloc jumploc in
  let vu = freeze_variables ~unsigned:true add testloc jumploc in
  let testfloc = get_floc testloc in
  let jumpfloc = get_floc jumploc in
  let zero = zero_constant_expr in
  let (found,optTestExpr) =
    match jumpopc with
    | Jecxz _ -> (true, Some (XOp (XEq, [v (ecx_r RW); zero])))
    | DirectLoop _ -> (true, Some (XOp (XNe, [v (ecx_r RW); zero])))
    | Jcc (cc, _) -> cc_expr v vu testopc cc
    | _ ->
       raise
         (BCH_failure
	    (LBLOCK [
                 jumploc#toPretty; STR ": "; STR " not a conditional jump"])) in
  if found then
    match optTestExpr with
    | Some expr ->
       if is_false expr then
         begin
           chlog#add
             "false condition (ignored)"
             (LBLOCK [
                  jumploc#toPretty;
                  STR " with ";
                  testloc#toPretty;
                  STR ": (";
                  STR (opcode_to_string jumpopc);
                  STR ", ";
                  STR (opcode_to_string testopc)]);
           (frozenVars#listOfValues, None)
         end
       else
	 begin
	   jumpfloc#set_test_expr expr;
	   testfloc#set_test_variables frozenVars#listOfPairs;
	   (frozenVars#listOfValues, optTestExpr)
	 end
    | _ -> (frozenVars#listOfValues, None)
  else
    begin
      chlog#add
        "unused condition"
        (LBLOCK [
             jumpfloc#l#toPretty; STR ": ";
	     STR (opcode_to_string jumpopc); STR " with ";
	     STR (opcode_to_string testopc)]);
      (frozenVars#listOfValues, None)
    end


let conditional_set_expr
      ~(setopc:opcode_t)
      ~(testopc:opcode_t)
      ~(setloc:location_int)
      ~(testloc:location_int): xpr_t =
  let frozenVars = new VariableCollections.table_t in
  let add v fv = frozenVars#set v fv in
  let v = freeze_variables add testloc setloc in
  let vu = freeze_variables ~unsigned:true add testloc setloc in
  let (found, optTestExpr) =
    match setopc with
    | Setcc (cc, _) -> cc_expr v vu testopc cc
    | _ ->
       raise
         (BCH_failure
	    (LBLOCK [
                 setloc#toPretty; STR ": ";
		 STR " not a conditional set instruction"])) in
  if found then
    match optTestExpr with
    | Some expr -> expr
    | _ -> random_constant_expr
  else
    random_constant_expr

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


(* Conditional execution: conditions
   
   EQ  Equal                        Z = 1
   NE  Not Equal                    Z = 0
   CS  Carry set                    C = 1
   CC  Carry clear                  C = 0
   MI  Minus, Negative              N = 1
   PL  Plus, positive or zero       N = 0
   VS  Overflow                     V = 1
   VC  No overflow                  V = 0
   HI  Unsigned higher              C = 1 and Z = 0
   LS  Unsigned lower or same       C = 0 or Z = 1
   GE  Signed greater than or equal N = V
   LT  Signed less than             N != V
   GT  Signed greater than          Z = 0 and N = V
   LE  Signed less than or equal    Z = 1 or N != V

   Setter instructions:

   CMP x, y:
   ---------
        (result, carry, overflow) = AddWithCarry(x, NOT(y), 1)
        N = result<31>   x < y (?)
        Z = result == 0  x - y == 0   -> x == y
        C = carry        x >= y
        V = overflow     x - y < -e31 or x - y > e31 (x < y - e31 or x > y + e31)

   setter      condition     predicate (on unsigned)
   CMP x, y    EQ            x = y
               NE            x != y
               LE            x = y    (Z = 1)
                             | (x < y & ((x < e31 & y < e31)    (N = 1, V = 0)
                                        | (x >= e31 & y >= 31)))
                             | (x >= y & (x >= e31 & y < e31))  (N = 0, V = 1)
      CMP x, 0 LE            x = 0    (Z = 1)
                             | (x > e31)   (N = 0, V = 1)

               GE            (x >= y & x < e31 & y < e31)      (N = 0, V = 0)
                             | (x < y & x < e31 & y >= e31)    (N = 1, V = 1)
      CMP x, 0 GE            (x >= 0 & x < e31)                (N = 0, V = 0)

               HI            (x > y)   (C = 1 and Z = 0)
 *)

let x2p = xpr_formatter#pr_expr

let tracked_locations = [ "0x10d90"; "0x10d98" ]

let track_location loc p =
  if List.mem loc tracked_locations then
    chlog#add ("tracked:" ^ loc) p


let freeze_variables
      ?(unsigned=false)
      (add:variable_t -> variable_t -> unit) 
      (testloc:location_int)
      (condloc:location_int)
      (op:arm_operand_int)  =
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
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
          let _ = track_location
                    testloc#ci
                    (LBLOCK [v#toPretty; NL;
                             testfloc#inv#toPretty; NL;
                             condfloc#inv#toPretty]) in
          if condfloc#inv#test_var_is_equal v testloc#ci condloc#ci then
            let _ = track_location
                      condloc#ci
                      (LBLOCK [v#toPretty; NL;
                               STR " test_var_is_equal"]) in
            ()
          else
            let fv =
              env#mk_frozen_test_value
                v testloc#ci condloc#ci in frozenVars#set v fv
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


let cc_expr
      (v: arm_operand_int -> xpr_t)   (* signed *)
      (vu: arm_operand_int -> xpr_t)  (* unsigned *)
      (testfloc: floc_int)
      (testopc: arm_opcode_t)
      (cc: arm_opcode_cc_t): (bool * xpr_t option) =
  let found = ref true in
  let iszero op =
    match testfloc#inv#rewrite_expr
            (op#to_expr testfloc) testfloc#env#get_variable_comparator with
    | XConst (IntConst n) -> n#equal numerical_zero
    | _ -> false in
  let gezero op =
    match testfloc#inv#rewrite_expr
            (op#to_expr testfloc) testfloc#env#get_variable_comparator with
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
       (match v x with
        | XVar var when testfloc#env#is_signed_symbolic_value var ->
           XOp (XLOr, [XOp (XEq, [v x; zero_constant_expr]);
                       XOp (XGe, [v x; int_constant_expr e15])])
        | _ ->
           XOp (XLOr, [XOp (XEq, [v x; zero_constant_expr]);
                       XOp (XGe, [v x; int_constant_expr e31])]))

    | (Compare (ACCAlways, x, y, _), ACCSignedGE) when iszero y ->
       XOp (XLAnd, [XOp (XGe, [v x; v y]);
                    XOp (XLt, [v x; int_constant_expr e31])])

    | (Compare (ACCAlways, x, y, _), ACCSignedGE) ->
       XOp (XLOr, [XOp (XLAnd, [XOp (XGe, [v x; v y]);
                                XOp (XLt, [v x; int_constant_expr e31]);
                                XOp (XLt, [v y; int_constant_expr e31])]);
                   XOp (XLAnd, [XOp (XLt, [v x; v y]);
                                XOp (XLt, [v x; int_constant_expr e31]);
                                XOp (XGe, [v y; int_constant_expr e31])])])

    | (Compare (ACCAlways, x, y, _), ACCUnsignedHigher) ->
       XOp (XGt, [v x; v y])

    | (Compare (ACCAlways, x, y, _), ACCNotUnsignedHigher) ->
       XOp (XLe, [v x; v y])
                  
    | _ -> begin found := false; random_constant_expr end in
  let expr = simplify_xpr expr in
  if is_random expr then (!found, None) else (true, Some expr)


let arm_conditional_expr
    ~(condopc:arm_opcode_t)
    ~(testopc:arm_opcode_t)
    ~(condloc:location_int)
    ~(testloc:location_int) =
  let frozenVars = new VariableCollections.table_t in
  let add v fv = frozenVars#set v fv in
  let v = freeze_variables add testloc condloc in
  let vu = freeze_variables ~unsigned:true add testloc condloc in
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
  let (found, optxpr) =
    match condopc with
    | Branch (c, _, _)
      | BranchExchange (c, _) when is_cond_conditional c ->
       cc_expr v vu testfloc testopc c
    | IfThen (c, _) when is_cond_conditional c ->
       cc_expr v vu testfloc testopc c
    | _ -> (false, None) in
  if found then
    match optxpr with
    | Some expr ->
	if is_false expr then (frozenVars#listOfValues, None) else
	begin
	  condfloc#set_test_expr expr ;
	  testfloc#set_test_variables frozenVars#listOfPairs ;
	  (frozenVars#listOfValues, optxpr)
	end
    | _ -> (frozenVars#listOfValues, None)
  else
    begin
      chlog#add
        "unused condition"
        (LBLOCK [
             condfloc#l#toPretty;
             STR ": "; 
	     STR (arm_opcode_to_string condopc);
             STR " with "; 
	     STR (arm_opcode_to_string testopc)]);
      (frozenVars#listOfValues, None)
    end
      

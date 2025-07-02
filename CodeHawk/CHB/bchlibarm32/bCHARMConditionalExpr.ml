(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs LLC

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
open BCHDoubleword
open BCHFloc
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes
open BCHARMOpcodeRecords

module TR = CHTraceResult


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


   CMN x, y:
   ---------
       (result, carry, overflow) = AddWithCarry(x, y, 0)
       N = result<31>    signed(x + y) < 0
       Z = result == 0   x + y = 0 , mod(x + y) = e32
       C = carry         unsigned(x + y) >= e32
       V = overflow      signed(x + y) >= e31 \/ signed(x + y) <= -e31

    setter     condition    predicate (on unsigned)
    CMN x, 1   LE           x < 0
    CMN x, 1   GT           x >= 0

 *)

let x2p = xpr_formatter#pr_expr
let max32_constant_expr = int_constant_expr e32

let tracked_locations = []


let track_location loc p =
  if List.mem loc tracked_locations then
    ch_diagnostics_log#add ("tracked:" ^ loc) p


let freeze_variables
      ?(unsigned=false)
      (add:variable_t -> variable_t -> unit)
      (testloc:location_int)
      (condloc:location_int)
      (op:arm_operand_int): xpr_t =
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
  let env = testfloc#f#env in
  let frozenVars = new VariableCollections.table_t in
  TR.tfold
    ~error:(fun e ->
      begin
        log_error_result __FILE__ __LINE__ e;
        random_constant_expr
      end)
    ~ok:(fun opXpr ->
      let vars = (variables_in_expr opXpr) in
      let varsKnown = ref true in
      let _ =
        List.iter (
            fun v ->
            if v#isTmp then
              varsKnown := false
            else if env#is_function_initial_value v then
              ()
            else if env#is_local_variable v then
              let _ =
                track_location
                  testloc#ci
                  (LBLOCK [
                       v#toPretty; NL;
                       testfloc#inv#toPretty; NL;
                       condfloc#inv#toPretty]) in
              if condfloc#inv#test_var_is_equal v testloc#ci condloc#ci then
                let _ =
                  track_location
                    condloc#ci
                    (LBLOCK [
                         v#toPretty; NL;
                         STR " test_var_is_equal"]) in
                ()
              else
                let fv = env#mk_frozen_test_value v testloc#ci condloc#ci in
                frozenVars#set v fv
            else if env#is_unknown_memory_variable v then
              varsKnown := false) vars in
      let subst v =
        if frozenVars#has v then
          match testfloc#inv#get_external_exprs v with
          | x::_ -> x
          | _ -> XVar (Option.get (frozenVars#get v))
        else
          XVar v in
      if !varsKnown then
        begin
          List.iter (fun (v, fv) -> add v fv) frozenVars#listOfPairs ;
          substitute_expr subst opXpr
        end
      else
        random_constant_expr)
    (op#to_expr ~unsigned testfloc)


let cc_expr
      (v: arm_operand_int -> xpr_t)   (* signed *)
      (vu: arm_operand_int -> xpr_t)  (* unsigned *)
      (_testfloc: floc_int)
      (testopc: arm_opcode_t)
      (cc: arm_opcode_cc_t): (bool * xpr_t option * arm_operand_int list) =
  let found = ref true in
  let is_one (x: xpr_t) =
    match x with
    | XConst (IntConst n) -> n#equal CHNumerical.numerical_one | _ -> false in
  let (expr, opsused) =
    match (testopc, cc) with

    | (Add (true, ACCAlways, _, x, y, _), ACCNotEqual) ->
       (XOp (XNe, [XOp (XPlus, [v x; v y]); zero_constant_expr]), [x; y])

    (* -------------------------------------------------------------- And --- *)

    | (BitwiseAnd (true, ACCAlways, _, x, y, _), ACCEqual) ->
       (XOp (XEq, [XOp (XBAnd, [vu x; vu y]); zero_constant_expr]), [x; y])

    | (BitwiseAnd (true, ACCAlways, _, x, y, _), ACCNotEqual) ->
       (XOp (XNe, [XOp (XBAnd, [vu x; vu y]); zero_constant_expr]), [x; y])

    (* ---------------------------------------------------------- Compare --- *)

    | (Compare (ACCAlways, x, y, _), ACCEqual) ->
       (XOp (XEq, [v x; v y]), [x; y])
    | (Compare (ACCAlways, x, y, _), ACCNotEqual) ->
       (XOp (XNe, [v x; v y]), [x; y])

    (* Occasionally the compiler will generate a a carryset condition for
       a signed integer to obtain a disjunctionof the form (if y is
       known to be non-negative)

          x >= y || x < 0

       For a signed integer four cases can be considered:

         x        y      x >=u y  (unsigned greater equal)
       -----------------------------------------------------------
        >= 0     >= 0    x >= y
        >= 0     < 0     false (since neg. numbers are larger than pos. numbers)
        < 0      >= 0    true (idem, reversed)
        < 0      < 0     x <= y

       This can be written as a disjunction of conjuncts as follows:

          (x >= 0 && y >= 0 && x >= y)
       || (x >= 0 && y < 0 && false)
       || (x < 0 && y >= 0 && true)
       || (x < 0 && y < 0 && x <= y)

       If y is known to be non-negative this can be simplified to

          (x >= 0 && x >= y) || (x < 0)

       which is equivalent to

          x >= y || x < 0

       as desired.

       for unsigned comparison this is still valid since x < 0 is
       always false.
     *)
    | (Compare (_, x, y, _), ACCCarrySet) ->
       (XOp (XLOr, [XOp (XGe, [vu x; vu y]);
                    XOp (XLt, [vu x; zero_constant_expr])]), [x; y])

    (* Occasionally the compiler will generate a carryclear condition
       for a signed integer to obtain a conjunction of the form (if y
       is known to be non-negative)

           x < y && x >= 0

       For a signed integer four cases can be considered:

         x        y      x <u y  (unsigned less than)
       -----------------------------------------------------------
        >= 0     >= 0    x < y
        >= 0     < 0     true (since neg. numbers are larger than pos. numbers)
        < 0      >= 0    false (idem, reversed)
        < 0      < 0     x > y

        This can be written as a disjunction of conjuncts as follows:

            (x >= 0 && y >= 0 && x < y)
        ||  (x >= 0 && y < 0 && true)
        ||  (x < 0 && y >= 0 && false)
        ||  (x < 0 && y < 0 && x > y)

        If y is known to be non-negative this can be simplified to

            (x >= 0 && x < y)

        since the second, third, and fourth disjunct simplify to false.

        for unsigned integer comparisons the second, third, and fourth
        disjunct vacuously simplify to false, and the conjunct x >= 0
        is vacuously true, so this is a valid representation in that
        case as well.
     *)
    | (Compare (_, x, y, _), ACCCarryClear) ->
       (XOp (XLAnd, [XOp (XLt, [vu x; vu y]);
                     XOp (XGe, [vu x; zero_constant_expr])]), [x; y])

    | (Compare (ACCAlways, x, y, _), ACCUnsignedHigher) ->
       (XOp (XGt, [vu x; vu y]), [x; y])
    | (Compare (ACCAlways, x, y, _), ACCNotUnsignedHigher) ->
       (XOp (XLe, [vu x; vu y]), [x; y])

    | (Compare (ACCAlways, x, y, _), ACCSignedGE) ->
       (XOp (XGe, [v x; v y]), [x; y])
    | (Compare (ACCAlways, x, y, _), ACCSignedLT) ->
       (XOp (XLt, [v x; v y]), [x; y])

    | (Compare (ACCAlways, x, y, _), ACCSignedLE) ->
       (XOp (XLe, [v x; v y]), [x; y])
    | (Compare (ACCAlways, x, y, _), ACCSignedGT) ->
       (XOp (XGt, [v x; v y]), [x; y])

    | (LogicalShiftLeft (true, ACCAlways, _, x, y, _), ACCNonNegative) ->
       (XOp (XGe, [XOp (XLsl, [vu x; vu y]); zero_constant_expr]), [x; y])

    (* ------------------------------------------------- Compare-negative --- *)

    | (CompareNegative (ACCAlways, x, y), ACCEqual) ->
       (XOp (XEq, [XOp (XPlus, [v x; v y]); zero_constant_expr]), [x; y])

    | (CompareNegative (ACCAlways, x, y), ACCNotEqual) ->
       (XOp (XNe, [XOp (XPlus, [v x; v y]); zero_constant_expr]), [x; y])

    | (CompareNegative (ACCAlways, x, y), ACCCarrySet) ->
       (XOp (XGe, [XOp (XPlus, [vu x; vu y]); max32_constant_expr]), [x; y])

    | (CompareNegative (ACCAlways, x, y), ACCUnsignedHigher) ->
       (XOp (XGt, [XOp (XPlus, [vu x; vu y]); max32_constant_expr]), [x; y])

    | (CompareNegative (ACCAlways, x, y), ACCSignedGT) when (is_one (v y)) ->
       (XOp (XGe, [v x; zero_constant_expr]), [x; y])

    | (CompareNegative (ACCAlways, x, y), ACCSignedLE) when (is_one (v y)) ->
       (XOp (XLt, [v x; zero_constant_expr]), [x; y])

    | (CompareNegative (ACCAlways, x, y), ACCCarryClear) ->
       (XOp (XLOr, [XOp (XLt, [XOp (XPlus, [v x; v y]); zero_constant_expr]);
                    XOp (XGe, [v x; zero_constant_expr])]), [x; y])

    (* ------------------------------------------------------------- Move --- *)

    | (Move (true, ACCAlways, _, x, _, _), ACCEqual) ->
       (XOp (XEq, [v x; zero_constant_expr]), [x])

    | (Move (true, ACCAlways, _, x, _, _), ACCNotEqual) ->
       (XOp (XNe, [v x; zero_constant_expr]), [x])

    (* ------------------------------------------------- Reverse Subtract --- *)

    | (ReverseSubtract (true, ACCAlways, _, x, y, _), ACCNonNegative) ->
       (XOp (XGe, [XOp (XMinus, [v y; v x]); zero_constant_expr]), [x; y])

    (* --------------------------------------------------------- Subtract --- *)

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCEqual) ->
       (XOp (XEq, [XOp (XMinus, [v x; v y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCCarrySet) ->
       (XOp (XGe, [XOp (XMinus, [vu x; vu y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCSignedGE) ->
       (XOp (XGe, [XOp (XMinus, [v x; v y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCSignedGT) ->
       (XOp (XGt, [XOp (XMinus, [v x; v y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCUnsignedHigher) ->
       (XOp (XGt, [XOp (XMinus, [vu x; vu y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCSignedLE) ->
       (XOp (XLe, [XOp (XMinus, [vu x; vu y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCSignedLT) ->
       (XOp (XLt, [XOp (XMinus, [v x; v y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCNegative) ->
       (XOp (XLt, [XOp (XMinus, [v x; v y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCNonNegative) ->
       (XOp (XGe, [XOp (XMinus, [v x; v y]); zero_constant_expr]), [x; y])

    | (Subtract (true, ACCAlways, _, x, y, _, _), ACCNotEqual) ->
       (XOp (XNe, [XOp (XMinus, [v x; v y]); zero_constant_expr]), [x; y])

    (* -------------------------------------------------------------- Test --- *)

    | (Test (ACCAlways, x, y, _), ACCEqual) ->
       (XOp (XEq, [XOp (XBAnd, [vu x; vu y]); zero_constant_expr]), [x; y])

    | (Test (ACCAlways, x, y, _), ACCNotEqual) ->
       (XOp (XNe, [XOp (XBAnd, [vu x; vu y]); zero_constant_expr]), [x; y])

    (* ---------------------------------------------------------- VCompare --- *)

    | (VCompare (_, ACCAlways, _, _, x, y), ACCSignedGT) ->
       (XOp (XGt, [v x; v y]), [x; y])
    | (VCompare (_, ACCAlways, _, _, x, y), ACCSignedLE) ->
       (XOp (XLe, [v x; v y]), [x; y])
    | (VCompare (_, ACCAlways, _, _, x, y), ACCNonNegative) ->
       (XOp (XGe, [v x; v y]), [x; y])

    | _ ->
       begin
         found := false;
         (random_constant_expr, [])
       end in
  if is_random expr then
    (!found, None, opsused)
  else
    (true, Some expr, opsused)


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
  let (found, optxpr, opsused) =
    match get_arm_opcode_condition condopc with
    | Some c when is_cond_conditional c ->
       cc_expr v vu testfloc testopc c
    | _ -> (false, None, []) in

  if found then
    match optxpr with
    | Some expr ->
       let expr = simplify_xpr expr in
       if is_false expr then
         (frozenVars#listOfValues, None, opsused)
       else
	 begin
           (if collect_diagnostics () then
              ch_diagnostics_log#add
                "condition"
                (LBLOCK [condloc#toPretty; STR ": "; (x2p expr); STR ". ";
                         pretty_print_list frozenVars#listOfValues
                           (fun v -> v#toPretty) "[" ", " "]" ]));
	   condfloc#set_test_expr expr;
	   testfloc#set_test_variables frozenVars#listOfPairs;
	   (frozenVars#listOfValues, (Some expr), opsused)
	 end
    | _ -> (frozenVars#listOfValues, None, opsused)
  else
    begin
      (if collect_diagnostics () then
         ch_diagnostics_log#add
           "unused condition"
           (LBLOCK [
                condfloc#l#toPretty;
                STR ": ";
	        STR (arm_opcode_to_string condopc);
                STR " with ";
	        STR (arm_opcode_to_string testopc)]));
      (frozenVars#listOfValues, None, opsused)
    end


let arm_conditional_conditional_expr
      ~(condopc: arm_opcode_t)
      ~(testopc: arm_opcode_t)
      ~(testtestopc: arm_opcode_t)
      ~(condloc: location_int)
      ~(testloc: location_int)
      ~(testtestloc: location_int) =
  let condfloc = get_floc condloc in
  let (fv1, cond1, opsused1) =
    arm_conditional_expr
      ~condopc: testopc
      ~testopc: testtestopc
      ~condloc: testloc
      ~testloc: testtestloc in
  let (fv2, cond2, opsused2) =
    arm_conditional_expr
      ~condopc
      ~testopc
      ~condloc
      ~testloc in
  let (fv3, cond3, opsused3) =
    arm_conditional_expr
      ~condopc
      ~testopc: testtestopc
      ~condloc
      ~testloc: testtestloc in
  let frozenVars = new VariableCollections.set_t in
  let _ = frozenVars#addList fv1 in
  let _ = frozenVars#addList fv2 in
  let _ = frozenVars#addList fv3 in
  let opsused = opsused1 @ opsused2 @ opsused3 in
  match (cond1, cond2, cond3) with
  | (Some cond1, Some cond2, Some cond3) ->
     let _ =
       if collect_diagnostics () then
         ch_diagnostics_log#add
           "conditional condition expressions"
           (LBLOCK [
                STR (arm_opcode_to_string condopc);
                STR "; ";
                STR (arm_opcode_to_string testopc);
                STR "; ";
                STR (arm_opcode_to_string testtestopc);
                STR ": cond1: ";
                x2p cond1;
                STR "; cond2: ";
                x2p cond2;
                STR "; cond3: ";
                x2p cond3]) in

     let xpr = XOp (XLOr, [XOp (XLAnd, [XOp (XLNot, [cond1]); cond3]);
                           XOp (XLAnd, [cond1; cond2])]) in
     begin
       (if collect_diagnostics () then
          ch_diagnostics_log#add "condition" (x2p xpr));
       condfloc#set_test_expr xpr;
       (frozenVars#toList, Some xpr, opsused)
     end
  | _ -> (frozenVars#toList, None, opsused)

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs LLC

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
open XprUtil

(* bchlib *)
open BCHFloc
open BCHLibTypes

(* bchlibpower32 *)
open BCHPowerOpcodeRecords
open BCHPowerTypes


let tracked_locations = []


let track_location loc p =
  if List.mem loc tracked_locations then
    ch_diagnostics_log#add ("tracked:" ^ loc) p


let freeze_variables
      ?(_unsigned=false)
      (add: variable_t -> variable_t -> unit)
      (testloc: location_int)
      (condloc: location_int)
      (op: pwr_operand_int)  =
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
    random_constant_expr


let pwr_conditional_expr
      ~(condopc: pwr_opcode_t)
      ~(testopc: pwr_opcode_t)
      ~(condloc: location_int)
      ~(testloc: location_int) =
  let frozenVars = new VariableCollections.table_t in
  let add v fv = frozenVars#set v fv in
  let v = freeze_variables add testloc condloc in
  let vu = freeze_variables ~_unsigned:true add testloc condloc in
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
  let (found, optxpr) =
    match condopc with
    | CBranchEqual _ ->
       (match testopc with
        | CompareImmediate (_, _, _, ra, simm) ->
           (true, Some (XOp (XEq, [v ra; v simm])))
        | CompareLogicalImmediate (_, _, _, ra, uimm) ->
           (true, Some (XOp (XEq, [vu ra; vu uimm])))
        | CompareWord (_, _, ra, rb) ->
           (true, Some (XOp (XEq, [v ra; v rb])))
        | _ -> (false, None))
    | CBranchLessEqual _ ->
       (match testopc with
        | CompareImmediate (_, _, _, ra, simm) ->
           (true, Some (XOp (XLe, [v ra; v simm])))
        | CompareLogical (_, _, ra, rb) ->
           (true, Some (XOp (XLe, [vu ra; vu rb])))
        | CompareLogicalImmediate (_, _, _, ra, uimm)->
           (true, Some (XOp (XLe, [vu ra; vu uimm])))
        | _ -> (false, None))
    | CBranchGreaterThan _ ->
       (match testopc with
        | CompareImmediate (_, _, _, ra, simm) ->
           (true, Some (XOp (XGt, [v ra; v simm])))
        | _ -> (false, None))
    | CBranchNotEqual _ ->
       (match testopc with
        | CompareImmediate (_, _, _, ra, simm) ->
           (true, Some (XOp (XNe, [v ra; v simm])))
        | CompareLogical (_, _, ra, rb) ->
           (true, Some (XOp (XNe, [vu ra; vu rb])))
        | CompareLogicalImmediate (_, _, _, ra, uimm) ->
           (true, Some (XOp (XNe, [vu ra; vu uimm])))
        | CompareWord (_, _, ra, rb) ->
           (true, Some (XOp (XNe, [v ra; v rb])))
        | _ -> (false, None))
    | _ -> (false, None) in

  if found then
    match optxpr with
    | Some expr ->
       condfloc#set_test_expr expr;
       testfloc#set_test_variables frozenVars#listOfPairs;
       (frozenVars#listOfValues, optxpr)
    | _ -> (frozenVars#listOfValues, None)
  else
    begin
      chlog#add
        "missing condition-test connection"
        (LBLOCK [
             condfloc#l#toPretty;
             STR ": ";
             STR (pwr_opcode_to_string condopc);
             STR " with ";
             STR (pwr_opcode_to_string testopc)]);
      (frozenVars#listOfValues, None)
    end

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023-2025 Aarno Labs LLC

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

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open Xsimplify


let x2p = xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s (x: xpr_t) = p2s (x2p x)


(* returns the largest constant term in the given expression, taking sign
   into account. If no constant terms are present zero is returned. *)
let rec largest_constant_term (x:xpr_t): numerical_t =
  match x with
  | XConst (IntConst n) -> n
  | XOp (XPlus, [x1; x2]) ->
    let c1 = largest_constant_term x1 in
    let c2 = largest_constant_term x2 in
    if c1#gt c2 then c1 else c2
  | XOp (XMinus, [x1; x2]) ->
    let c1 = largest_constant_term x1 in
    let c2 = largest_constant_term (XOp (XNeg, [x2])) in
    if c1#gt c2 then c1 else c2
  | _ -> numerical_zero


let smallest_constant_term (x: xpr_t): numerical_t =
  let rec aux (x: xpr_t) (polarity: bool) =
    match x, polarity with
    | XConst (IntConst n), true -> n
    | XConst (IntConst n), false -> n#neg
    | XOp (XPlus, [x1; x2]), _ ->
       let c1 = aux x1 polarity in
       let c2 = aux x2 polarity in
       if c1#lt c2 then c1 else c2
    | XOp (XMinus, [x1; x2]), _ ->
       let c1 = aux x1 polarity in
       let c2 = aux x2 (not polarity) in
       if c1#lt c2 then c1 else c2
    | _ -> numerical_zero in
  aux x true


let smallest_wrapped_constant_term (x: xpr_t): numerical_t * numerical_t =
  let x = simplify_xpr x in
  let l = largest_constant_term x in
  let s = smallest_constant_term x in
  if l#gt (mkNumericalPowerOf2 31) then
    (l, l#sub (mkNumericalPowerOf2 32))
  else
    (s, s)


(* rewrites the expression in a form with scaled terms first, followed by a
   constant term. *)
let normalize_offset_expr (x:xpr_t) =
  let rewrite_scaled_expr y =
    match y with
    | XConst _ | XVar _ -> y
    | XOp (XMult, [XConst _; _ ]) -> y
    | XOp (XMult, [y1; XConst _ as y2]) -> XOp (XMult, [y2; y1])
    | _ -> y in
  let x = simplify_xpr x in
  match x with
  | XConst _ | XVar _ -> x
  | XOp (XMult, _) -> rewrite_scaled_expr x
  | XOp (XPlus, [XConst _ as x1; x2]) -> XOp (XPlus, [rewrite_scaled_expr x2; x1])
  | XOp (XPlus, [x1; XConst _ as x2]) -> XOp (XPlus, [rewrite_scaled_expr x1; x2])
  | _ -> x


let normalize_scaled_ivar_expr (xpr: xpr_t) (ivar: variable_t): xpr_t option =
  let xpr = simplify_xpr xpr in
  let aux x =
    match x with
    | XVar v when v#equal ivar -> Some x
    | XOp (XPlus, [XVar v; XConst _]) when v#equal ivar -> Some x
    | XOp (XMult, [XVar v; XConst _]) when v#equal ivar -> Some x
    | XOp (XPlus, [XOp (XMult, [XVar v; XConst _]); XConst _]) when v#equal ivar ->
       Some x
    | _ ->
       let _ =
         log_error_result
           ~tag:"normalize-scaled-ivar-expr"
           __FILE__ __LINE__
           [(x2s x) ^ " with ivar " ^ (p2s ivar#toPretty)] in
       None
  in
  aux xpr


let rec vars_as_positive_terms (x:xpr_t) =
  match x with
    XVar v -> [ v ]
  | XOp (XPlus, [ x1 ; x2 ]) ->
     (vars_as_positive_terms x1) @ (vars_as_positive_terms x2)
  | XOp (XMinus, [ x1 ; _ ]) -> vars_as_positive_terms x1
  | _ -> []


let get_array_index_offset (xpr: xpr_t) (size: int): (xpr_t * xpr_t) option =
  let xpr = simplify_xpr xpr in
  let xzero = int_constant_expr 0 in
  if size = 1 then
    Some (xpr, xzero)
  else
    let numsize = mkNumerical size in
    match xpr with
    | XConst (IntConst n) ->
       let (quo, rem) = n#quomod (mkNumerical size) in
       Some (num_constant_expr quo, num_constant_expr rem)
    | XOp (XMult, [XConst (IntConst n); XVar v]) when n#equal numsize ->
       Some (XVar v, xzero)
    | XOp (XMult, [XConst (IntConst n); XOp ((XXlsh | XXlsb), [XVar v])])
         when n#equal numsize ->
       Some (XVar v, xzero)
    | XOp (XPlus, [XOp (XMult, [XConst (IntConst n1); XVar v]);
                   XConst (IntConst n2)])
      | XOp (XPlus, [XConst (IntConst n2);
                     XOp (XMult, [XConst (IntConst n1); XVar v])])
         when n1#equal numsize ->
       if n2#equal numerical_zero then
         Some (XVar v, xzero)
       else
         let (quo, rem) = n2#quomod numsize in
         let xrem = num_constant_expr rem in
         if quo#equal numerical_zero then
           Some (XVar v, xrem)
         else
           if quo#lt numerical_zero then
             Some (XOp (XMinus, [XVar v; num_constant_expr quo#neg]), xrem)
           else
             Some (XOp (XPlus, [XVar v; num_constant_expr quo]), xrem)
    | XOp (XMinus, [XOp (XMult, [XConst (IntConst n1); XVar v]);
                    XConst (IntConst n2)]) when n1#equal numsize ->
       if n2#equal numerical_zero then
         Some (XVar v, xzero)
       else
         let (quo, rem) = n2#neg#quomod numsize in
         let xrem = num_constant_expr rem in
         if quo#equal numerical_zero then
           Some (XVar v, xrem)
         else
           if quo#lt numerical_zero then
             Some (XOp (XMinus, [XVar v; num_constant_expr quo#neg]), xrem)
           else
             Some (XOp (XPlus, [XVar v; num_constant_expr quo]), xrem)
    | _ ->
       None

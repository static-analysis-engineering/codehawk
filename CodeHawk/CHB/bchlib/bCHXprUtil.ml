(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023      Aarno Labs LLC

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

(* xprlib *)
open XprTypes
open Xsimplify


(* returns the largest constant term in the given expression, taking sign into account *)
let rec largest_constant_term (x:xpr_t) =
  match x with 
    XConst (IntConst n) -> n
  | XOp (XPlus, [ x1 ; x2 ]) ->
    let c1 = largest_constant_term x1 in
    let c2 = largest_constant_term x2 in
    if c1#gt c2 then c1 else c2
  | XOp (XMinus, [ x1 ; x2 ]) ->
    let c1 = largest_constant_term x1 in
    let c2 = largest_constant_term (XOp (XNeg, [ x2 ])) in
    if c1#gt c2 then c1 else c2
  | _ -> numerical_zero


(* rewrites the expression in a form with constants first followed by (scaled) terms *)
let normalize_offset_expr (x:xpr_t) =
  let rewrite_scaled_expr y = 
    match y with
      XConst _ | XVar _ -> y
    | XOp (XMult, [ XConst _ ; _ ]) -> y
    | XOp (XMult, [ y1 ; XConst _ as y2 ]) -> XOp (XMult, [ y2 ; y1 ]) 
    | _ -> y in
  let x = simplify_xpr x in
  match x with
    XConst _ | XVar _ -> x
  | XOp (XMult, _) -> rewrite_scaled_expr x
  | XOp (XPlus, [ XConst _ as x1 ; x2 ]) -> XOp (XPlus, [ x1 ; rewrite_scaled_expr x2 ])
  | XOp (XPlus, [ x1 ; XConst _ as x2 ]) -> XOp (XPlus, [ x2 ; rewrite_scaled_expr x1 ])
  | _ -> x
    
let rec vars_as_positive_terms (x:xpr_t) =
  match x with
    XVar v -> [ v ]
  | XOp (XPlus, [ x1 ; x2 ]) -> (vars_as_positive_terms x1) @ (vars_as_positive_terms x2)
  | XOp (XMinus, [ x1 ; _ ]) -> vars_as_positive_terms x1
  | _ -> []

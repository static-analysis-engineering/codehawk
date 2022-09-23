(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open Xprt
open XprTypes
open Xsimplify


(* Use Farkas Lemma to discharge:
   consequence is implied if there exists non-negative c such that
   consequence - c * antecedent <= 0 is valid
   arguments: antecedent xa  : interpret as xa <= 0
              consequent xc  : interpret as xc <= 0
   result: (xa <= 0)  implies  (xc <= 0)
 *)
let xfimplies (xa:xpr_t) (xc:xpr_t) =
  let zero = num_constant_expr numerical_zero in
  let factors = List.map (fun f -> num_constant_expr (mkNumerical f))
                         [ 1 ; 2 ; 3 ; 4 ; 8 ] in
  let deps =
    List.map
      (fun f -> XOp (XMinus, [ xc ; XOp (XMult, [ f ; xa ]) ])) factors in
  List.fold_left (fun acc d ->
      acc ||
        let k = XOp (XLe, [ d ; zero ]) in
        is_true (simplify_xpr k)) false deps

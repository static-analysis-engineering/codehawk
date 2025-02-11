(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2025 Aarno Labs LLC

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

(* xprlib *)
open XprTypes

(* chlib *)
open CHLanguage
open CHNumerical

module X = Xprt


let xzero = X.zero_constant_expr

let xone = X.one_constant_expr

let xtrue = X.true_constant_expr

let xfalse = X.false_constant_expr

let xnegone = X.int_constant_expr (-1)

let xrnd = X.random_constant_expr

let xi_unknown = X.unknown_int_constant_expr

let mk_ix (i: int) = X.num_constant_expr (mkNumerical i)

let mk_nx (n: numerical_t) = X.num_constant_expr n

let mk_neg (x: xpr_t) = XOp (XNeg, [x])

let mk_var (name: string) = new variable_t (new symbol_t name) NUM_VAR_TYPE


let mk_addressof (name: string) =
  let v = mk_var name in
  XOp ((Xf "addressofvar"), [XVar v])


let mk_vars (name: string) (n: int) =
  let rec aux nn result =
    if nn = 0 then
      result
    else
      let v = mk_var (name ^ "_" ^ (string_of_int nn)) in
      aux (nn - 1) (v :: result) in
  aux n []

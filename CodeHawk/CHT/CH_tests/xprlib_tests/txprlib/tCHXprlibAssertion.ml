(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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


module A = TCHAssertion
module H = Hashtbl
module XP = XprToPretty
module XS = Xsimplify


let p2s = CHPrettyUtil.string_printer#print
let x2p = XP.xpr_formatter#pr_expr
let x2s x = p2s (x2p x)


let equal_xpr =
  A.make_equal (fun x1 x2 -> (x2s x1) = (x2s x2)) x2s


let is_true (x:xpr_t) = equal_xpr (XConst (BoolConst true)) x


let is_false (x:xpr_t) = equal_xpr (XConst (BoolConst false)) x


let implies (x1: xpr_t) (x2: xpr_t) (result: bool) =
  if result then
    ()
  else
    A.fail
      ("(" ^ (x2s x1) ^ " <= 0) implies (" ^ (x2s x2) ^ " <= 0)")
      ("unable to prove implication")
      ""

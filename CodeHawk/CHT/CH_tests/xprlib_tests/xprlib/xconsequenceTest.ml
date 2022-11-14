(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

module XA = TCHXprlibAssertion
module XG = TCHXprlibGenerator
module TS = TCHTestSuite

module C = Xconsequence
module X = Xprt


let () =
  begin

    TS.new_testsuite "xconsequence";

    (* v <= 0 implies v <= 0 *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        XA.implies v v (C.xfimplies v v));

    (* (v - 1) <= 0 implies v - 2 <= 0 *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.xone]) in
        let x2 = XOp (XMinus, [v; XG.mk_ix 2]) in
        XA.implies x1 x2 (C.xfimplies x1 x2));

    (* (v - 3) <= 0 implies (8 * (v - 3)) <= 0 *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 3]) in
        let x2 = XOp (XMult, [XG.mk_ix 8; XOp (XMinus, [v; XG.mk_ix 3])]) in
        XA.implies x1 x2 (C.xfimplies x1 x2));

    (* (v - 9) <= 0 implies ((4 * v) - 39) <= 0 *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let four = XG.mk_ix 4 in
        let x1 = XOp (XMinus, [v; XG.mk_ix 9]) in
        let x2 = XOp (XMinus, [XOp (XMult, [four; v]); XG.mk_ix 39]) in
        XA.implies x1 x2 (C.xfimplies x1 x2));

    (* ((v - 10) + 1) <= 0 implies (((0 + (v * 4) - 40) + 1) <= 0 *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let four = XG.mk_ix 4 in
        let ten = XG.mk_ix 10 in
        let x1 = XOp (XPlus, [XOp (XMinus, [v; ten]); XG.xone]) in
        let xfour = XOp (XMult, [v; four]) in
        let xfourpz = XOp (XPlus, [XG.xzero; xfour]) in
        let xfourpzm = XOp (XMinus, [xfourpz; XG.mk_ix 40]) in
        let x2 = XOp (XPlus, [xfourpzm; XG.xone]) in
        XA.implies x1 x2 (C.xfimplies x1 x2));
    
    TS.launch_tests ();
    exit 0
  end

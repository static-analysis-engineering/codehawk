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

module S = Xsimplify

let simplify = S.simplify_xpr


let testname = "xsimplifyTest"
let lastupdated = "2022-11-28"


let basic () =
  begin

    TS.new_testsuite testname lastupdated;

    (* 0 + 0 = 0 *)
    TS.add_simple_test
      (fun () ->
        XA.equal_xpr
          XG.xzero (simplify (XOp (XPlus, [XG.xzero; XG.xzero]))));

    (* v - v  simplifies to 0 *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        XA.equal_xpr XG.xzero (simplify (XOp (XMinus, [v; v]))));

    (* v <= v simplifies to true *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        XA.is_true (simplify (XOp (XLe, [v; v]))));

    (* (v - 2) - (v - 1) simplifies to -1 *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 1]) in
        let x2 = XOp (XMinus, [v; XG.mk_ix 2]) in
        XA.equal_xpr (XG.mk_ix (-1)) (simplify (XOp (XMinus, [x2; x1]))));

    (* (v - 2) - (v - 1) < 0 simplifies to true *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 1]) in
        let x2 = XOp (XMinus, [v; XG.mk_ix 2]) in
        let xdiff = XOp (XMinus, [x2; x1]) in
        XA.is_true (simplify (XOp (XLt, [xdiff; XG.xzero]))));

    (* ((v - 1) * 4) - (v * 4) < 0 simplifies to true *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMult, [v; XG.mk_ix 4]) in
        let x2 = XOp (XMult, [XOp (XMinus, [v; XG.xone]); XG.mk_ix 4]) in
        let xdiff = XOp (XMinus, [x2; x1]) in
        XA.is_true (simplify (XOp (XLt, [xdiff; XG.xzero]))));

    (* (v - 2) < (v - 1) simplifies to true *)
    TS.add_simple_test
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 1]) in
        let x2 = XOp (XMinus, [v; XG.mk_ix 2]) in
        XA.is_true (simplify (XOp (XLt, [x2; x1]))));

    (* ((4 * v) - 39) - (4 * (v - 9)) = -3 simplifies to -3 *)
    TS.add_simple_test
      (fun () ->
        let four = XG.mk_ix 4 in
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 9]) in
        let x2 = XOp (XMinus, [XOp (XMult, [four; v]); XG.mk_ix 39]) in
        let diff = XOp (XMinus, [x2; XOp (XMult, [XG.mk_ix 4; x1])]) in
        XA.equal_xpr (XG.mk_ix (-3)) (simplify diff));

    (* ((((0 + (v * 4)) - 40) + 1) - (4 * ((v - 10) + 1))) simplifies to -3 *)
    TS.add_simple_test
      (fun () ->
        let four = XG.mk_ix 4 in
        let ten = XG.mk_ix 10 in
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XPlus, [XOp (XMinus, [v; ten]); XG.xone]) in
        let xfour = XOp (XMult, [v; four]) in
        let xfourpz = XOp (XPlus, [XG.xzero; xfour]) in
        let xfourpzm = XOp (XMinus, [xfourpz; XG.mk_ix 40]) in
        let x2 = XOp (XPlus, [xfourpzm; XG.xone]) in
        let diff = XOp (XMinus, [x2; XOp (XMult, [four; x1])]) in
        XA.equal_xpr (XG.mk_ix (-3)) (simplify diff));

    (* 32767 < (32767 / 2) simplifies to false *)
    TS.add_simple_test
      (fun () ->
        let two = XG.mk_ix 2 in
        let a = XG.mk_ix 32767 in
        let ha = XOp (XDiv, [a; two]) in
        let r = XOp (XLt, [a; ha]) in
        XA.is_false (simplify r));

    (* 2 < (32767 / 2) simplifies to true *)
    TS.add_simple_test
      (fun () ->
        let two = XG.mk_ix 2 in
        let a = XG.mk_ix 32767 in
        let ha = XOp (XDiv, [a; two]) in
        let r = XOp (XLt, [two; ha]) in
        XA.is_true (simplify r));

    (* (v1 < v2) != 0 simplifies to v1 < v2 *)
    TS.add_simple_test
      (fun () ->
        let v1 = XVar (XG.mk_var "v1") in
        let v2 = XVar (XG.mk_var "v2") in
        let x1 = XOp (XLt, [v1; v2]) in
        let xpr = XOp (XNe, [x1; XG.xzero]) in
        XA.equal_xpr x1 (simplify xpr));

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    basic ();
    TS.exit_file ()
  end

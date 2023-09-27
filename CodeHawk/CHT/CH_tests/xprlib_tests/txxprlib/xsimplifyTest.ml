(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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
let lastupdated = "2023-09-22"


let basic () =
  begin

    TS.new_testsuite (testname ^ "_basic") lastupdated;

    (* 0 + 0 = 0 *)
    TS.add_simple_test
      ~title:"add-zero"
      (fun () ->
        XA.equal_xpr
          XG.xzero (simplify (XOp (XPlus, [XG.xzero; XG.xzero]))));

    (* v - v  simplifies to 0 *)
    TS.add_simple_test
      ~title:"subtract-equal"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        XA.equal_xpr XG.xzero (simplify (XOp (XMinus, [v; v]))));

    (* v <= v simplifies to true *)
    TS.add_simple_test
      ~title:"less-than-or-equal"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        XA.is_true (simplify (XOp (XLe, [v; v]))));

    (* (v - 2) - (v - 1) simplifies to -1 *)
    TS.add_simple_test
      ~title:"double-subtract"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 1]) in
        let x2 = XOp (XMinus, [v; XG.mk_ix 2]) in
        XA.equal_xpr (XG.mk_ix (-1)) (simplify (XOp (XMinus, [x2; x1]))));

    (* (v - 2) - (v - 1) < 0 simplifies to true *)
    TS.add_simple_test
      ~title:"double-subtract-less-than"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 1]) in
        let x2 = XOp (XMinus, [v; XG.mk_ix 2]) in
        let xdiff = XOp (XMinus, [x2; x1]) in
        XA.is_true (simplify (XOp (XLt, [xdiff; XG.xzero]))));

    (* ((v - 1) * 4) - (v * 4) < 0 simplifies to true *)
    TS.add_simple_test
      ~title:"subtract-multiply"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMult, [v; XG.mk_ix 4]) in
        let x2 = XOp (XMult, [XOp (XMinus, [v; XG.xone]); XG.mk_ix 4]) in
        let xdiff = XOp (XMinus, [x2; x1]) in
        XA.is_true (simplify (XOp (XLt, [xdiff; XG.xzero]))));

    (* (v - 2) < (v - 1) simplifies to true *)
    TS.add_simple_test
      ~title:"subtract-less-than"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 1]) in
        let x2 = XOp (XMinus, [v; XG.mk_ix 2]) in
        XA.is_true (simplify (XOp (XLt, [x2; x1]))));

    (* ((4 * v) - 39) - (4 * (v - 9)) = -3 simplifies to -3 *)
    TS.add_simple_test
      ~title:"multiply-subtract"
      (fun () ->
        let four = XG.mk_ix 4 in
        let v = XVar (XG.mk_var "v") in
        let x1 = XOp (XMinus, [v; XG.mk_ix 9]) in
        let x2 = XOp (XMinus, [XOp (XMult, [four; v]); XG.mk_ix 39]) in
        let diff = XOp (XMinus, [x2; XOp (XMult, [XG.mk_ix 4; x1])]) in
        XA.equal_xpr (XG.mk_ix (-3)) (simplify diff));

    (* ((((0 + (v * 4)) - 40) + 1) - (4 * ((v - 10) + 1))) simplifies to -3 *)
    TS.add_simple_test
      ~title:"mult-subtr-add"
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
      ~title:"divide-less-than"
      (fun () ->
        let two = XG.mk_ix 2 in
        let a = XG.mk_ix 32767 in
        let ha = XOp (XDiv, [a; two]) in
        let r = XOp (XLt, [a; ha]) in
        XA.is_false (simplify r));

    (* 2 < (32767 / 2) simplifies to true *)
    TS.add_simple_test
      ~title:"less-than-divide"
      (fun () ->
        let two = XG.mk_ix 2 in
        let a = XG.mk_ix 32767 in
        let ha = XOp (XDiv, [a; two]) in
        let r = XOp (XLt, [two; ha]) in
        XA.is_true (simplify r));

    (* (v1 < v2) != 0 simplifies to v1 < v2 *)
    TS.add_simple_test
      ~title:"not-zero-predicate-lt"
      (fun () ->
        let v1 = XVar (XG.mk_var "v1") in
        let v2 = XVar (XG.mk_var "v2") in
        let x1 = XOp (XLt, [v1; v2]) in
        let xpr = XOp (XNe, [x1; XG.xzero]) in
        XA.equal_xpr x1 (simplify xpr));

    (* (v1 - v2) != 0 simplifies to v1 != v2) *)
    TS.add_simple_test
      ~title:"not-zero-predicate-ne"
      (fun () ->
        let v1 = XVar (XG.mk_var "v1") in
        let v2 = XVar (XG.mk_var "v2") in
        let x1 = XOp (XMinus, [v1; v2]) in
        let xpr = XOp (XNe, [x1; XG.xzero]) in
        let expected = XOp (XNe, [v1; v2]) in
        XA.equal_xpr expected (simplify xpr));

    TS.add_simple_test
      ~title:"bitwise-or"
      (fun () ->
        let n1 = XG.mk_ix (0x19ff * 0x10000) in
        let n2 = XG.mk_ix 5376 in
        let xpr = XOp (XBOr, [n1; n2]) in
        let expected = XG.mk_ix 0x19ff1500 in
        XA.equal_xpr expected (simplify xpr));

    TS.launch_tests ()
  end


let reduce_plus () =
  begin

    TS.new_testsuite (testname ^ "_reduce_plus") lastupdated;

    (* c + 0 ==> c *)
    TS.add_simple_test
      ~title: "cst-add-zero"
      (fun () ->
        let eight = XG.mk_ix 8 in
        XA.equal_xpr eight (simplify (XOp (XPlus, [eight; XG.xzero]))));

    (* 0 + c ==> c *)
    TS.add_simple_test
      ~title: "zero-add-cst"
      (fun () ->
        let eight = XG.mk_ix 8 in
        XA.equal_xpr eight (simplify (XOp (XPlus, [XG.xzero; eight]))));

    (* a + b ==> sum(a, b) *)
    TS.add_simple_test
      ~title: "cst-add-cst"
      (fun () ->
        let i14 = XG.mk_ix 14 in
        let i42 = XG.mk_ix 42 in
        XA.equal_xpr (XG.mk_ix 56) (simplify (XOp (XPlus, [i14; i42]))));

    (* v + 0 ==> v *)
    TS.add_simple_test
      ~title: "var-add-zero"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        XA.equal_xpr v (simplify (XOp (XPlus, [v; XG.xzero]))));

    (* 0 + v ==> v *)
    TS.add_simple_test
      ~title: "zero-add-var"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        XA.equal_xpr v (simplify (XOp (XPlus, [XG.xzero; v]))));

    (* x + 0 ==> simplify(x) *)
    TS.add_simple_test
      ~title: "xpr-add-zero"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x = XOp (XMinus, [v; XG.mk_ix 1]) in
        XA.equal_xpr x (simplify (XOp (XPlus, [x; XG.xzero]))));

    (* 0 + x ==> simplify(x) *)
    TS.add_simple_test
      ~title: "zero-add-xpr"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let x = XOp (XMinus, [v; XG.mk_ix 1]) in
        XA.equal_xpr x (simplify (XOp (XPlus, [XG.xzero; x]))));

    (* x + (y - x) ==> simplify(y) *)
    TS.add_simple_test
      ~title: "cancel-right"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let u = XVar (XG.mk_var "u") in
        let x = XOp (XMinus, [v; XG.mk_ix 1]) in
        let y = XOp (XMult, [u; XG.mk_ix 14]) in
        let ny = simplify y in
        XA.equal_xpr ny (simplify (XOp (XPlus, [x; XOp (XMinus, [y; x])]))));

    (* (y - x) + x ==> simplify(y) *)
    TS.add_simple_test
      ~title: "cancel-left"
      (fun () ->
        let v = XVar (XG.mk_var "v") in
        let u = XVar (XG.mk_var "u") in
        let x = XOp (XMinus, [v; XG.mk_ix 1]) in
        let y = XOp (XMult, [u; XG.mk_ix 14]) in
        let ny = simplify y in
        XA.equal_xpr ny (simplify (XOp (XPlus, [XOp (XMinus, [y; x]); x]))));

    (* (x + y) + (z - y) ==> simplify(x + z) *)
    TS.add_simple_test
      ~title: "cancel-common-right"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let z = XVar (XG.mk_var "z") in
        let xzsum = XOp (XPlus, [x; z]) in
        let xysum = XOp (XPlus, [x; y]) in
        let zydiff = XOp (XMinus, [z; y]) in
        XA.equal_xpr xzsum (simplify (XOp (XPlus, [xysum; zydiff]))));

    (* (z - y) + (x + y) ==> simplify(x + z) *)
    TS.add_simple_test
      ~title: "cancel-common-left"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let z = XVar (XG.mk_var "z") in
        let zxsum = XOp (XPlus, [z; x]) in
        let xysum = XOp (XPlus, [x; y]) in
        let zydiff = XOp (XMinus, [z; y]) in
        XA.equal_xpr zxsum (simplify (XOp (XPlus, [zydiff; xysum]))));

    (* [a, b] + c ==> [a+c, b+c] *)
    TS.add_simple_test
      ~title: "range-add"
      (fun () ->
        let i14 = XG.mk_ix 14 in
        let i28 = XG.mk_ix 28 in
        let i12 = XG.mk_ix 12 in
        let i26 = XG.mk_ix 26 in
        let i40 = XG.mk_ix 40 in
        let rng = XOp (XNumRange, [i14; i28]) in
        let rrng = XOp (XNumRange, [i26; i40]) in
        XA.equal_xpr rrng (simplify (XOp (XPlus, [rng; i12]))));

    (* [a, _] + [b, _] ==> [a+b, _] *)
    TS.add_simple_test
      ~title: "lbrange-add"
      (fun () ->
        let i14 = XG.mk_ix 14 in
        let i28 = XG.mk_ix 28 in
        let i42 = XG.mk_ix 42 in
        let rng1 = XOp (XNumRange, [i14; XG.xi_unknown]) in
        let rng2 = XOp (XNumRange, [i28; XG.xi_unknown]) in
        let rrng = XOp (XNumRange, [i42; XG.xi_unknown]) in
        XA.equal_xpr rrng (simplify (XOp (XPlus, [rng1; rng2]))));

    (* [a, _] + [b, c] ==> [a+b, _] *)
    TS.add_simple_test
      ~title: "lbrange-add2"
      (fun () ->
        let i14 = XG.mk_ix 14 in
        let i28 = XG.mk_ix 28 in
        let i42 = XG.mk_ix 42 in
        let rng1 = XOp (XNumRange, [i14; XG.xi_unknown]) in
        let rng2 = XOp (XNumRange, [i28; i42]) in
        let rrng = XOp (XNumRange, [i42; XG.xi_unknown]) in
        XA.equal_xpr rrng (simplify (XOp (XPlus, [rng1; rng2]))));

    (* a + [b, _] ==> [a+b, _] *)
    TS.add_simple_test
      ~title: "lbrange-add3"
      (fun () ->
        let i14 = XG.mk_ix 14 in
        let i28 = XG.mk_ix 28 in
        let i42 = XG.mk_ix 42 in
        let rng2 = XOp (XNumRange, [i28; XG.xi_unknown]) in
        let rrng = XOp (XNumRange, [i42; XG.xi_unknown]) in
        XA.equal_xpr rrng (simplify (XOp (XPlus, [i14; rng2]))));

    (* a + (-b) ==> a - b *)
    TS.add_simple_test
      ~title: "add-neg"
      (fun () ->
        let i14 = XG.mk_ix 14 in
        let i7 = XG.mk_ix 7 in
        let im7 = XG.mk_neg i7 in
        XA.equal_xpr i7 (simplify (XOp (XPlus, [i14; im7]))));

    (* y + (-1 * x) ==> y - x *)
    TS.add_simple_test
      ~title: "add_mult-neg"
      (fun () ->
        let y = XVar (XG.mk_var "y") in
        let x = XVar (XG.mk_var "x") in
        let m = XOp (XMult, [XG.xnegone; x]) in
        let r = XOp (XMinus, [y; x]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [y; m]))));

    (* (-1 * x) + y ==> y - x *)
    TS.add_simple_test
      ~title: "add_mult-neg"
      (fun () ->
        let y = XVar (XG.mk_var "y") in
        let x = XVar (XG.mk_var "x") in
        let m = XOp (XMult, [XG.xnegone; x]) in
        let r = XOp (XMinus, [y; x]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [m; y]))));

    (* a + (b + x) ==> x + (a+b) *)
    TS.add_simple_test
      ~title: "add-assoc-left"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 14 in
        let b = XG.mk_ix 28 in
        let r = XOp (XPlus, [x; XG.mk_ix 42]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [a; XOp (XPlus, [b; x])]))));

    (* a + (x + b) ==> x + (a + b) *)
    TS.add_simple_test
      ~title: "add-assoc-left-comm"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 14 in
        let b = XG.mk_ix 28 in
        let r = XOp (XPlus, [x; XG.mk_ix 42]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [a; XOp (XPlus, [x; b])]))));

    (* (a + x) + b ==> x + (a + b) *)
    TS.add_simple_test
      ~title: "add-assoc-right"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 14 in
        let b = XG.mk_ix 28 in
        let r = XOp (XPlus, [x; XG.mk_ix 42]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [XOp (XPlus, [a; x]); b]))));

    (* (x + a) + b ==> x + (a + b) *)
    TS.add_simple_test
      ~title: "add-assoc-right-comm"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 14 in
        let b = XG.mk_ix 28 in
        let r = XOp (XPlus, [x; XG.mk_ix 42]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [XOp (XPlus, [x; a]); b]))));

    (* a + (b - x) ==> (a+b) - x *)
    TS.add_simple_test
      ~title: "sub-assoc-left"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 14 in
        let b = XG.mk_ix 28 in
        let r = XOp (XMinus, [XG.mk_ix 42; x]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [a; XOp (XMinus, [b; x])]))));

    (* (b - x) + a ==> (a+b) - x *)
    TS.add_simple_test
      ~title: "sub-assoc-right"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 14 in
        let b = XG.mk_ix 28 in
        let r = XOp (XMinus, [XG.mk_ix 42; x]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [XOp (XMinus, [b; x]); a]))));

    (* a + (x - b) ==> x + (a-b) for a > b *)
    TS.add_simple_test
      ~title: "sub-assoc-left-rev"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 28 in
        let b = XG.mk_ix 14 in
        let r = XOp (XPlus, [x; XG.mk_ix 14]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [a; XOp (XMinus, [x; b])]))));

    (* a + (x - b) ==> x for a = b *)
    TS.add_simple_test
      ~title: "sub-assoc-left-rev0"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 28 in
        let b = XG.mk_ix 28 in
        XA.equal_xpr x (simplify (XOp (XPlus, [a; XOp (XMinus, [x; b])]))));

    (* a + (x - b) ==> x for a < b *)
    TS.add_simple_test
      ~title: "sub-assoc-left-revmin"
      (fun () ->
        let x = XVar (XG.mk_var "x") in
        let a = XG.mk_ix 14 in
        let b = XG.mk_ix 18 in
        let r = XOp (XMinus, [x; XG.mk_ix 4]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [a; XOp (XMinus, [x; b])]))));

    (* (a - x) + y ==> (y - x) + a *)
    TS.add_simple_test
      ~title: "sub-assoc-right-var"
      (fun () ->
        let a = XG.mk_ix 17 in
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let r = XOp (XPlus, [XOp (XMinus, [y; x]); a]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [XOp (XMinus, [a; x]); y]))));

    (* (x - a) + y ==> (x + y) - a *)
    TS.add_simple_test
      ~title: "sub-assoc-right-var-rev"
      (fun () ->
        let a = XG.mk_ix 17 in
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let r = XOp (XMinus, [XOp (XPlus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [XOp (XMinus, [x; a]); y]))));

    (* x + (a - y) ==> (x - y) + a *)
    TS.add_simple_test
      ~title: "sub-assoc-left-var"
      (fun () ->
        let a = XG.mk_ix 17 in
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let r = XOp (XPlus, [XOp (XMinus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [x; XOp (XMinus, [a; y])]))));

    (* x + (y - a) ==> (x + y) - a *)
    TS.add_simple_test
      ~title: "sub-assoc-left-var2"
      (fun () ->
        let a = XG.mk_ix 17 in
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let r = XOp (XMinus, [XOp (XPlus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [x; XOp (XMinus, [y; a])]))));

    (* (a + x) + y ==> (x + y) + a *)
    TS.add_simple_test
      ~title: "add-assoc-right-var"
      (fun () ->
        let a = XG.mk_ix 17 in
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let r = XOp (XPlus, [XOp (XPlus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [XOp (XPlus, [a; x]); y]))));

    (* (x + a) + y ==> (x + y) + a *)
    TS.add_simple_test
      ~title: "add-assoc-right-var2"
      (fun () ->
        let a = XG.mk_ix 17 in
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let r = XOp (XPlus, [XOp (XPlus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [XOp (XPlus, [x; a]); y]))));

    (* x + (a + y) ==> (x + y) + a *)
    TS.add_simple_test
      ~title: "add-assoc-left-var"
      (fun () ->
        let a = XG.mk_ix 17 in
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let r = XOp (XPlus, [XOp (XPlus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [x; XOp (XPlus, [a; y])]))));

    (* x + (y + a) ==> (x + y) + a *)
    TS.add_simple_test
      ~title: "add-assoc-left-var2"
      (fun () ->
        let a = XG.mk_ix 17 in
        let x = XVar (XG.mk_var "x") in
        let y = XVar (XG.mk_var "y") in
        let r = XOp (XPlus, [XOp (XPlus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XPlus, [x; XOp (XPlus, [y; a])]))));

    (* (a * u) + (b * u) ==> (a+b) * u *)
    TS.add_simple_test
      ~title: "factor-out"
      (fun () ->
        let a = XG.mk_ix 17 in
        let b = XG.mk_ix 11 in
        let u = XVar (XG.mk_var "u") in
        let r = XOp (XMult, [XG.mk_ix 28; u]) in
        XA.equal_xpr
          r (simplify (XOp (XPlus, [XOp (XMult, [a; u]); XOp (XMult, [b; u])]))));

    TS.launch_tests ()
  end


let reduce_minus () =
  let a = XG.mk_ix 27 in
  let b = XG.mk_ix 12 in
  let apb = XG.mk_ix 39 in
  let amb = XG.mk_ix 15 in
  let x = XVar (XG.mk_var "x") in
  let y = XVar (XG.mk_var "y") in
  let z = XVar (XG.mk_var "z") in
  let u = XVar (XG.mk_var "u") in
  let xpy = XOp (XPlus, [x; y]) in
  let xmy = XOp (XMinus, [x; y]) in
  begin

    TS.new_testsuite (testname ^ "_reduce_minus") lastupdated;

    (* (x + y) - x ==> y *)
    TS.add_simple_test
      ~title: "cancel"
      (fun () ->
        XA.equal_xpr y (simplify (XOp (XMinus, [xpy; x]))));

    (* (x + y) - y ==> x *)
    TS.add_simple_test
      ~title: "cancel1"
      (fun () ->
        XA.equal_xpr x (simplify (XOp (XMinus, [xpy; y]))));

    (* (x - y) - x ==> -y *)
    TS.add_simple_test
      ~title: "cancel2"
      (fun () ->
        let negy = XOp (XNeg, [y]) in
        XA.equal_xpr negy (simplify (XOp (XMinus, [xmy; x]))));

    (* ((x + y) + z) - x ==> y + z *)
    TS.add_simple_test
      ~title: "cancel3"
      (fun () ->
        let r = XOp (XPlus, [y; z]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XPlus, [xpy; z]); x]))));

    (* ((x + y) + z) - y ==> x + z *)
    TS.add_simple_test
      ~title: "cancel4"
      (fun () ->
        let r = XOp (XPlus, [x; z]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XPlus, [xpy; z]); y]))));

    (* ((x - y) + z) - x  --> -y + z *)
    TS.add_simple_test
      ~title: "cancel5"
      (fun () ->
        let r = XOp (XPlus, [XOp (XNeg, [y]); z]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XPlus, [xmy; z]); x]))));

    (* ((x + y) + z) - z ==> x + y *)
    TS.add_simple_test
      ~title: "cancel6"
      (fun () ->
        XA.equal_xpr xpy (simplify (XOp (XMinus, [XOp (XPlus, [xpy; z]); z]))));

    (* ((x + y) - z) - x  ==>  y - z *)
    TS.add_simple_test
      ~title: "cancel7"
      (fun () ->
        let r = XOp (XMinus, [y; z]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XMinus, [xpy; z]); x]))));

    (* ((x + y) - z) - y  ==>  x - z *)
    TS.add_simple_test
      ~title: "cancel8"
      (fun () ->
        let r = XOp (XMinus, [x; z]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XMinus, [xpy; z]); y]))));

    (* (a - b) ==> a-b *)
    TS.add_simple_test
      ~title: "sub-const"
      (fun () ->
        XA.equal_xpr amb (simplify (XOp (XMinus, [a; b]))));

    (* [a, _] - b ==> [(a-b), _] *)
    TS.add_simple_test
      ~title: "sub-lbrange"
      (fun () ->
        let alb = XOp (XNumRange, [a; XG.xi_unknown]) in
        let r = XOp (XNumRange, [amb; XG.xi_unknown]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [alb; b]))));

    (* (a + x) - b  ==> x + (a-b) *)
    TS.add_simple_test
      ~title: "assoc-left"
      (fun () ->
        let r = XOp (XPlus, [x; amb]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XPlus, [a; x]); b]))));

    (* (x + a) - b  ==> x + (a-b) *)
    TS.add_simple_test
      ~title: "assoc-left2"
      (fun () ->
        let r = XOp (XPlus, [x; amb]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XPlus, [x; a]); b]))));

    (* a - (b - x)  ==> x + (a-b) *)
    TS.add_simple_test
      ~title: "assoc-right"
      (fun () ->
        let r = XOp (XPlus, [x; amb]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [a; XOp (XMinus, [b; x])]))));

    (* a - (x - b) ==> (a+b) - x *)
    TS.add_simple_test
      ~title: "assoc-right2"
      (fun () ->
        let r = XOp (XMinus, [apb; x]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [a; XOp (XMinus, [x; b])]))));

    (* (x - a) - b ==> x - (a+b) *)
    TS.add_simple_test
      ~title: "assoc-left3"
      (fun () ->
        let r = XOp (XMinus, [x; apb]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XMinus, [x; a]); b]))));

    (* (a + x) - y ==> (x - y) + a *)
    TS.add_simple_test
      ~title: "rearrange"
      (fun () ->
        let r = XOp (XPlus, [XOp (XMinus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XPlus, [a; x]); y]))));

    (* (x + a) - y ==> (x - y) + a *)
    TS.add_simple_test
      ~title: "rearrange"
      (fun () ->
        let r = XOp (XPlus, [XOp (XMinus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XPlus, [x; a]); y]))));

    (* (x - a) - y ==> (x - y) - a *)
    TS.add_simple_test
      ~title: "rearrange2"
      (fun () ->
        let r = XOp (XMinus, [XOp (XMinus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [XOp (XMinus, [x; a]); y]))));

    (* x - (a + y) ==> (x - y) - a *)
    TS.add_simple_test
      ~title: "rearrange3"
      (fun () ->
        let r = XOp (XMinus, [XOp (XMinus, [x; y]); a]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [x; XOp (XPlus, [a; y])]))));

    (* x - (a - y) ==> (x + y) - a *)
    TS.add_simple_test
      ~title: "rearrange4"
      (fun () ->
        let r = XOp (XMinus, [xpy; a]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [x; XOp (XMinus, [a; y])]))));

    (* x - (y - a) ==> (x - y) + a *)
    TS.add_simple_test
      ~title: "rearrange5"
      (fun () ->
        let r = XOp (XPlus, [xmy; a]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [x; XOp (XMinus, [y; a])]))));

    (* x - ((-1) * y) ==> x + y *)
    TS.add_simple_test
      ~title: "negone"
      (fun () ->
        let negy = XOp (XMult, [XG.xnegone; y]) in
        XA.equal_xpr xpy (simplify (XOp (XMinus, [x; negy]))));

    (* x - ((-1) * y) ==> x + y *)
    TS.add_simple_test
      ~title: "negone2"
      (fun () ->
        let negy = XOp (XMult, [y; XG.xnegone]) in
        XA.equal_xpr xpy (simplify (XOp (XMinus, [x; negy]))));

    (* (a * u) - (b * u) ==> (a-b) * u *)
    TS.add_simple_test
      ~title: "factor-out"
      (fun () ->
        let au = XOp (XMult, [a; u]) in
        let bu = XOp (XMult, [b; u]) in
        let r = XOp (XMult, [amb; u]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [au; bu]))));

    (* (u * a) - (u * b) ==> (a-b) * u *)
    TS.add_simple_test
      ~title: "factor-out2"
      (fun () ->
        let au = XOp (XMult, [u; a]) in
        let bu = XOp (XMult, [u; b]) in
        let r = XOp (XMult, [amb; u]) in
        XA.equal_xpr r (simplify (XOp (XMinus, [au; bu]))));

    TS.launch_tests ()
  end


let reduce_mult () =
  let a = XG.mk_ix 5 in
  let b = XG.mk_ix 7 in
  let c = XG.mk_ix 9 in
  let atb = XG.mk_ix 35 in
  let atc = XG.mk_ix 45 in
  let btc = XG.mk_ix 63 in
  let x = XVar (XG.mk_var "x") in
  begin

    TS.new_testsuite (testname ^ "_reduce_mult") lastupdated;

    (* x * 0 ==> 0 *)
    TS.add_simple_test
      ~title: "zero"
      (fun () ->
        XA.equal_xpr XG.xzero (simplify (XOp (XMult, [x; XG.xzero]))));

    (* 0 * x ==> 0 *)
    TS.add_simple_test
      ~title: "zero2"
      (fun () ->
        XA.equal_xpr XG.xzero (simplify (XOp (XMult, [XG.xzero; x]))));

    (* x * 1 ==> x *)
    TS.add_simple_test
      ~title: "one"
      (fun () ->
        XA.equal_xpr x (simplify (XOp (XMult, [x; XG.xone]))));

    (* 1 * x ==> x *)
    TS.add_simple_test
      ~title: "one2"
      (fun () ->
        XA.equal_xpr x (simplify (XOp (XMult, [XG.xone; x]))));

    (* a * b ==> a*b *)
    TS.add_simple_test
      ~title: "constants"
      (fun () ->
        XA.equal_xpr atb (simplify (XOp (XMult, [a; b]))));

    (* [a, b] * c ==> [a * c; b * c] *)
    TS.add_simple_test
      ~title: "closed-range"
      (fun () ->
        let rng = XOp (XNumRange, [a; b]) in
        let r = XOp (XNumRange, [atc; btc]) in
        XA.equal_xpr r (simplify (XOp (XMult, [rng; c]))));

    (* [a, _] * c ==> [a * c, _] *)
    TS.add_simple_test
      ~title: "lb-range"
      (fun () ->
        let rng = XOp (XNumRange, [a; XG.xi_unknown]) in
        let r = XOp (XNumRange, [atc; XG.xi_unknown]) in
        XA.equal_xpr r (simplify (XOp (XMult, [rng; c]))));

    (* (x - a) * b ->  ==> (b * x) - a*b *)
    TS.add_simple_test
      ~title: "distribute"
      (fun () ->
        let r = XOp (XMinus, [XOp (XMult, [b; x]); atb]) in
        XA.equal_xpr r (simplify (XOp (XMult, [XOp (XMinus, [x; a]); b]))));

    (* a * (x - b) ==> (a * x) - a*b) *)
    TS.add_simple_test
      ~title: "distribute2"
      (fun () ->
        let r = XOp (XMinus, [XOp (XMult, [a; x]); atb]) in
        XA.equal_xpr r (simplify (XOp (XMult, [a; XOp (XMinus, [x; b])]))));

    (* a * (b + x) ==> (a * x) + a*b) *)
    TS.add_simple_test
      ~title: "distribute3"
      (fun () ->
        let r = XOp (XPlus, [XOp (XMult, [a; x]); atb]) in
        XA.equal_xpr r (simplify (XOp (XMult, [a; XOp (XPlus, [b; x])]))));

    (* a * (b * x) ==> (a*b) * x *)
    TS.add_simple_test
      ~title: "combine"
      (fun () ->
        let r = XOp (XMult, [atb; x]) in
        XA.equal_xpr r (simplify (XOp (XMult, [a; XOp (XMult, [b; x])]))));

    (* a * (x * b) ==> (a*b) * x *)
    TS.add_simple_test
      ~title: "combine2"
      (fun () ->
        let r = XOp (XMult, [atb; x]) in
        XA.equal_xpr r (simplify (XOp (XMult, [a; XOp (XMult, [x; b])]))));

    (* (a * x) * b ==> (a*b) * x *)
    TS.add_simple_test
      ~title: "combine3"
      (fun () ->
        let r = XOp (XMult, [atb; x]) in
        XA.equal_xpr r (simplify (XOp (XMult, [XOp (XMult, [a; x]); b]))));

    (* (x * a) * b ==> (a*b) * x *)
    TS.add_simple_test
      ~title: "combine4"
      (fun () ->
        let r = XOp (XMult, [atb; x]) in
        XA.equal_xpr r (simplify (XOp (XMult, [XOp (XMult, [x; a]); b]))));

    (* x * a ==> a * x *)
    TS.add_simple_test
      ~title: "normalize"
      (fun () ->
        let r = XOp (XMult, [a; x]) in
        XA.equal_xpr r (simplify (XOp (XMult, [x; a]))));

    TS.launch_tests ()
  end


let reduce_div () =
  let a = XG.mk_ix 35 in
  let b = XG.mk_ix 7 in
  let adb = XG.mk_ix 5 in
  let x = XVar (XG.mk_var "x") in
  begin

    TS.new_testsuite (testname ^ "_reduce_div") lastupdated;

    (* 0 / x ==> 0 *)
    TS.add_simple_test
      ~title: "zero"
      (fun () ->
        XA.equal_xpr XG.xzero (simplify (XOp (XDiv, [XG.xzero; x]))));

    (* x / 1 ==> x *)
    TS.add_simple_test
      ~title: "one"
      (fun () -> XA.equal_xpr x (simplify (XOp (XDiv, [x; XG.xone]))));

    (* a / b ==> a/b *)
    TS.add_simple_test
      ~title: "constants"
      (fun () -> XA.equal_xpr adb (simplify (XOp (XDiv, [a; b]))));

    (* (a * x) / b ==> (a/b) * x *)
    TS.add_simple_test
      ~title: "redistribute"
      (fun () ->
        let r = XOp (XMult, [adb; x]) in
        XA.equal_xpr r (simplify (XOp (XDiv, [XOp (XMult, [a; x]); b]))));

    (* (x * a) / b ==> (a/b) * x *)
    TS.add_simple_test
      ~title: "redistribute2"
      (fun () ->
        let r = XOp (XMult, [adb; x]) in
        XA.equal_xpr r (simplify (XOp (XDiv, [XOp (XMult, [x; a]); b]))));

    TS.launch_tests ()
  end


let reduce_mod () =
  let a = XG.mk_ix 32 in
  let b = XG.mk_ix 5 in
  let amb = XG.mk_ix 2 in
  let am1 = XG.mk_ix 31 in
  let x = XVar (XG.mk_var "x") in
  begin

    TS.new_testsuite (testname ^ "_reduce_mod") lastupdated;

    (* 0 % x ==> 0 *)
    TS.add_simple_test
      ~title: "zero"
      (fun () ->
        XA.equal_xpr XG.xzero (simplify (XOp (XMod, [XG.xzero; x]))));

    (* x % 1 ==> 0 *)
    TS.add_simple_test
      ~title: "one"
      (fun () ->
        XA.equal_xpr XG.xzero (simplify (XOp (XMod, [x; XG.xone]))));

    (* a % b ==> a%b *)
    TS.add_simple_test
      ~title: "constants"
      (fun () -> XA.equal_xpr amb (simplify (XOp (XMod, [a; b]))));

    (* x % a ==> [0; (a-1)] *)
    TS.add_simple_test
      ~title: "range"
      (fun () ->
        let r = XOp (XNumRange, [XG.xzero; am1]) in
        XA.equal_xpr r (simplify (XOp (XMod, [x; a]))));

    TS.launch_tests ()
  end


let reduce_xlsb () =
  let x = XVar (XG.mk_var "x") in
  begin

    TS.new_testsuite (testname ^ "_reduce_xlsb") lastupdated;

    (* xlsb (xlsb x) ==> xlsb x *)
    TS.add_simple_test
      ~title: "idempotent"
      (fun () ->
        let r = XOp (XXlsb, [x]) in
        XA.equal_xpr r (simplify (XOp (XXlsb, [r]))));

    (* xlsb (xlsh x) ==> xlsb x *)
    TS.add_simple_test
      ~title: "absorption"
      (fun () ->
        let r = XOp (XXlsb, [x]) in
        XA.equal_xpr r (simplify (XOp (XXlsb, [XOp (XXlsh, [x])]))));

    (* xlsb ((xlsb x) / n) ==> (xlsb x) / n *)
    TS.add_simple_test
      ~title: "division"
      (fun () ->
        let r = XOp (XDiv, [XOp (XXlsb, [x]); XG.mk_ix 4]) in
        XA.equal_xpr r (simplify (XOp (XXlsb, [r]))));

    (* xlsb ((xlsb x) & n) ==> (xlsb x) & n *)
    TS.add_simple_test
      ~title: "binary-and"
      (fun () ->
        let r = XOp (XBAnd, [XOp (XXlsb, [x]); XG.mk_ix 4]) in
        XA.equal_xpr r (simplify (XOp (XXlsb, [r]))));

    TS.launch_tests ()
  end


let reduce_xlsh () =
  let x = XVar (XG.mk_var "x") in
  begin

    TS.new_testsuite (testname ^ "_reduce_lsh") lastupdated;

    (* xlsh (xlsh x) ==> xlsh x *)
    TS.add_simple_test
      ~title: "idempotent"
      (fun () ->
        let r = XOp (XXlsh, [x]) in
        XA.equal_xpr r (simplify (XOp (XXlsh, [r]))));

    (* xlsh (xlsb x) ==> xlsb x *)
    TS.add_simple_test
      ~title: "absorption"
      (fun () ->
        let r = XOp (XXlsb, [x]) in
        XA.equal_xpr r (simplify (XOp (XXlsh, [XOp (XXlsb, [x])]))));

    (* xlsh ((xlsb x) << n) ==> (xlsb x) << n  if 0 <= n <= 8 *)
    TS.add_simple_test
      ~title: "shift-left"
      (fun () ->
        let r = XOp (XLsl, [XOp (XXlsb, [x]); XG.mk_ix 8]) in
        XA.equal_xpr r (simplify (XOp (XXlsh, [r]))));

    TS.launch_tests ()
  end


let reduce_lt () =
  let v = XVar (XG.mk_var "v") in
  let x = XVar (XG.mk_var "x") in
  let a = XG.mk_ix 5 in
  let b = XG.mk_ix 2 in
  let c = XG.mk_ix 7 in
  let d = XG.mk_ix 3 in
  let e = XG.mk_ix (-3) in
  let i10 = XG.mk_ix 10 in
  begin

    TS.new_testsuite (testname ^ "_reduce_lt") lastupdated;

    (* b < a ==> true *)
    TS.add_simple_test
      ~title: "constant-true"
      (fun () -> XA.equal_xpr XG.xtrue (simplify (XOp (XLt, [b; a]))));

    (* a < b ==> false *)
    TS.add_simple_test
      ~title: "constant-false"
      (fun () -> XA.equal_xpr XG.xfalse (simplify (XOp (XLt, [a; b]))));

    (* v < v + a ==> true *)
    TS.add_simple_test
      ~title: "lt-var-true"
      (fun () ->
        XA.equal_xpr
          XG.xtrue (simplify (XOp (XLt, [v; XOp (XPlus, [v; a])]))));

    (* v < v - a ==> false *)
    TS.add_simple_test
      ~title: "lt-var-false"
      (fun () ->
        XA.equal_xpr
          XG.xfalse (simplify (XOp (XLt, [v; XOp (XMinus, [v; a])]))));

    (* v < v + x ==> x > 0 *)
    TS.add_simple_test
      ~title: "lt-addend"
      (fun () ->
        let r = XOp (XGt, [x; XG.xzero]) in
        XA.equal_xpr r (simplify (XOp (XLt, [v; XOp (XPlus, [v; x])]))));

    (* (v - a) < (v - b) ==> true *)
    TS.add_simple_test
      ~title: "pos-diff"
      (fun () ->
        XA.equal_xpr
          XG.xtrue
          (simplify (XOp (XLt, [XOp (XMinus, [v; a]); XOp (XMinus, [v; b])]))));

    (* (v - b) < (v - a) ==> false *)
    TS.add_simple_test
      ~title: "neg-diff"
      (fun () ->
        XA.equal_xpr
          XG.xfalse
          (simplify (XOp (XLt, [XOp (XMinus, [v; b]); XOp (XMinus, [v; a])]))));

    (* [b, a] < c ==> true *)
    TS.add_simple_test
      ~title: "range-true"
      (fun () ->
        XA.equal_xpr
          XG.xtrue (simplify (XOp (XLt, [XOp (XNumRange, [b; a]); c]))));

    (* c < [b, a] ==> false *)
    TS.add_simple_test
      ~title: "range-false"
      (fun () ->
        XA.equal_xpr
          XG.xfalse (simplify (XOp (XLt, [c; XOp (XNumRange, [b; a])]))));

    (* a < b + x ==> x > (a - b) *)
    TS.add_simple_test
      ~title: "move-left"
      (fun () ->
        let r = XOp (XGt, [x; d]) in
        XA.equal_xpr r (simplify (XOp (XLt, [a; XOp (XPlus, [b; x])]))));

    (* a < x + b ==> x > (a - b) *)
    TS.add_simple_test
      ~title: "move-left2"
      (fun () ->
        let r = XOp (XGt, [x; d]) in
        XA.equal_xpr r (simplify (XOp (XLt, [a; XOp (XPlus, [x; b])]))));

    (* a - x < b ==> x > (a - b) *)
    TS.add_simple_test
      ~title: "move-left3"
      (fun () ->
        let r = XOp (XGt, [x; d]) in
        XA.equal_xpr r (simplify (XOp (XLt, [XOp (XMinus, [a; x]); b]))));

    (* x - a < b ==> x < (a+b) *)
    TS.add_simple_test
      ~title: "move-right"
      (fun () ->
        let r = XOp (XLt, [x; c]) in
        XA.equal_xpr r (simplify (XOp (XLt, [XOp (XMinus, [x; a]); b]))));

    (* a < b - x ==> x < (b-a) *)
    TS.add_simple_test
      ~title: "exchange"
      (fun () ->
        let r = XOp (XLt, [x; e]) in
        XA.equal_xpr r (simplify (XOp (XLt, [a; XOp (XMinus, [b; x])]))));

    (* a < x - b ==> x > (a+b) *)
    TS.add_simple_test
      ~title: "exchange2"
      (fun () ->
        let r = XOp (XGt, [x; c]) in
        XA.equal_xpr r (simplify (XOp (XLt, [a; XOp (XMinus, [x; b])]))));

    (* a < b * x ==> x > a/b (if a divides b) *)
    TS.add_simple_test
      ~title: "div"
      (fun () ->
        let r = XOp (XGt, [x; a]) in
        XA.equal_xpr r (simplify (XOp (XLt, [i10; XOp (XMult, [b; x])]))));

    (* a < x * b ==> x > a/b (if a divides b) *)
    TS.add_simple_test
      ~title: "div2"
      (fun () ->
        let r = XOp (XGt, [x; a]) in
        XA.equal_xpr r (simplify (XOp (XLt, [i10; XOp (XMult, [x; b])]))));

    TS.launch_tests ()
  end





let () =
  begin
    TS.new_testfile testname lastupdated;
    basic ();
    reduce_plus ();
    reduce_minus ();
    reduce_mult ();
    reduce_div ();
    reduce_mod ();
    reduce_xlsb ();
    reduce_xlsh ();
    reduce_lt ();
    TS.exit_file ()
  end

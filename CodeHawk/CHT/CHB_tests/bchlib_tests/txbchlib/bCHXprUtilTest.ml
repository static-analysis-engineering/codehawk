(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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


module XA = TCHXprlibAssertion
module XG = TCHXprlibGenerator
module XBA = TCHBchlibAssertion
module TS = TCHTestSuite

module X = BCHXprUtil

let testname = "bCHXprUtilTest"
let lastupdated = "2024-08-21"


let array_index_offset_test () =
  let xv = XVar (XG.mk_var "v") in
  begin

    TS.new_testsuite (testname ^ "_array_index_offset_test") lastupdated;

    (* n, 1-> (n, 0) *)
    TS.add_simple_test
      ~title:"constant"
      (fun () ->
        XBA.equal_array_index_offset
          ~expected: (Some ((XG.mk_ix 12), numerical_zero))
          ~received: (X.get_array_index_offset (XG.mk_ix 12) 1)
          ());

    (* v, 1 -> (v, 0) *)
    TS.add_simple_test
      ~title:"variable"
      (fun () ->
        XBA.equal_array_index_offset
          ~expected: (Some (xv, numerical_zero))
          ~received: (X.get_array_index_offset xv 1)
          ());

    (* x, 1 -> (x, 0) *)
    TS.add_simple_test
      ~title:"expr"
      (fun () ->
        let x = XOp (XMult, [XG.mk_ix 12; XVar (XG.mk_var "v")]) in
        XBA.equal_array_index_offset
          ~expected: (Some (x, numerical_zero))
          ~received: (X.get_array_index_offset x 1)
          ());

    (* 12, 2 -> (6, 0) *)
    TS.add_simple_test
      ~title:"constant-ds"
      (fun () ->
        XBA.equal_array_index_offset
          ~expected: (Some ((XG.mk_ix 6), numerical_zero))
          ~received: (X.get_array_index_offset (XG.mk_ix 12) 2)
          ());

    (* 12, 2 -> (6, 0) *)
    TS.add_simple_test
      ~title:"constant-ds-rem"
      (fun () ->
        XBA.equal_array_index_offset
          ~expected: (Some ((XG.mk_ix 6), numerical_one))
          ~received: (X.get_array_index_offset (XG.mk_ix 13) 2)
          ());

    (* 2v, 2 -> (v, 0) *)
    TS.add_simple_test
      ~title:"variable-ds"
      (fun () ->
        let x = XOp (XMult, [XG.mk_ix 2; xv]) in
        XBA.equal_array_index_offset
          ~expected: (Some (xv, numerical_zero))
          ~received: (X.get_array_index_offset x 2)
          ());

    (* 2v + 1, 2 -> (v, 1) *)
    TS.add_simple_test
      ~title:"variable-ds-rem"
      (fun () ->
        let x = XOp (XPlus, [XOp (XMult, [XG.mk_ix 2; xv]); XG.mk_ix 1]) in
        XBA.equal_array_index_offset
          ~expected: (Some (xv, numerical_one))
          ~received: (X.get_array_index_offset x 2)
          ());

    (* 2v + 5, 2 -> (v+2, 1) *)
    TS.add_simple_test
      ~title:"variable-dsp-rem"
      (fun () ->
        let x = XOp (XPlus, [XOp (XMult, [XG.mk_ix 2; xv]); XG.mk_ix 5]) in
        XBA.equal_array_index_offset
          ~expected: (Some (XOp (XPlus, [xv; XG.mk_ix 2]), numerical_one))
          ~received: (X.get_array_index_offset x 2)
          ());

    (* 2v + 1, 3 -> None *)
    TS.add_simple_test
      ~title:"variable-none"
      (fun () ->
        let x = XOp (XPlus, [XOp (XMult, [XG.mk_ix 2; xv]); XG.mk_ix 1]) in
        XBA.equal_array_index_offset
          ~expected: None
          ~received: (X.get_array_index_offset x 3)
          ());

    (* 2v - 3, 2 -> (v-2, 1) *)
    TS.add_simple_test
      ~title:"variable-dps-min"
      (fun () ->
        let x = XOp (XMinus, [XOp (XMult, [XG.mk_ix 2; xv]); XG.mk_ix 3]) in
        XBA.equal_array_index_offset
          ~expected: (Some (XOp (XMinus, [xv; XG.mk_ix 2]), numerical_one))
          ~received: (X.get_array_index_offset x 2)
          ());

    (* 68v - 68, 68 -> (v-1, 0) *)
    TS.add_simple_test
      ~title:"variable-dps-min-zero"
      (fun () ->
        let x = XOp (XMinus, [XOp (XMult, [XG.mk_ix 68; xv]); XG.mk_ix 68]) in
        XBA.equal_array_index_offset
          ~expected: (Some (XOp (XMinus, [xv; XG.mk_ix 1]), numerical_zero))
          ~received: (X.get_array_index_offset x 68)
          ());

    (* 68v - 68, 60 -> (v-1, 8) *)
    TS.add_simple_test
      ~title:"variable-dps-min-eight"
      (fun () ->
        let x = XOp (XMinus, [XOp (XMult, [XG.mk_ix 68; xv]); XG.mk_ix 60]) in
        XBA.equal_array_index_offset
          ~expected: (Some (XOp (XMinus, [xv; XG.mk_ix 1]), mkNumerical 8))
          ~received: (X.get_array_index_offset x 68)
          ());

    (* ((((0x4 * v) + g_data_array) + (0x40 * v)) - 0x40) *)
    TS.add_simple_test
      ~title:"variable-simp"
      (fun () ->
        let xdata = XVar (XG.mk_var "data") in
        let x1 = XOp (XMult, [XG.mk_ix 4; xv]) in
        let x2 = XOp (XPlus, [x1; xdata]) in
        let x3 = XOp (XPlus, [x2; XOp (XMult, [XG.mk_ix 64; xv])]) in
        let x4 = XOp (XMinus, [x3; XG.mk_ix 64]) in
        let x5 = XOp (XMinus, [x4; xdata]) in
        let x = simplify_xpr x5 in
        XBA.equal_array_index_offset
          ~expected: (Some (XOp (XMinus, [xv; XG.mk_ix 1]), mkNumerical 4))
          ~received: (X.get_array_index_offset x 68)
          ());

    TS.launch_tests ()

  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    array_index_offset_test ();
    TS.exit_file ()
  end

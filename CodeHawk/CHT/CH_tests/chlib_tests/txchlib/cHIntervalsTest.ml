(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026      Aarno Labs LLC

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

(* Division in the non-relational numerical domains. CHIF DIV is division
   truncated toward zero (C11 6.5.5p6, ARM sdiv/udiv, Java idiv): issues
   31b and 33 in the CodeHawk-C issues list. *)

(* chlib *)
open CHBounds
open CHConstants
open CHIntervals
open CHNumerical
open CHStridedIntervals
open CHTIntervals

(* chutil *)
open CHPrettyUtil

module A = TCHAssertion
module TS = TCHTestSuite


let testname = "cHIntervalsTest"
let lastupdated = "2026-11-14"

let n = mkNumerical
let iv lo hi = mkInterval (n lo) (n hi)
let b i = bound_of_num (n i)

let equal_pretty expected p =
  A.equal_string expected (pretty_to_string p)


let bound_div_trunc () =
  begin
    TS.new_testsuite (testname ^ "_bound_div_trunc") lastupdated;

    TS.add_simple_test
      ~title:"pos-pos"
      (fun () -> equal_pretty "3" ((b 7)#div_trunc (b 2))#toPretty);

    TS.add_simple_test
      ~title:"neg-pos"
      (fun () -> equal_pretty "-3" ((b (-7))#div_trunc (b 2))#toPretty);

    TS.add_simple_test
      ~title:"pos-neg"
      (fun () -> equal_pretty "-3" ((b 7)#div_trunc (b (-2)))#toPretty);

    TS.add_simple_test
      ~title:"neg-neg"
      (fun () -> equal_pretty "3" ((b (-7))#div_trunc (b (-2)))#toPretty);

    TS.add_simple_test
      ~title:"num-inf"
      (fun () -> equal_pretty "0" ((b (-7))#div_trunc plus_inf_bound)#toPretty);

    TS.add_simple_test
      ~title:"inf-neg"
      (fun () -> equal_pretty "-oo" (plus_inf_bound#div_trunc (b (-3)))#toPretty);

    TS.launch_tests ()
  end


let interval_div () =
  begin
    TS.new_testsuite (testname ^ "_interval_div") lastupdated;

    (* u in [0, 100]: u / 16 in [0, 6] (was [0, 7]) *)
    TS.add_simple_test
      ~title:"nonneg-exact-upper"
      (fun () -> equal_pretty "[0; 6]" ((iv 0 100)#div (iv 16 16))#toPretty);

    (* [-7, 9] / [2, 3] = [-3, 4] (was [-4, 5]) *)
    TS.add_simple_test
      ~title:"mixed-sign-dividend"
      (fun () -> equal_pretty "[-3; 4]" ((iv (-7) 9)#div (iv 2 3))#toPretty);

    (* [-7, -1] / [2, 3] = [-3, 0] *)
    TS.add_simple_test
      ~title:"negative-dividend"
      (fun () -> equal_pretty "[-3; 0]" ((iv (-7) (-1))#div (iv 2 3))#toPretty);

    (* [-7, 9] / [-3, -2] = [-4, 3] *)
    TS.add_simple_test
      ~title:"negative-divisor"
      (fun () ->
        equal_pretty "[-4; 3]" ((iv (-7) 9)#div (iv (-3) (-2)))#toPretty);

    (* [-7, -7] / [2, 2] = [-3, -3] (C: -7 / 2 == -3) *)
    TS.add_simple_test
      ~title:"singleton-truncation"
      (fun () -> equal_pretty "[-3; -3]" ((iv (-7) (-7))#div (iv 2 2))#toPretty);

    (* [-5, +oo] / [2, +oo] = [-2, +oo] *)
    TS.add_simple_test
      ~title:"infinite-bounds"
      (fun () ->
        let x = topInterval#lowerBound (b (-5)) in
        let y = topInterval#lowerBound (b 2) in
        equal_pretty "[-2; +oo]" (x#div y)#toPretty);

    (* [5, +oo] / [-oo, -1] = [-oo, 0] *)
    TS.add_simple_test
      ~title:"infinite-bounds-negative-divisor"
      (fun () ->
        let x = topInterval#lowerBound (b 5) in
        let y = topInterval#upperBound (b (-1)) in
        equal_pretty "[-oo; 0]" (x#div y)#toPretty);

    (* divisor containing zero: top *)
    TS.add_simple_test
      ~title:"divisor-contains-zero"
      (fun () -> equal_pretty "[-oo; +oo]" ((iv 1 10)#div (iv (-1) 1))#toPretty);

    (* exhaustive check against OCaml (truncating) integer division *)
    TS.add_simple_test
      ~title:"exhaustive-small"
      (fun () ->
        let r = List.init 13 (fun i -> i - 6) in
        List.iter (fun a1 ->
          List.iter (fun a2 ->
            if a1 <= a2 then
              List.iter (fun d1 ->
                List.iter (fun d2 ->
                  if d1 <= d2 && (d2 < 0 || d1 > 0) then
                    let qs = ref [] in
                    begin
                      for x = a1 to a2 do
                        for y = d1 to d2 do
                          qs := (x / y) :: !qs  (* OCaml / truncates *)
                        done
                      done;
                      let lo = List.fold_left min max_int !qs in
                      let hi = List.fold_left max min_int !qs in
                      equal_pretty
                        ("[" ^ string_of_int lo ^ "; " ^ string_of_int hi ^ "]")
                        ((iv a1 a2)#div (iv d1 d2))#toPretty
                    end) r) r) r) r);

    TS.launch_tests ()
  end


let tinterval_div () =
  begin
    TS.new_testsuite (testname ^ "_tinterval_div") lastupdated;

    TS.add_simple_test
      ~title:"mixed-sign-dividend"
      (fun () ->
        equal_pretty "[-3; 4]"
          ((mkTInterval (n (-7)) (n 9))#div (mkTInterval (n 2) (n 3)))#toPretty);

    TS.launch_tests ()
  end


let strided_interval_div () =
  begin
    TS.new_testsuite (testname ^ "_strided_interval_div") lastupdated;

    (* {1, 9, 17} / 4 = {0, 2, 4} *)
    TS.add_simple_test
      ~title:"nonneg-stride-kept"
      (fun () ->
        let r = (mkStridedIntervalN 1 17 8 1)#div (mkSingletonStridedIntervalN 4) in
        begin
          equal_pretty "0" r#getMin#toPretty;
          equal_pretty "4" r#getMax#toPretty;
          equal_pretty "2" r#getStride#toPretty;
          equal_pretty "0" r#getRem#toPretty
        end);

    (* {-7, 1, 9} / 4 = {-1, 0, 2}: no stride (was stride 2, unsound) *)
    TS.add_simple_test
      ~title:"crossing-zero-no-stride"
      (fun () ->
        let r = (mkStridedIntervalN (-7) 9 8 1)#div (mkSingletonStridedIntervalN 4) in
        begin
          equal_pretty "-1" r#getMin#toPretty;
          equal_pretty "2" r#getMax#toPretty;
          equal_pretty "1" r#getStride#toPretty
        end);

    (* {-23, -15, -7} / 4 = {-5, -3, -1} *)
    TS.add_simple_test
      ~title:"nonpos-stride-kept"
      (fun () ->
        let r = (mkStridedIntervalN (-23) (-7) 8 1)#div (mkSingletonStridedIntervalN 4) in
        begin
          equal_pretty "-5" r#getMin#toPretty;
          equal_pretty "-1" r#getMax#toPretty;
          equal_pretty "2" r#getStride#toPretty;
          equal_pretty "1" r#getRem#toPretty
        end);

    (* {1, 9, 17} / -4 = {-4, -2, 0} (stride was negative) *)
    TS.add_simple_test
      ~title:"negative-divisor"
      (fun () ->
        let r = (mkStridedIntervalN 1 17 8 1)#div (mkSingletonStridedIntervalN (-4)) in
        begin
          equal_pretty "-4" r#getMin#toPretty;
          equal_pretty "0" r#getMax#toPretty;
          equal_pretty "2" r#getStride#toPretty;
          equal_pretty "0" r#getRem#toPretty
        end);

    (* {-7, 1, 9} / -1 = {-9, -1, 7} *)
    TS.add_simple_test
      ~title:"unit-divisor-crossing-zero"
      (fun () ->
        let r = (mkStridedIntervalN (-7) 9 8 1)#div (mkSingletonStridedIntervalN (-1)) in
        begin
          equal_pretty "-9" r#getMin#toPretty;
          equal_pretty "7" r#getMax#toPretty;
          equal_pretty "8" r#getStride#toPretty;
          equal_pretty "7" r#getRem#toPretty
        end);

    (* exhaustive soundness check: every quotient x / d (OCaml truncation) of
       a member x is a member of the result, and the bounds are exact *)
    TS.add_simple_test
      ~title:"exhaustive-small"
      (fun () ->
        let to_int bd = match bd#getBound with
          | NUMBER v -> v#toInt | _ -> A.fail_msg "infinite bound" in
        for lo = -20 to 20 do
          for st = 1 to 12 do
            for rm = 0 to st - 1 do
              for k = 0 to 3 do
                for d = -6 to 6 do
                  if d <> 0 then
                    let hi = lo + k * st in
                    let si = mkStridedIntervalN lo hi st rm in
                    if not si#isBottom then
                      let r = si#div (mkSingletonStridedIntervalN d) in
                      let (rlo, rhi) = (to_int r#getMin, to_int r#getMax) in
                      let (rst, rrm) = (r#getStride#toInt, r#getRem#toInt) in
                      let (slo, shi) = (to_int si#getMin, to_int si#getMax) in
                      let sst = si#getStride#toInt in
                      let qs = ref [] in
                      let x = ref slo in
                      begin
                        while !x <= shi do
                          qs := (!x / d) :: !qs;
                          x := !x + sst
                        done;
                        List.iter (fun q ->
                            if q < rlo || q > rhi
                               || ((q - rrm) mod rst + rst) mod rst <> 0 then
                              A.fail_msg
                                (Printf.sprintf
                                   "{%d..%d, %d} / %d: %d not in %s"
                                   slo shi sst d q
                                   (pretty_to_string r#toPretty))) !qs;
                        A.equal_string
                          (string_of_int (List.fold_left min max_int !qs))
                          (string_of_int rlo);
                        A.equal_string
                          (string_of_int (List.fold_left max min_int !qs))
                          (string_of_int rhi)
                      end
                done
              done
            done
          done
        done);

    TS.launch_tests ()
  end


let constant_div () =
  begin
    TS.new_testsuite (testname ^ "_constant_div") lastupdated;

    (* -7 DIV 2 = -3 (was top) *)
    TS.add_simple_test
      ~title:"negative-dividend"
      (fun () ->
        equal_pretty "-3"
          ((mkNumericalConstant (n (-7)))#div (mkNumericalConstant (n 2)))#toPretty);

    (* division by the constant zero: top *)
    TS.add_simple_test
      ~title:"divide-by-zero"
      (fun () ->
        equal_pretty "T"
          ((mkNumericalConstant (n 7))#div (mkNumericalConstant (n 0)))#toPretty);

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    bound_div_trunc ();
    interval_div ();
    tinterval_div ();
    strided_interval_div ();
    constant_div ();
    TS.exit_file ()
  end

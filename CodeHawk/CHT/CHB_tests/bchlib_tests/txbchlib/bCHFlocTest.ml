(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024-2025  Aarno Labs LLC

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
open Xprt
open XprTypes

(* bchlib *)
open BCHBCFiles
open BCHBCTypes
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHLibTypes

(* bchcil *)
open BCHParseCilFile

module A = TCHAssertion
module TR = CHTraceResult
module TS = TCHTestSuite
module XBA = TCHBchlibAssertion

let mmap = BCHGlobalMemoryMap.global_memory_map


let testname = "bCHFlocTest"
let lastupdated = "2025-08-19"


let get_var_at_address_test () =
  let secaddr = TR.tget_ok (string_to_doubleword "0x500000") in
  let secsize = TR.tget_ok (string_to_doubleword "0x100000") in
  let _ =  mmap#set_section ~readonly:false ~initialized:false ".bss" secaddr secsize in
  let faddr = "0x1d6bfc" in
  let iaddr = "0x1d6cbc" in
  let gvaddr = "0x5e1e1c" in
  let dwfaddr = TR.tget_ok (string_to_doubleword faddr) in
  let dwiaddr = TR.tget_ok (string_to_doubleword iaddr) in
  let dwgvaddr = TR.tget_ok (string_to_doubleword gvaddr) in
  let loc = BCHLocation.make_location_by_address dwfaddr dwiaddr in
  let dwgvxpr = num_constant_expr dwgvaddr#to_numerical in
  begin
    TS.new_testsuite
      (testname ^ "_get_var_at_address_test") lastupdated;

    parse_cil_file ~removeUnused:false "decompose_array_address.i";
    ignore (functions_data#add_function dwfaddr);
    let compinfo = bcfiles#get_compinfo_by_name "x44_struct_t" in
    let finfo = get_function_info dwfaddr in
    let floc = get_floc_by_address dwfaddr dwiaddr in
    let gvar = TR.tget_ok (finfo#env#mk_global_variable loc dwgvaddr#to_numerical) in
    let indexvar = finfo#env#mk_initial_register_value (ARMRegister AR0) in
    let indexxpr1 = XOp (XMinus, [XVar indexvar; int_constant_expr 1]) in

    TS.add_simple_test
      ~title:"constant-68"
      (fun () ->
        let xpr = XOp (XPlus, [dwgvxpr; int_constant_expr 68]) in
        let xpr = Xsimplify.simplify_xpr xpr in
        let xprvar = floc#get_var_at_address ~btype:BCHBCTypeUtil.t_int xpr in
        let xpoffset = FieldOffset (("field0", compinfo.bckey), NoOffset) in
        let xpoffset = ArrayIndexOffset(int_constant_expr 1, xpoffset) in
        let expected_r = finfo#env#add_memory_offset gvar xpoffset in
        let expected = TR.to_option expected_r in
        match xprvar with
          Ok received ->
           XBA.equal_opt_variable
             ~expected
             ~received:(Some received)
             ()
        | Error e -> A.fail_msg ("Error: " ^ (String.concat "; " e)));

    TS.add_simple_test
      ~title:"constant-72"
      (fun () ->
        let xpr = XOp (XPlus, [dwgvxpr; int_constant_expr 72]) in
        let xpr = Xsimplify.simplify_xpr xpr in
        let xprvar = floc#get_var_at_address ~btype:BCHBCTypeUtil.t_int xpr in
        let xpoffset = FieldOffset (("field4", compinfo.bckey), NoOffset) in
        let xpoffset = ArrayIndexOffset(int_constant_expr 1, xpoffset) in
        let expected_r = finfo#env#add_memory_offset gvar xpoffset in
        let expected = TR.to_option expected_r in
        match xprvar with
          Ok received ->
          XBA.equal_opt_variable
            ~expected
            ~received:(Some received)
            ()
        | Error e -> A.fail_msg ("Error: " ^ (String.concat "; " e)));

    TS.add_simple_test
      ~title:"var-68"
      (fun () ->
        let xpr =
          XOp (XPlus, [dwgvxpr;
                       XOp (XMult, [int_constant_expr 68; XVar indexvar])]) in
        let xprvar = floc#get_var_at_address ~btype:BCHBCTypeUtil.t_int xpr in
        let xpoffset = FieldOffset (("field0", compinfo.bckey), NoOffset) in
        let xpoffset = ArrayIndexOffset(XVar indexvar, xpoffset) in
        let expected_r = finfo#env#add_memory_offset gvar xpoffset in
        let expected = TR.to_option expected_r in
        match xprvar with
        | Ok received ->
          XBA.equal_opt_variable
            ~expected
            ~received:(Some received)
            ()
        | Error e -> A.fail_msg ("Error: " ^ (String.concat "; " e)));


    TS.add_simple_test
      ~title:"varm1-68"
      (fun () ->
        let subxpr = XOp (XMult, [int_constant_expr 68; XVar indexvar]) in
        let subxpr = XOp (XMinus, [subxpr; int_constant_expr 68]) in
        let xpr = XOp (XPlus, [dwgvxpr; subxpr]) in
        let xprvar = floc#get_var_at_address ~btype:BCHBCTypeUtil.t_int xpr in
        let xpoffset = FieldOffset (("field0", compinfo.bckey), NoOffset) in
        let xpoffset = ArrayIndexOffset(indexxpr1, xpoffset) in
        let expected_r = finfo#env#add_memory_offset gvar xpoffset in
        let expected = TR.to_option expected_r in
        match xprvar with
        | Ok received ->
           XBA.equal_opt_variable
             ~expected
             ~received:(Some received)
             ()
        | Error e -> A.fail_msg ("Error: " ^ (String.concat "; " e)));

    TS.add_simple_test
      ~title:"varm1-64"
      (fun () ->
        let subxpr = XOp (XMult, [int_constant_expr 68; XVar indexvar]) in
        let subxpr = XOp (XMinus, [subxpr; int_constant_expr 64]) in
        let xpr = XOp (XPlus, [dwgvxpr; subxpr]) in
        let xprvar = floc#get_var_at_address ~btype:BCHBCTypeUtil.t_int xpr in
        let xpoffset = FieldOffset (("field4", compinfo.bckey), NoOffset) in
        let xpoffset = ArrayIndexOffset(indexxpr1, xpoffset) in
        let expected_r = finfo#env#add_memory_offset gvar xpoffset in
        let expected = TR.to_option expected_r in
        match xprvar with
        | Ok received ->
           XBA.equal_opt_variable
             ~expected
             ~received:(Some received)
             ()
        | Error e -> A.fail_msg ("Error: " ^ (String.concat "; " e)));

    TS.add_simple_test
      ~title:"varm1-60"
      (fun () ->
        let subxpr = XOp (XMult, [int_constant_expr 68; XVar indexvar]) in
        let subxpr = XOp (XMinus, [subxpr; int_constant_expr 60]) in
        let xpr = XOp (XPlus, [dwgvxpr; subxpr]) in
        let xprvar = floc#get_var_at_address ~btype:BCHBCTypeUtil.t_char xpr in
        let xpoffset = ArrayIndexOffset (int_constant_expr 0, NoOffset) in
        let xpoffset = FieldOffset (("buffer", compinfo.bckey), xpoffset) in
        let xpoffset = ArrayIndexOffset(indexxpr1, xpoffset) in
        let expected_r = finfo#env#add_memory_offset gvar xpoffset in
        let expected = TR.to_option expected_r in
        match xprvar with
        | Ok received ->
           XBA.equal_opt_variable
             ~expected
             ~received:(Some received)
             ()
        | Error e -> A.fail_msg ("Error: " ^ (String.concat "; " e)));

    (* (((g_data_array + (0x4 * R0_in[4]_in)) + (0x40 * R0_in[4]_in)) - 0x40)) *)

    TS.add_simple_test
      ~title:"varm1s-60"
      (fun () ->
        let subxpr1 = XOp (XMult, [int_constant_expr 4; XVar indexvar]) in
        let subxpr2 = XOp (XMult, [int_constant_expr 64; XVar indexvar]) in
        let xpr = XOp (XPlus, [dwgvxpr; subxpr1]) in
        let xpr = XOp (XPlus, [xpr; subxpr2]) in
        let xpr = XOp (XMinus, [xpr; int_constant_expr 64]) in
        let xprvar = floc#get_var_at_address xpr in
        let xpoffset = FieldOffset (("field4", compinfo.bckey), NoOffset) in
        let xpoffset = ArrayIndexOffset(indexxpr1, xpoffset) in
        let expected_r = finfo#env#add_memory_offset gvar xpoffset in
        let expected = TR.to_option expected_r in
        match xprvar with
        | Ok received ->
           XBA.equal_opt_variable
             ~expected
             ~received:(Some received)
             ()
        | Error e -> A.fail_msg ("Error: " ^ (String.concat "; " e)));

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    get_var_at_address_test ();
    TS.exit_file ()
  end

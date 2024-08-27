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
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHBCFiles
open BCHBCTypes
open BCHConstantDefinitions
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHLibTypes
open BCHMemoryReference

(* bchcil *)
open BCHParseCilFile

module TR = CHTraceResult
module TS = TCHTestSuite
module XBA = TCHBchlibAssertion


let testname = "bCHFlocTest"
let lastupdated = "2024-08-20"


let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)


let decompose_array_address_test () =
  let faddr = "0x1d6bfc" in
  let iaddr = "0x1d6cbc" in
  let gvaddr = "0x5e1e1c" in
  let dwfaddr = TR.tget_ok (string_to_doubleword faddr) in
  let dwiaddr = TR.tget_ok (string_to_doubleword iaddr) in
  let dwgvaddr = TR.tget_ok (string_to_doubleword gvaddr) in
  let gvname = "x44_array" in
  begin
    TS.new_testsuite
      (testname ^ "_decompose_array_address_test") lastupdated;

    parse_cil_file ~removeUnused:false "decompose_array_address.i";
    ignore (functions_data#add_function dwfaddr);

    let arraysym = {
        xconst_name = gvname;
        xconst_value = dwgvaddr;
        xconst_type =
          if bcfiles#has_varinfo gvname then
            let vinfo = bcfiles#get_varinfo gvname in
            vinfo.bvtype
          else
            raise
              (Invalid_argument "Error in arraysym");
        xconst_desc = "decompose_array_address";
        xconst_is_addr = true
      } in
    let _ = add_address arraysym in
    let compinfo = bcfiles#get_compinfo_by_name "x44_struct_t" in

    let finfo = get_function_info dwfaddr in
    let floc = get_floc_by_address dwfaddr dwiaddr in
    let ty = get_symbolic_address_type_by_name gvname in
    let basevar =
      finfo#env#mk_global_memory_address
        ~optname:(Some gvname) ~opttype:(Some ty) dwgvaddr#to_numerical in
    let memref = TR.tget_ok (floc#f#env#mk_base_variable_reference basevar) in
    let indexvar = finfo#env#mk_initial_register_value (ARMRegister AR0) in
    let indexxpr1 = XOp (XMinus, [XVar indexvar; int_constant_expr 1]) in

    TS.add_simple_test
      ~title:"constant-68"
      (fun () ->
        let xpr = XOp (XPlus, [XVar basevar; int_constant_expr 68]) in
        let xpsuboffset = FieldOffset (("field0", compinfo.bckey), NoOffset) in
        let xpmemoffset = ArrayIndexOffset(int_constant_expr 1, xpsuboffset) in
        let optmeminfo = floc#decompose_array_address xpr in
        XBA.equal_opt_meminfo
          ~expected: (Some (memref, xpmemoffset))
          ~received: optmeminfo
          ());

    TS.add_simple_test
      ~title:"constant-72"
      (fun () ->
        let xpr = XOp (XPlus, [XVar basevar; int_constant_expr 72]) in
        let xpsuboffset = FieldOffset (("field4", compinfo.bckey), NoOffset) in
        let xpmemoffset = ArrayIndexOffset(int_constant_expr 1, xpsuboffset) in
        let optmeminfo = floc#decompose_array_address xpr in
        XBA.equal_opt_meminfo
          ~expected: (Some (memref, xpmemoffset))
          ~received: optmeminfo
          ());

    TS.add_simple_test
      ~title:"var-68"
      (fun () ->
        let xpr =
          XOp (XPlus, [XVar basevar;
                       XOp (XMult, [int_constant_expr 68; XVar indexvar])]) in
        let xpsuboffset = FieldOffset (("field0", compinfo.bckey), NoOffset) in
        let xpmemoffset = ArrayIndexOffset(XVar indexvar, xpsuboffset) in
        let optmeminfo = floc#decompose_array_address xpr in
        XBA.equal_opt_meminfo
          ~expected: (Some (memref, xpmemoffset))
          ~received: optmeminfo
          ());

    TS.add_simple_test
      ~title:"varm1-68"
      (fun () ->
        let subxpr = XOp (XMult, [int_constant_expr 68; XVar indexvar]) in
        let subxpr = XOp (XMinus, [subxpr; int_constant_expr 68]) in
        let xpr = XOp (XPlus, [XVar basevar; subxpr]) in
        let xpsuboffset = FieldOffset (("field0", compinfo.bckey), NoOffset) in
        let xpmemoffset = ArrayIndexOffset(indexxpr1, xpsuboffset) in
        let optmeminfo = floc#decompose_array_address xpr in
        XBA.equal_opt_meminfo
          ~expected: (Some (memref, xpmemoffset))
          ~received: optmeminfo
          ());

    TS.add_simple_test
      ~title:"varm1-64"
      (fun () ->
        let subxpr = XOp (XMult, [int_constant_expr 68; XVar indexvar]) in
        let subxpr = XOp (XMinus, [subxpr; int_constant_expr 64]) in
        let xpr = XOp (XPlus, [XVar basevar; subxpr]) in
        let xpsuboffset = FieldOffset (("field4", compinfo.bckey), NoOffset) in
        let xpmemoffset = ArrayIndexOffset(indexxpr1, xpsuboffset) in
        let optmeminfo = floc#decompose_array_address xpr in
        XBA.equal_opt_meminfo
          ~expected: (Some (memref, xpmemoffset))
          ~received: optmeminfo
          ());

    TS.add_simple_test
      ~title:"varm1-60"
      (fun () ->
        let subxpr = XOp (XMult, [int_constant_expr 68; XVar indexvar]) in
        let subxpr = XOp (XMinus, [subxpr; int_constant_expr 60]) in
        let xpr = XOp (XPlus, [XVar basevar; subxpr]) in
        let xpsuboffset = ConstantOffset (numerical_zero, NoOffset) in
        let xpsuboffset = FieldOffset (("buffer", compinfo.bckey), xpsuboffset) in
        let xpmemoffset = ArrayIndexOffset(indexxpr1, xpsuboffset) in
        let optmeminfo = floc#decompose_array_address xpr in
        XBA.equal_opt_meminfo
          ~expected: (Some (memref, xpmemoffset))
          ~received: optmeminfo
          ());

    (* (((g_data_array + (0x4 * R0_in[4]_in)) + (0x40 * R0_in[4]_in)) - 0x40)) *)

    TS.add_simple_test
      ~title:"varm1s-60"
      (fun () ->
        let subxpr1 = XOp (XMult, [int_constant_expr 4; XVar indexvar]) in
        let subxpr2 = XOp (XMult, [int_constant_expr 64; XVar indexvar]) in
        let xpr = XOp (XPlus, [XVar basevar; subxpr1]) in
        let xpr = XOp (XPlus, [xpr; subxpr2]) in
        let xpr = XOp (XMinus, [xpr; int_constant_expr 64]) in
        let xpsuboffset = FieldOffset (("field4", compinfo.bckey), NoOffset) in
        let xpmemoffset = ArrayIndexOffset(indexxpr1, xpsuboffset) in
        let optmeminfo = floc#decompose_array_address xpr in
        XBA.equal_opt_meminfo
          ~expected: (Some (memref, xpmemoffset))
          ~received: optmeminfo
          ());

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    decompose_array_address_test ();
    TS.exit_file ()
  end

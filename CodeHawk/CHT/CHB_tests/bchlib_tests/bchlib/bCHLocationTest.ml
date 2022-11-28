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

(* bchlib *)
open BCHLibTypes

(* tchlib *)
module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

(* tbchlib *)
module BA = TCHBchlibAssertion
module BG = TCHBchlibGenerator
module BS = TCHBchlibSpecification

(* chlib *)
module P = CHPretty

(* bchlib *)
module B = BCHBasicTypes
module D = BCHDoubleword
module L = BCHLocation


let testname = "bCHLocationTest"
let lastupdated = "2022-11-28"


let make_dw = D.string_to_doubleword


let c = String.concat "_"


let rec fc (lst: string list) =
  match lst with
  | [] -> ""
  | [s] -> s
  | [s1; s2] -> "F:" ^ (c lst)
  | s1 :: tl -> "F:" ^ s1 ^ "_" ^ (fc tl)
              

let faddr1 = "0x401000"
let iaddr11 = "0x401105"
let iaddr12 = "0x40110a"

let faddr2 = "0x403000"
let iaddr21 = "0x403005"
let iaddr22 = "0x403009"

let faddr3 = "0x405000"
let iaddr31 = "0x405005"
let iaddr32 = "0x405009"


let baseloc =
  L.make_location
    ~ctxt:[]
    {loc_faddr = make_dw faddr1; loc_iaddr = make_dw iaddr11}


let cloc =
  L.make_c_location
    baseloc
    (FunctionContext
       {ctxt_faddr = make_dw faddr2;
        ctxt_callsite = make_dw iaddr21;
        ctxt_returnsite = make_dw iaddr22})


let loc_basic () =
  begin
    TS.new_testsuite (testname ^ "_basic") lastupdated;

    TS.add_simple_test
      (fun () -> A.equal_string baseloc#ci (c [iaddr11]));

    TS.add_simple_test
      (fun () ->
        let iloc = L.make_i_location baseloc (make_dw iaddr12) in
        A.equal_string iloc#ci (c [iaddr12]));

    TS.add_simple_test
      (fun () -> A.equal_string cloc#ci (fc [iaddr21; iaddr11]));

    TS.add_simple_test
      (fun () ->
        let s = cloc#ci in
        let loc = L.ctxt_string_to_location (make_dw faddr2) s in
        A.equal_string loc#ci s);

    TS.add_simple_test
      (fun () ->
        let s = cloc#ci in
        let loc = L.ctxt_string_to_location (make_dw faddr2) s in
        BA.equal_location cloc loc);

    TS.add_simple_test
      (fun () ->
        let s = cloc#ci in
        let s2 =
          L.add_ctxt_to_ctxt_string
            (make_dw faddr2)
            s
            (FunctionContext
               {ctxt_faddr = make_dw faddr3;
                ctxt_callsite = make_dw iaddr31;
                ctxt_returnsite = make_dw iaddr32}) in
        A.equal_string s2 (fc [iaddr31; iaddr21; iaddr11]));

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    loc_basic ();
    TS.exit_file ()
  end

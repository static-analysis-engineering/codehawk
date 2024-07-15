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


let testname = "bCHTypeConstraintStoreTest"
let lastupdated = "2024-07-10"

(* chlib *)
open CHPretty

(* bchlib *)
open BCHBasicTypes
open BCHBCFiles
open BCHBCTypePretty
open BCHCPURegisters
open BCHFunctionInterface
open BCHLibTypes
open BCHSystemSettings
open BCHTypeConstraintStore

(* bchcil *)
open BCHParseCilFile

module TS = TCHTestSuite

module A = TCHAssertion



let get_fintf (f: string): function_interface_t =
  let bvinfo =
    if bcfiles#has_varinfo f then
      bcfiles#get_varinfo f
    else
      raise
        (BCH_failure (LBLOCK [STR "Function name "; STR f; STR " not found"])) in
  bvarinfo_to_function_interface bvinfo


let arm_function_signature_type_constraints () =
  let tests = [
      ("f_1", ["t_sub_0x100.param_R0 <:> int"; "t_sub_0x100.rtn <:> int"]);
      ("f_2", ["t_sub_0x100.param_R1 <:> int";
               "t_sub_0x100.param_R0 <:> int";
               "t_sub_0x100.rtn <:> int"]);
      ("f_12", ["t_sub_0x100.param_R0.deref <:> char";
                "t_sub_0x100.rtn.deref <:> char"]);
      ("f_13", ["t_sub_0x100.param_R0.deref <:> t_struct_struct4";
                "t_sub_0x100.rtn.deref <:> char"])

    ] in
  begin
    TS.new_testsuite
      (testname ^ "_arm_function_signature_type_constraints") lastupdated;

    parse_cil_file ~removeUnused:false "header.i";
    system_settings#set_architecture "arm";

    List.iter (fun (title, expected) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let store = mk_type_constraint_store () in
            let fintf = get_fintf title in
            let _ =
              record_function_interface_type_constraints store "0x100" fintf in
            let result =
              List.map
                type_constraint_to_string
                (store#get_function_type_constraints "0x100") in
            A.make_equal_list
              (fun r1 r2 -> r1 = r2)
              (fun r -> r)
              expected
              result)) tests;

    TS.launch_tests ()

  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    arm_function_signature_type_constraints ();
    TS.exit_file ()
  end

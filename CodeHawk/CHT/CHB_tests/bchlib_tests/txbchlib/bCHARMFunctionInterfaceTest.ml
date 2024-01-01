(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023  Aarno Labs LLC

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
open BCHARMFunctionInterface
open BCHBCFiles
open BCHBCTypeUtil
open BCHCPURegisters
open BCHFtsParameter
open BCHLibTypes

(* bchcil *)
open BCHParseCilFile


let testname = "bCHARMFunctionInterfaceTest"
let lastupdated = "2023-12-30"


module A =TCHAssertion
module BA = TCHBchlibAssertion
module TS = TCHTestSuite


let get_int_param_next_state_test () =
  let regtests = [
      ("AR0", AR0, AR0, Some AR1, None);
      ("AR1", AR1, AR1, Some AR2, None);
      ("AR2", AR2, AR2, Some AR3, None);
      ("AR3", AR3, AR3, None, Some 0)
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_get_int_paramloc_next_test") lastupdated;

    List.iter (fun (title, nxtreg, xlocreg, xnxtreg, xnxtoff) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let aas = {aas_start_state with aas_next_core_reg = Some nxtreg} in
            let (par, naas) = get_int_param_next_state 4 "name" t_int aas 1 in
            let xnaas =
              {aas_start_state with
                aas_next_core_reg = xnxtreg; aas_next_offset = xnxtoff} in
            BA.equal_arm_argument_state ~expected:xnaas ~received:naas ()))
      regtests;

    TS.add_simple_test
      ~title:"stack"
      (fun () ->
        let aas =
          {aas_start_state with
            aas_next_core_reg = None; aas_next_offset = Some 0} in
        let (par, naas) = get_int_param_next_state 4 "name" t_int aas 1 in
        let xnaas = {aas with aas_next_offset = Some 4} in
        BA.equal_arm_argument_state ~expected:xnaas ~received:naas ());

    TS.add_simple_test
      ~title:"dead state"
      (fun () ->
        let aas = {aas_start_state with aas_next_core_reg = None} in
        A.raises
          ~msg:"dead state"
          (fun () -> get_int_param_next_state 4 "name" t_int aas 1));

    TS.launch_tests ()
  end


let get_arm_struct_field_locations_test () =
  (* Note: types are not checked in BA.equal_param_locations *)
  let regtests = [
      ("struct1_t", []);
      ("struct2_t", []);
      ("struct3_t", []);
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_get_arm_struct_field_locations_test") lastupdated;

    parse_cil_file ~removeUnused:false "header.i";

    List.iter (fun (title, locations) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let cinfo = bcfiles#get_compinfo_by_name title in
            let finfo = List.hd cinfo.bcfields in
            let aas = push_field_pos aas_start_state finfo in
            let (locs, naas) = get_arm_struct_field_locations finfo aas in
            let xlocs = [
                mk_register_parameter_location
                  ~position:[mk_field_position cinfo.bckey 0 (get_struct_field_name finfo)]
                  (register_of_arm_register AR0)] in
            BA.equal_param_locations ~expected:xlocs ~received:locs ())) regtests;

    TS.launch_tests ()
  end


let get_arm_struct_param_next_state_test () =
  let regtests = [
      ("struct1_t", [AR0; AR1; AR2])
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_get_arm_struct_param_next_state_test") lastupdated;

    parse_cil_file ~removeUnused:false "header.i";

    List.iter (fun (title, paramlocs) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let cinfo = bcfiles#get_compinfo_by_name title in
            let btype = get_compinfo_struct_type cinfo in
            let size = size_of_btype btype in
            let (param, naas) =
              get_arm_struct_param_next_state
                size "arg_1" btype aas_start_state 1 in
            let xlocs =
              List.map2 (fun finfo reg ->
                  let register = register_of_arm_register reg in
                  let offset = Option.get (get_struct_field_offset finfo) in
                  let fname = get_struct_field_name finfo in
                  mk_register_parameter_location
                    ~btype:(get_struct_field_type finfo)
                    ~size:(Option.get (get_struct_field_size finfo))
                    ~position:[mk_field_position cinfo.bckey offset fname]
                    register) cinfo.bcfields paramlocs in
            let xparam =
              mk_indexed_multiple_locations_parameter ~btype xlocs 1 in
            BA.equal_fts_parameter ~expected:xparam ~received:param ())) regtests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    get_int_param_next_state_test ();
    get_arm_struct_field_locations_test ();
    get_arm_struct_param_next_state_test ();
    TS.exit_file ()
  end

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
(* Unit tests for the conversion of a c-header supplied signature into a CH
   function interface, with allocation of parameters to locations (i.e.,
   registers, stack locations) depending on the architecture.

   The names of the tests refer to function signatures in the file header.i in
   this directory, which is parsed by CIL.
 *)

(* chlib *)
open CHPretty
open CHNumerical

(* tchblib *)
open TCHSpecification

(* bchlib *)
open BCHBasicTypes
open BCHBCFiles
open BCHBCTypes
open BCHFunctionInterface
open BCHLibTypes
open BCHSystemSettings
open BCHUtilities

(* bchcil *)
open BCHParseCilFile

module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

module BA = TCHBchlibAssertion
module BG = TCHBchlibGenerator
module BS = TCHBchlibSpecification
module BU = TCHBchlibUtils

module D = BCHDoubleword
module TR = CHTraceResult
module TU = BCHBCTypeUtil
module FI = BCHFunctionInterface


let testname = "bCHFunctionInterfaceTest"
let lastupdated = "2023-12-21"


let function_signature_of_bvarinfo_x86 () =
  let tests = [
      (* testspec:
         f_1: name of function declaration in file header.i
         1  : parameter index
         "i": parameter name
         TU.t_int: parameter type
         4:  parameter size
         "s": parameter location kind (stack)
         TU.t_int: type of parameter_location
         "4": offset (in bytes above initial stack pointer)
       *)
      ("f_1", [(1, "i", TU.t_int, 4, [("s", TU.t_int, "4")])]);
      ("f_2", [(1, "i", TU.t_int, 4, [("s", TU.t_int, "4")]);
               (2, "j", TU.t_int, 4, [("s", TU.t_int, "8")])]);
      ("f_3", [(1, "i", TU.t_int, 4, [("s", TU.t_int, "4")]);
               (2, "d", TU.t_double, 8, [("s", TU.t_double, "8")]);
               (3, "j", TU.t_int, 4, [("s", TU.t_int, "16")])]);
    ] in
  begin

    TS.new_testsuite
      (testname ^ "_function_signature_of_bvarinfo_x86") lastupdated;

    parse_cil_file ~removeUnused:false "header.i";

    List.iter (fun (title, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let bvinfo =
              if bcfiles#has_varinfo title then
                bcfiles#get_varinfo title
              else
                raise
                  (BCH_failure (LBLOCK [STR title; STR " not found"])) in
            let xresult = List.map BU.convert_fts_parameter_input result in
            let fintf = FI.bvarinfo_to_function_interface bvinfo in
            let tsig = fintf.fintf_type_signature in
            BA.equal_function_parameters
              ~expected:xresult
              ~received:tsig.fts_parameters ())) tests;

    TS.launch_tests()
  end


let function_signature_of_bvarinfo_arm () =
  let tests = [
      ("f_1", [(1, "i", TU.t_int, 4, [("r", TU.t_int, "R0")])]);
      ("f_2", [(1, "i", TU.t_int, 4, [("r", TU.t_int, "R0")]);
               (2, "j", TU.t_int, 4, [("r", TU.t_int, "R1")])]);
      ("f_3", [(1, "i", TU.t_int, 4, [("r", TU.t_int, "R0")]);
               (2, "d", TU.t_double, 8, [("r", TU.t_double, "D0")]);
               (3, "j", TU.t_int, 4, [("r", TU.t_int, "R1")])]);
      ("f_4", [(1, "x", TU.t_float, 4, [("r", TU.t_float, "S0")]);
               (2, "y", TU.t_float, 4, [("r", TU.t_float, "S1")]);
               (3, "z", TU.t_float, 4, [("r", TU.t_float, "S2")]);
               (4, "a", TU.t_int, 4, [("r", TU.t_int, "R0")]);
               (5, "b", TU.t_int, 4, [("r", TU.t_int, "R1")])]);
      ("f_5", [(1, "x", TU.t_float, 4, [("r", TU.t_float, "S0")]);
               (2, "y", TU.t_double, 8, [("r", TU.t_double, "D1")]);
               (3, "z", TU.t_float, 4, [("r", TU.t_float, "S1")]);
               (4, "t", TU.t_float, 4, [("r", TU.t_float, "S4")])])
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_function_signature_of_bvarinfo_arm") lastupdated;

    parse_cil_file ~removeUnused:false "header.i";
    system_settings#set_architecture "arm";

    List.iter (fun (title, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let bvinfo =
              if bcfiles#has_varinfo title then
                bcfiles#get_varinfo title
              else
                raise
                  (BCH_failure (LBLOCK [STR title; STR " not found"])) in
            let xresult = List.map BU.convert_fts_parameter_input result in
            let fintf = FI.bvarinfo_to_function_interface bvinfo in
            let tsig = fintf.fintf_type_signature in
            BA.equal_function_parameters
              ~expected:xresult
              ~received:tsig.fts_parameters ())) tests;

    TS.launch_tests ()
  end


let function_signature_of_bvarinfo_mips () =
  let tests = [
      ("f_1", [(1, "i", TU.t_int, 4, [("r", TU.t_int, "$a0")])]);
      ("f_2", [(1, "i", TU.t_int, 4, [("r", TU.t_int, "$a0")]);
               (2, "j", TU.t_int, 4, [("r", TU.t_int, "$a1")])]);
      ("f_6", [(1, "a", TU.t_int, 4, [("r", TU.t_int, "$a0")]);
               (2, "b", TU.t_int, 4, [("r", TU.t_int, "$a1")]);
               (3, "c", TU.t_int, 4, [("r", TU.t_int, "$a2")]);
               (4, "d", TU.t_int, 4, [("r", TU.t_int, "$a3")]);
               (5, "e", TU.t_int, 4, [("s", TU.t_int, "16")])])
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_function_signature_of_bvarinfo_mips") lastupdated;

    parse_cil_file ~removeUnused:false "header.i";
    system_settings#set_architecture "mips";

    List.iter (fun (title, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let bvinfo =
              if bcfiles#has_varinfo title then
                bcfiles#get_varinfo title
              else
                raise
                  (BCH_failure (LBLOCK [STR title; STR " not found"])) in
            let xresult = List.map BU.convert_fts_parameter_input result in
            let fintf = FI.bvarinfo_to_function_interface bvinfo in
            let tsig = fintf.fintf_type_signature in
            BA.equal_function_parameters
              ~expected:xresult
              ~received:tsig.fts_parameters ())) tests;

    TS.launch_tests ()
  end


let read_xml_function_interface_mips () =
  let tests = [
      ("fileno",
       [(1, "stream", TU.t_ptrto (TU.t_named "FILE"), 4,
         [("r", TU.t_ptrto (TU.t_named "FILE"), "$a0")])]);
      ("getnameinfo",
       [(1, "sa", TU.t_ptrto (TU.t_named "sockaddr"), 4,
         [("r", TU.t_ptrto (TU.t_named "sockaddr"), "$a0")]);
        (2, "salen", TU.t_named "socklen_t", 4,
         [("r", TU.t_named "socklen_t", "$a1")]);
        (3, "node", TU.t_charptr, 4, [("r", TU.t_charptr, "$a2")]);
        (4, "nodelen", TU.t_named "socklen_t", 4,
         [("r", TU.t_named "socklen_t", "$a3")]);
        (5, "service", TU.t_charptr, 4, [("s", TU.t_charptr, "16")]);
        (6, "servicelen", TU.t_named "socklen_t", 4,
         [("s", TU.t_named "socklen_t", "20")])]);
      ("memcpy",
       [(1, "dest", TU.t_voidptr, 4, [("r", TU.t_voidptr, "$a0")]);
        (2, "src", TU.t_voidptr, 4, [("r", TU.t_voidptr, "$a1")]);
        (3, "count", TU.t_named "size_t", 4,
         [("r", TU.t_named "size_t", "$a2")])]);
      ("strcpy",
       [(1, "dest", TU.t_charptr, 4, [("r", TU.t_charptr, "$a0")]);
        (2, "src", TU.t_charptr, 4, [("r", TU.t_charptr, "$a1")])])
    ] in
  let _ = system_settings#set_summary_jar "utsummaries.jar" in
  let summarypath = system_settings#get_summary_paths in
  begin
    TS.new_testsuite
      (testname ^ "_read_xml_function_interface") lastupdated;

    system_settings#set_architecture "mips";

    List.iter (fun (fname, result) ->
        TS.add_simple_test
          ~title:fname
          (fun () ->
            let filename = "so_functions/" ^ fname in
            if has_summary_file summarypath filename then
              let xresult = List.map BU.convert_fts_parameter_input result in
              let xstring = get_summary_file summarypath filename in
              let libfnode = BU.get_so_xml_summary_string_node fname xstring in
              let fapi = libfnode#getTaggedChild "api" in
              let fintf = FI.read_xml_function_interface fapi in
              let tsig = fintf.fintf_type_signature in
              BA.equal_function_parameters
                ~expected:xresult
                ~received:tsig.fts_parameters ())) tests;

    TS.launch_tests ()
  end


let read_xml_function_interface_arm () =
  let tests = [
      ("fileno",
       [(1, "stream", TU.t_ptrto (TU.t_named "FILE"), 4,
         [("r", TU.t_ptrto (TU.t_named "FILE"), "R0")])]);
      ("getnameinfo",
       [(1, "sa", TU.t_ptrto (TU.t_named "sockaddr"), 4,
         [("r", TU.t_ptrto (TU.t_named "sockaddr"), "R0")]);
        (2, "salen", TU.t_named "socklen_t", 4,
         [("r", TU.t_named "socklen_t", "R1")]);
        (3, "node", TU.t_charptr, 4, [("r", TU.t_charptr, "R2")]);
        (4, "nodelen", TU.t_named "socklen_t", 4,
         [("r", TU.t_named "socklen_t", "R3")]);
        (5, "service", TU.t_charptr, 4, [("s", TU.t_charptr, "0")]);
        (6, "servicelen", TU.t_named "socklen_t", 4,
         [("s", TU.t_named "socklen_t", "4")])]);
      ("memcpy",
       [(1, "dest", TU.t_voidptr, 4, [("r", TU.t_voidptr, "R0")]);
        (2, "src", TU.t_voidptr, 4, [("r", TU.t_voidptr, "R1")]);
        (3, "count", TU.t_named "size_t", 4,
         [("r", TU.t_named "size_t", "R2")])]);
      ("strcpy",
       [(1, "dest", TU.t_charptr, 4, [("r", TU.t_charptr, "R0")]);
        (2, "src", TU.t_charptr, 4, [("r", TU.t_charptr, "R1")])])
    ] in
  let _ = system_settings#set_summary_jar "utsummaries.jar" in
  let summarypath = system_settings#get_summary_paths in
  begin
    TS.new_testsuite
      (testname ^ "_read_xml_function_interface") lastupdated;

    system_settings#set_architecture "arm";

    List.iter (fun (fname, result) ->
        TS.add_simple_test
          ~title:fname
          (fun () ->
            let filename = "so_functions/" ^ fname in
            if has_summary_file summarypath filename then
              let xresult = List.map BU.convert_fts_parameter_input result in
              let xstring = get_summary_file summarypath filename in
              let libfnode = BU.get_so_xml_summary_string_node fname xstring in
              let fapi = libfnode#getTaggedChild "api" in
              let fintf = FI.read_xml_function_interface fapi in
              let tsig = fintf.fintf_type_signature in
              BA.equal_function_parameters
                ~expected:xresult
                ~received:tsig.fts_parameters ())) tests;

    TS.launch_tests ()
  end


let get_mips_inferred_fts_parameters () =
  let tests = [
      ("f1", [("r", TU.t_int, "$a0")], [(1, "arg_1", TU.t_int, 4, [("r", TU.t_int, "$a0")])]);
      ("f2", [("r", TU.t_int, "$a1")],
       [(1, "arg_1", TU.t_unknown, 4, [("r", TU.t_unknown, "$a0")]);
        (2, "arg_2", TU.t_int, 4, [("r", TU.t_int, "$a1")])]);
      ("f3", [("r", TU.t_int, "$a2")],
       [(1, "arg_1", TU.t_unknown, 4, [("r", TU.t_unknown, "$a0")]);
        (2, "arg_2", TU.t_unknown, 4, [("r", TU.t_unknown, "$a1")]);
        (3, "arg_3", TU.t_int, 4, [("r", TU.t_int, "$a2")])]);
      ("f4", [("r", TU.t_int, "$a3")],
       [(1, "arg_1", TU.t_unknown, 4, [("r", TU.t_unknown, "$a0")]);
        (2, "arg_2", TU.t_unknown, 4, [("r", TU.t_unknown, "$a1")]);
        (3, "arg_3", TU.t_unknown, 4, [("r", TU.t_unknown, "$a2")]);
        (4, "arg_4", TU.t_int, 4, [("r", TU.t_int, "$a3")])]);
      ("f5", [("s", TU.t_int, "16")],
       [(1, "arg_1", TU.t_unknown, 4, [("r", TU.t_unknown, "$a0")]);
        (2, "arg_2", TU.t_unknown, 4, [("r", TU.t_unknown, "$a1")]);
        (3, "arg_3", TU.t_unknown, 4, [("r", TU.t_unknown, "$a2")]);
        (4, "arg_4", TU.t_unknown, 4, [("r", TU.t_unknown, "$a3")]);
        (5, "arg_5", TU.t_int, 4, [("s", TU.t_int, "16")])]);
      ("f6", [("s", TU.t_int, "20")],
       [(1, "arg_1", TU.t_unknown, 4, [("r", TU.t_unknown, "$a0")]);
        (2, "arg_2", TU.t_unknown, 4, [("r", TU.t_unknown, "$a1")]);
        (3, "arg_3", TU.t_unknown, 4, [("r", TU.t_unknown, "$a2")]);
        (4, "arg_4", TU.t_unknown, 4, [("r", TU.t_unknown, "$a3")]);
        (5, "arg_5", TU.t_unknown, 4, [("s", TU.t_unknown, "16")]);
        (6, "arg_6", TU.t_int, 4, [("s", TU.t_int, "20")])]);
      ("f7", [("r", TU.t_int, "$a3"); ("s", TU.t_int, "20")],
       [(1, "arg_1", TU.t_unknown, 4, [("r", TU.t_unknown, "$a0")]);
        (2, "arg_2", TU.t_unknown, 4, [("r", TU.t_unknown, "$a1")]);
        (3, "arg_3", TU.t_unknown, 4, [("r", TU.t_unknown, "$a2")]);
        (4, "arg_4", TU.t_int, 4, [("r", TU.t_int, "$a3")]);
        (5, "arg_5", TU.t_unknown, 4, [("s", TU.t_unknown, "16")]);
        (6, "arg_6", TU.t_int, 4, [("s", TU.t_int, "20")])]);
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_get_inferred_fts_parameters") lastupdated;

    system_settings#set_architecture "mips";

    List.iter (fun (fname, locs, result) ->
        TS.add_simple_test
          ~title:fname
               (fun () ->
                 let xresult = List.map BU.convert_fts_parameter_input result in
                 let locs =
                   List.map
                     (BU.input_parameter_location_to_parameter_location "mips")
                     locs in
                 let fintf = default_function_interface ~locations:locs fname in
                 let params = get_fts_parameters fintf in
                 BA.equal_function_parameters
                   ~expected:xresult
                   ~received:params ())) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    function_signature_of_bvarinfo_x86 ();
    function_signature_of_bvarinfo_arm ();
    function_signature_of_bvarinfo_mips ();
    read_xml_function_interface_mips ();
    read_xml_function_interface_arm ();
    get_mips_inferred_fts_parameters ();
    TS.exit_file ()
  end

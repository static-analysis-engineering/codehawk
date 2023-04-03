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

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHStreamWrapper

(* bchlibelf *)
open BCHDwarf
open BCHDwarfTypes
open BCHDwarfUtils
open BCHELFDebugAbbrevSection
open BCHELFTypes
open BCHELFSectionHeader

(* tchlib *)
module TS = TCHTestSuite

module A = TCHAssertion
module G = TCHGenerator
module S = TCHSpecification

(* bchlib *)
module D = BCHDoubleword
module SI = BCHSystemInfo
module SW = BCHStreamWrapper
module U = BCHByteUtilities

(* tbchlibelf *)
module EA = TCHBchlibelfAssertion

module TR = CHTraceResult


let testname = "bCHDwarf"
let lastupdated = "2023-04-03"


let decode_debug_attribute_value_test () =
  let tests = [
      ("addr", "DW_AT_low_pc", "DW_FORM_addr", "00811a00", "0x811a00");
      ("data1", "DW_AT_language", "DW_FORM_data1", "01", "1");
      ("data2", "DW_AT_decl_line", "DW_FORM_data2", "5595", "21909");
      ("data4", "DW_AT_stmt_list", "DW_FORM_data4", "00003e17", "0x3e17");
      ("sdata-0", "DW_AT_const_value", "DW_FORM_sdata", "00", "0");
      ("sdata-18", "DW_AT_const_value", "DW_FORM_sdata", "12", "18");
      ("sdata-200", "DW_AT_const_value", "DW_FORM_sdata", "c801", "200");
      ("sdata-500", "DW_AT_const_value", "DW_FORM_sdata", "f403", "500");
      ("sdata-neg", "DW_AT_const_value", "DW_FORM_sdata", "807f060000", "-128");
      ("ref4", "DW_AT_type", "DW_FORM_ref4", "0000004f", "<0x4f>");
      ("string", "DW_AT_name", "DW_FORM_string", "696e7400", "int");
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_decode_debug_attribute_value_test") lastupdated;

    List.iter (fun (title, s_attr, s_form, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let bytestring = U.write_hex_bytes_to_bytestring bytes in
            let ch = make_pushback_stream ~little_endian:false bytestring in
            let attr = string_to_dwarf_attr_type s_attr in
            let form = string_to_dwarf_form_type s_form in
            let (_, atvalue) =
              decode_debug_attribute_value
                ~attrspec:(attr, form) ~base:wordzero ch in
            A.equal_string result (dwarf_attr_value_to_string atvalue))) tests;

    TS.launch_tests ()
  end       


let decode_debug_ref_attribute_value_test () =
  let tests = [
      ("ref4", "DW_AT_type", "DW_FORM_ref4", "0x0", "0000004f", "<0x4f>");
      ("ref4-r0", "DW_AT_type", "DW_FORM_ref4", "0x63cb6", "00000030", "<0x63ce6>");
      ("ref4-r1", "DW_AT_type", "DW_FORM_ref4", "0x63cb6", "0000012e", "<0x63de4>")
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_decode_debug_ref_attribute_value_test") lastupdated;

    List.iter (fun (title, s_attr, s_form, base, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let bytestring = U.write_hex_bytes_to_bytestring bytes in
            let ch = make_pushback_stream ~little_endian:false bytestring in
            let attr = string_to_dwarf_attr_type s_attr in
            let form = string_to_dwarf_form_type s_form in
            let base = TR.tget_ok (string_to_doubleword base) in
            let (_, atvalue) =
              decode_debug_attribute_value
                ~attrspec:(attr, form) ~base:base ch in
            A.equal_string result (dwarf_attr_value_to_string atvalue))) tests;

    TS.launch_tests ()
  end


let decode_variable_die_test () =
  let get_string =
    (fun (index: int) ->
      match index with
      | 2761 -> "arg_options"
      | _ -> "?") in
  let tests = [
      ("var-addr", "223400030e3a0b3b0b491302180000", "0x0",
       "22c90a00000137fd0b00000503bc130a000000",
       [(DW_AT_name, "0xac9:arg_options");
        (DW_AT_decl_file, "1");
        (DW_AT_decl_line, "55");
        (DW_AT_type, "<0xbfd>");
        (DW_AT_location, "DW_OP_addr: 0xa13bc (size: 5)")]);
      ("var-loc-list", "23340003083a0b3b0b491302170000", "0x0",
       "236f707400013e5a000000bb000000",
       [(DW_AT_name, "opt");
        (DW_AT_decl_file, "1");
        (DW_AT_decl_line, "62");
        (DW_AT_type, "<0x5a>");
        (DW_AT_location, "0xbb (loclistptr)")])
         
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_decode_variable_die_test") lastupdated;

    List.iter (fun (title, abbrev, base, debuginfo, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let astring = U.write_hex_bytes_to_bytestring abbrev in
            let istring = U.write_hex_bytes_to_bytestring debuginfo in
            let sh = mk_elf_section_header () in
            let section = mk_elf_debug_abbrev_section astring sh in
            let abbreventry = section#get_abbrev_entry in
            let fabbrev = fun (i: int) -> abbreventry in
            let chi = make_pushback_stream ~little_endian:true istring in
            let base = TR.tget_ok (string_to_doubleword base) in
            let var =
              decode_variable_die
                ~get_abbrev_entry:fabbrev
                ~get_string
                ~base
                chi in
            EA.equal_variable_debuginfo_entry result var)) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    decode_debug_attribute_value_test ();
    decode_debug_ref_attribute_value_test ();
    decode_variable_die_test ();
    TS.exit_file ()
  end

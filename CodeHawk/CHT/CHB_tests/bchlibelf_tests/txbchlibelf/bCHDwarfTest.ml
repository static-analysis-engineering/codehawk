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
let lastupdated = "2023-02-14"


let decode_decompilation_unit_header_test () =
  let tests = [
      ("cu-0", "000012d100040000000004", ("0x12d1", 4, "0x0", 4));
      ("cu-1", "000036d900040000013c04", ("0x36d9", 4, "0x13c", 4))
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_decode_decompilation_unit_header_test") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let bytestring = U.write_hex_bytes_to_bytestring bytes in
            let ch = make_pushback_stream ~little_endian:false bytestring in
            let cuheader = decode_compilation_unit_header ch in
            EA.equal_compilation_unit_header result cuheader ())) tests;

    TS.launch_tests ()
  end


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
              decode_debug_attribute_value ch wordzero (attr, form) in
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
            let (_, atvalue) = decode_debug_attribute_value ch base (attr, form) in
            A.equal_string result (dwarf_attr_value_to_string atvalue))) tests;

    TS.launch_tests ()
  end


let decode_compilation_unit_test () =
  let tests = [
      ("cu-1",
       "01110010061101120103081b0825081305000000",
       "0x9a6a",
       "000000ad0002"
       ^ "00000778040100003e1700811a000081"
       ^ "20582e2e2f50726f6a6563745f536574"
       ^ "74696e67732f537461727475705f436f"
       ^ "64652f6763632f636f7265305f696e74"
       ^ "635f73775f68616e646c6572732e5300"
       ^ "5c5c56424f585356525c736861726564"
       ^ "5f446f776e6c6f6164735c776f726b73"
       ^ "706163655f73333264735f76322e315c"
       ^ "6d706335373737635f6465765f633130"
       ^ "5c44656275675f464c41534800303030"
       ^ "3030303030303030008001",
       ("0xad", "0x778", 1, DW_TAG_compile_unit,
       [(DW_AT_stmt_list, "0x3e17");
        (DW_AT_low_pc, "0x811a00");
        (DW_AT_high_pc, "0x812058");
        (DW_AT_name, "../Project_Settings/Startup_Code/gcc/core0_intc_sw_handlers.S");
        (DW_AT_comp_dir, "\\\\VBOXSVR\\shared_Downloads\\workspace_s32ds_v2.1\\mpc5777c_dev_c10\\Debug_FLASH");
        (DW_AT_producer, "00000000000");
        (DW_AT_language, "32769")]))
    ] in
  begin
    TS.new_testsuite
      (testname ^ "_decode_compilation_unit_test") lastupdated;

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
            let chi = make_pushback_stream ~little_endian:false istring in
            let base = TR.tget_ok (string_to_doubleword base) in            
            let cu = decode_compilation_unit chi base fabbrev in
            EA.equal_compilation_unit result cu ())) tests;

    TS.launch_tests ()
  end
  
  

let () =
  begin
    TS.new_testfile testname lastupdated;
    decode_decompilation_unit_header_test ();
    decode_debug_attribute_value_test ();
    decode_debug_ref_attribute_value_test ();
    decode_compilation_unit_test ();
    TS.exit_file ()
  end

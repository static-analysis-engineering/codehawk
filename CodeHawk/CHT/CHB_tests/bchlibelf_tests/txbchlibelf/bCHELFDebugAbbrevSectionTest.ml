(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023-2024  Aarno Labs LLC

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

(* bchlibelf *)
open BCHELFDebugAbbrevSection
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


let testname = "bCHELFDebugAbbrevSection"
let lastupdated = "2023-02-12"



let get_abbrev_entry_test () =
  let tests = [
      ("tag_compile_unit",
       "011101250e130b030e1b0e101799421700000000",
       (1, "DW_TAG_compile_unit", true,
        [("DW_AT_producer", "DW_FORM_strp");
         ("DW_AT_language", "DW_FORM_data1");
         ("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_comp_dir", "DW_FORM_strp");
         ("DW_AT_stmt_list", "DW_FORM_sec_offset");
         ("DW_AT_GNU_macros", "DW_FORM_sec_offset")]));
      ("tag_base_type",
       "0224000b0b3e0b030800000000",
       (2, "DW_TAG_base_type", false,
        [("DW_AT_byte_size", "DW_FORM_data1");
         ("DW_AT_encoding", "DW_FORM_data1");
         ("DW_AT_name", "DW_FORM_string")]));
      ("tag_typedef",
       "041600030e3a0b3b0b49130000",
       (4, "DW_TAG_typedef", false,
        [("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data1");
         ("DW_AT_type", "DW_FORM_ref4")]));
      ("tag_enumeration_type",
       "0504010b0b3a0b3b0b01130000",
       (5, "DW_TAG_enumeration_type", true,
        [("DW_AT_byte_size", "DW_FORM_data1");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data1");
         ("DW_AT_sibling", "DW_FORM_ref4")]));
      ("tag_enumerator",
       "062800030e1c0d0000",
       (6, "DW_TAG_enumerator", false,
        [("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_const_value", "DW_FORM_sdata")]));
      ("tag_volatile_type",
       "07350049130000",
       (7, "DW_TAG_volatile_type", false,
        [("DW_AT_type", "DW_FORM_ref4")]));
      ("tag_const_type",
       "08260049130000",
       (8, "DW_TAG_const_type", false,
        [("DW_AT_type", "DW_FORM_ref4")]));
      ("tag_array_type",
       "090101491301130000",
       (9, "DW_TAG_array_type", true,
        [("DW_AT_type", "DW_FORM_ref4");
         ("DW_AT_sibling", "DW_FORM_ref4")]));
      ("tag_subrange_type",
       "0a210049132f0b0000",
       (10, "DW_TAG_subrange_type", false,
        [("DW_AT_type", "DW_FORM_ref4");
         ("DW_AT_upper_bound", "DW_FORM_data1")]));
      ("tag_structure_type",
       "0b13010b0b3a0b3b0501130000",
       (11, "DW_TAG_structure_type", true,
        [("DW_AT_byte_size", "DW_FORM_data1");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data2");
         ("DW_AT_sibling", "DW_FORM_ref4")]));
      ("tag_union_type",
       "0a17010b0b3a0b3b0501130000",
       (10, "DW_TAG_union_type", true,
        [("DW_AT_byte_size", "DW_FORM_data1");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data2");
         ("DW_AT_sibling", "DW_FORM_ref4")]));
      ("tag_member",
       "0c0d0003083a0b3b054913380b0000",
       (12, "DW_TAG_member", false,
        [("DW_AT_name", "DW_FORM_string");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data2");
         ("DW_AT_type", "DW_FORM_ref4");
         ("DW_AT_data_member_location", "DW_FORM_data1")]));
      ("tag_pointer_type",
       "100f000b0b0000",
       (16, "DW_TAG_pointer_type", false,
        [("DW_AT_byte_size", "DW_FORM_data1")]));
      ("tag_subroutine_type",
       "171501271901130000",
       (23, "DW_TAG_subroutine_type", true,
        [("DW_AT_prototyped", "DW_FORM_flag_present");
         ("DW_AT_sibling", "DW_FORM_ref4")]));
      ("tag_formal_parameter",
       "18050049130000",
       (24, "DW_TAG_formal_parameter", false,
        [("DW_AT_type", "DW_FORM_ref4")]));
      ("tag_unspecified_parameters",
       "2018000000",
       (32, "DW_TAG_unspecified_parameters", false, []));
      ("tag_variable_34",
       "223400030e3a0b3b0b491302180000",
       (34, "DW_TAG_variable", false,
        [("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data1");
         ("DW_AT_type", "DW_FORM_ref4");
         ("DW_AT_location", "DW_FORM_exprloc")]));
      ("tag_variable_35",
       "23340003083a0b3b0b491302170000",
       (35, "DW_TAG_variable", false,
        [("DW_AT_name", "DW_FORM_string");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data1");
         ("DW_AT_type", "DW_FORM_ref4");
         ("DW_AT_location", "DW_FORM_sec_offset")]));
      ("tag_variable_ext",
       "193400030e3a0b3b0b49133f193c190000",
       (25, "DW_TAG_variable", false,
        [("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data1");
         ("DW_AT_type", "DW_FORM_ref4");
         ("DW_AT_external", "DW_FORM_flag_present");
         ("DW_AT_declaration", "DW_FORM_flag_present")]));
      ("tag_variable_loc",
       "1a3400030e3a0b3b0b49133f190218000000",
       (26, "DW_TAG_variable", false,
        [("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data1");
         ("DW_AT_type", "DW_FORM_ref4");
         ("DW_AT_external", "DW_FORM_flag_present");
         ("DW_AT_location", "DW_FORM_exprloc")]));
      ("tag_subprogram",
       "132e01030e3a0b3b0b271911011206401897421901130000",
       (19, "DW_TAG_subprogram", true,
        [("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data1");
         ("DW_AT_prototyped", "DW_FORM_flag_present");
         ("DW_AT_low_pc", "DW_FORM_addr");
         ("DW_AT_high_pc", "DW_FORM_data4");
         ("DW_AT_frame_base", "DW_FORM_exprloc");
         ("DW_AT_GNU_all_call_sites", "DW_FORM_flag_present");
         ("DW_AT_sibling", "DW_FORM_ref4")]));
      ("tag_subprogram_tail",
       "1e2e013f19030e3a0b3b0b2719491311011206401896421901130000",
       (30, "DW_TAG_subprogram", true,
        [("DW_AT_external", "DW_FORM_flag_present");
         ("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data1");
         ("DW_AT_prototyped", "DW_FORM_flag_present");
         ("DW_AT_type", "DW_FORM_ref4");
         ("DW_AT_low_pc", "DW_FORM_addr");
         ("DW_AT_high_pc", "DW_FORM_data4");
         ("DW_AT_frame_base", "DW_FORM_exprloc");
         ("DW_AT_GNU_all_tail_call_sites", "DW_FORM_flag_present");
         ("DW_AT_sibling", "DW_FORM_ref4")]));
      ("tag_lexical_block",
       "170b01110112060000",
       (23, "DW_TAG_lexical_block", true,
        [("DW_AT_low_pc", "DW_FORM_addr");
         ("DW_AT_high_pc", "DW_FORM_data4")]));
      ("tag_label",
       "1f0a00030e3a0b3b0511010000",
       (31, "DW_TAG_label", false,
        [("DW_AT_name", "DW_FORM_strp");
         ("DW_AT_decl_file", "DW_FORM_data1");
         ("DW_AT_decl_line", "DW_FORM_data2");
         ("DW_AT_low_pc", "DW_FORM_addr")]));
      ("tag_inlined_subroutine",
       "111d01311311011206580b59050000",
       (17, "DW_TAG_inlined_subroutine", true,
        [("DW_AT_abstract_origin", "DW_FORM_ref4");
         ("DW_AT_low_pc", "DW_FORM_addr");
         ("DW_AT_high_pc", "DW_FORM_data4");
         ("DW_AT_call_file", "DW_FORM_data1");
         ("DW_AT_call_line", "DW_FORM_data2")]));
      ("tag_GNU_call_site",
       "1789820101110131130000",
       (23, "DW_TAG_GNU_call_site", true,
        [("DW_AT_low_pc", "DW_FORM_addr");
         ("DW_AT_abstract_origin", "DW_FORM_ref4")]));
      ("tag_GNU_call_site_parameter",
       "188a82010002189142180000",
       (24, "DW_TAG_GNU_call_site_parameter", false,
        [("DW_AT_location", "DW_FORM_exprloc");
         ("DW_AT_GNU_call_site_value", "DW_FORM_exprloc")]))
          
    ] in
  begin
    TS.new_testsuite (testname ^ "_get_abbrev_entry_test") lastupdated;

    List.iter (fun (title, bytes, result) ->
        TS.add_simple_test
          ~title
          (fun () ->
            let bytestring = U.write_hex_bytes_to_bytestring bytes in            
            let sectionheader = mk_elf_section_header () in
            let section = mk_elf_debug_abbrev_section bytestring sectionheader in
            let abbreventry = section#get_abbrev_entry in
            EA.equal_abbrev_entry ~expected:result ~received:abbreventry ())) tests;

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    get_abbrev_entry_test ();
    TS.exit_file ()
  end

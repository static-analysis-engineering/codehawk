(* =============================================================================
   CodeHawk Binary Analyzer 
   Henny Sipma
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
open BCHBasicTypes

(* bchlibelf *)
open BCHELFTypes

module H = Hashtbl


let dw_tag_values = H.create 31  (* int -> dwarf_tag_type *)
let dw_tag_names = H.create 31 (* dwarf_tag_type -> string *)
let dw_tag_string_values = H.create 31 (* string -> dwarf_tag_type *)

let _ =
  List.iter (fun (index, tag, name) ->
      begin
        H.add dw_tag_values index tag;
        H.add dw_tag_names tag name;
        H.add dw_tag_string_values name tag
      end)
    [(0x01, DW_TAG_array_type, "DW_TAG_array_type");
     (0x02, DW_TAG_class_type, "DW_TAG_class_type");
     (0x03, DW_TAG_entry_point, "DW_TAG_entry_point");
     (0x04, DW_TAG_enumeration_type, "DW_TAG_enumeration_type");
     (0x05, DW_TAG_formal_parameter, "DW_TAG_formal_parameter");
     (0x08, DW_TAG_imported_declaration, "DW_TAG_imported_declaration");
     (0x0a, DW_TAG_label, "DW_TAG_label");
     (0x0b, DW_TAG_lexical_block, "DW_TAG_lexical_block");
     (0x0d, DW_TAG_member, "DW_TAG_member");
     (0x0f, DW_TAG_pointer_type, "DW_TAG_pointer_type");
     (0x10, DW_TAG_reference_type, "DW_TAG_reference_type");
     (0x11, DW_TAG_compile_unit, "DW_TAG_compile_unit");
     (0x12, DW_TAG_string_type, "DW_TAG_string_type");
     (0x13, DW_TAG_structure_type, "DW_TAG_structure_type");
     (0x15, DW_TAG_subroutine_type, "DW_TAG_subroutine_type");
     (0x16, DW_TAG_typedef, "DW_TAG_typedef");
     (0x17, DW_TAG_union_type, "DW_TAG_union_type");
     (0x18, DW_TAG_unspecified_parameters, "DW_TAG_unspecified_parameters");
     (0x19, DW_TAG_variant, "DW_TAG_variant");
     (0x1a, DW_TAG_common_block, "DW_TAG_common_block");
     (0x1b, DW_TAG_common_inclusion, "DW_TAG_common_inclusion");
     (0x1c, DW_TAG_inheritance, "DW_TAG_inheritance");
     (0x1d, DW_TAG_inlined_subroutine, "DW_TAG_inlined_subroutine");
     (0x1e, DW_TAG_module, "DW_TAG_module");
     (0x1f, DW_TAG_ptr_to_member_type, "DW_TAG_ptr_to_member_type");
     (0x20, DW_TAG_set_type, "DW_TAG_set_type");
     (0x21, DW_TAG_subrange_type, "DW_TAG_subrange_type");
     (0x22, DW_TAG_with_stmt, "DW_TAG_with_stmt");
     (0x23, DW_TAG_access_declaration, "DW_TAG_access_declaration");
     (0x24, DW_TAG_base_type, "DW_TAG_base_type");
     (0x25, DW_TAG_catch_block, "DW_TAG_catch_block");
     (0x26, DW_TAG_const_type, "DW_TAG_const_type");
     (0x27, DW_TAG_constant, "DW_TAG_constant");
     (0x28, DW_TAG_enumerator, "DW_TAG_enumerator");
     (0x29, DW_TAG_file_type, "DW_TAG_file_type");
     (0x2a, DW_TAG_friend, "DW_TAG_friend");
     (0x2b, DW_TAG_namelist, "DW_TAG_namelist");
     (0x2c, DW_TAG_namelist_item, "DW_TAG_namelist_item");
     (0x2d, DW_TAG_packed_type, "DW_TAG_packed_type");
     (0x2e, DW_TAG_subprogram, "DW_TAG_subprogram");
     (0x2f, DW_TAG_template_type_parameter, "DW_TAG_template_type_parameter");
     (0x30, DW_TAG_template_value_parameter, "DW_TAG_template_value_parameter");
     (0x31, DW_TAG_thrown_type, "DW_TAG_thrown_type");
     (0x32, DW_TAG_try_block, "DW_TAG_try_block");
     (0x33, DW_TAG_variant_part, "DW_TAG_variant_part");
     (0x34, DW_TAG_variable, "DW_TAG_variable");
     (0x35, DW_TAG_volatile_type, "DW_TAG_volatile_type");
     (0x36, DW_TAG_dwarf_procedure, "DW_TAG_dwarf_procedure");
     (0x37, DW_TAG_restrict_type, "DW_TAG_restrict_type");
     (0x38, DW_TAG_interface_type, "DW_TAG_interface_type");
     (0x39, DW_TAG_namespace, "DW_TAG_namespace");
     (0x3a, DW_TAG_imported_module, "DW_TAG_imported_module");
     (0x3b, DW_TAG_unspecified_type, "DW_TAG_unspecified_type");
     (0x3c, DW_TAG_partial_unit, "DW_TAG_partial_type");
     (0x3d, DW_TAG_imported_unit, "DW_TAG_imported_unit");
     (0x3f, DW_TAG_condition, "DW_TAG_condition");
     (0x40, DW_TAG_shared_type, "DW_TAG_shared_type");
     (0x41, DW_TAG_type_unit, "DW_TAG_type_unit");
     (0x42, DW_TAG_rvalue_reference_type, "DW_TAG_rvalue_reference_type");
     (0x43, DW_TAG_template_alias, "DW_TAG_template_alias");
     (0x4109, DW_TAG_GNU_call_site, "DW_TAG_GNU_call_site");
     (0x410a, DW_TAG_GNU_call_site_parameter, "DW_TAG_GNU_call_site_parameter")
    ]


let dw_attr_values = H.create 31  (* int -> dwarf_attr_type *)
let dw_attr_names = H.create 31  (* dwarf_attr_type -> string *)
let dw_attr_string_values = H.create 31 (* string -> dwarf_attr_type *)

let _ =
  List.iter (fun (index, attr, name) ->
      begin
        H.add dw_attr_values index attr;
        H.add dw_attr_names attr name;
        H.add dw_attr_string_values name attr
      end)
    [(0x01, DW_AT_sibling, "DW_AT_sibling");
     (0x02, DW_AT_location, "DW_AT_location");
     (0x03, DW_AT_name, "DW_AT_name");
     (0x09, DW_AT_ordering, "DW_AT_ordering");
     (0x0b, DW_AT_byte_size, "DW_AT_byte_size");
     (0x0c, DW_AT_bit_offset, "DW_AT_bit_offset");
     (0x0d, DW_AT_bit_size, "DW_AT_bit_size");
     (0x10, DW_AT_stmt_list, "DW_AT_stmt_list");
     (0x11, DW_AT_low_pc, "DW_AT_low_pc");
     (0x12, DW_AT_high_pc, "DW_AT_high_pc");
     (0x13, DW_AT_language, "DW_AT_language");
     (0x15, DW_AT_discr, "DW_AT_discr");
     (0x16, DW_AT_discr_value, "DW_AT_discr_value");
     (0x17, DW_AT_visibility, "DW_AT_visibility");
     (0x18, DW_AT_import, "DW_AT_import");
     (0x19, DW_AT_string_length, "DW_AT_string_length");
     (0x1a, DW_AT_common_reference, "DW_AT_common_reference");
     (0x1b, DW_AT_comp_dir, "DW_AT_comp_dir");
     (0x1c, DW_AT_const_value, "DW_AT_const_value");
     (0x1d, DW_AT_containing_type, "DW_AT_containing_type");
     (0x1e, DW_AT_default_value,"DW_AT_default_value");
     (0x20, DW_AT_inline, "DW_AT_inline");
     (0x21, DW_AT_is_optional, "DW_AT_is_optional");
     (0x22, DW_AT_lower_bound, "DW_AT_lower_bound");
     (0x25, DW_AT_producer, "DW_AT_producer");
     (0x27, DW_AT_prototyped, "DW_AT_prototyped");
     (0x2a, DW_AT_return_addr, "DW_AT_return_addr");
     (0x2c, DW_AT_start_scope, "DW_AT_start_scope");
     (0x2e, DW_AT_bit_stride, "DW_AT_bit_stride");
     (0x2f, DW_AT_upper_bound, "DW_AT_upper_bound");
     (0x31, DW_AT_abstract_origin, "DW_AT_abstract_origin");
     (0x32, DW_AT_accessibility, "DW_AT_accessibility");
     (0x33, DW_AT_address_class, "DW_AT_address_class");
     (0x34, DW_AT_artificial, "DW_AT_artificial");
     (0x35, DW_AT_base_types, "DW_AT_base_types");
     (0x36, DW_AT_calling_convention, "DW_AT_calling_convention");
     (0x37, DW_AT_count, "DW_AT_count");
     (0x38, DW_AT_data_member_location, "DW_AT_data_member_location");
     (0x39, DW_AT_decl_column, "DW_AT_decl_column");
     (0x3a, DW_AT_decl_file, "DW_AT_decl_file");
     (0x3b, DW_AT_decl_line, "DW_AT_decl_line");
     (0x3c, DW_AT_declaration, "DW_AT_declaration");
     (0x3d, DW_AT_discr_list, "DW_AT_discr_list");
     (0x3e, DW_AT_encoding, "DW_AT_encoding");
     (0x3f, DW_AT_external, "DW_AT_external");
     (0x40, DW_AT_frame_base, "DW_AT_frame_base");
     (0x41, DW_AT_friend, "DW_AT_friend");
     (0x42, DW_AT_identifier_case, "DW_AT_identifier_case");
     (0x43, DW_AT_macro_info, "DW_AT_macro_info");
     (0x44, DW_AT_namelist_item, "DW_AT_namelist_item");
     (0x45, DW_AT_priority, "DW_AT_priority");
     (0x46, DW_AT_segment, "DW_AT_segment");
     (0x47, DW_AT_specification, "DW_AT_specification");
     (0x48, DW_AT_static_link, "DW_AT_static_link");
     (0x49, DW_AT_type, "DW_AT_type");
     (0x4a, DW_AT_use_location, "DW_AT_use_location");
     (0x4b, DW_AT_variable_parameter, "DW_AT_variable_parameter");
     (0x4c, DW_AT_virtuality, "DW_AT_virtuality");
     (0x4d, DW_AT_vtable_elem_location, "DW_AT_vtable_elem_location");
     (0x4e, DW_AT_allocated, "DW_AT_allocated");
     (0x4f, DW_AT_associated, "DW_AT_associated");
     (0x50, DW_AT_data_location, "DW_AT_data_location");
     (0x51, DW_AT_byte_stride, "DW_AT_byte_stride");
     (0x52, DW_AT_entry_pc, "DW_AT_entry_pc");
     (0x53, DW_AT_use_UTF8, "DW_AT_use_UTF8");
     (0x54, DW_AT_extension, "DW_AT_extension");
     (0x55, DW_AT_ranges, "DW_AT_ranges");
     (0x56, DW_AT_trampoline, "DW_AT_trampoline");
     (0x57, DW_AT_call_column, "DW_AT_call_column");
     (0x58, DW_AT_call_file, "DW_AT_call_file");
     (0x59, DW_AT_call_line, "DW_AT_call_line");
     (0x5a, DW_AT_description, "DW_AT_description");
     (0x5b, DW_AT_binary_scale, "DW_AT_binary_scale");
     (0x5c, DW_AT_decimal_scale, "DW_AT_decimal_scale");
     (0x5d, DW_AT_small, "DW_AT_small");
     (0x5e, DW_AT_decimal_sign, "DW_AT_decimal_sign");
     (0x5f, DW_AT_digit_count, "DW_AT_digit_count");
     (0x60, DW_AT_picture_string, "DW_AT_picture_string");
     (0x61, DW_AT_mutable, "DW_AT_mutable");
     (0x2111, DW_AT_GNU_call_site_value, "DW_AT_GNU_call_site_value");
     (0x2116, DW_AT_GNU_all_tail_call_sites, "DW_AT_GNU_all_tail_call_sites");
     (0x2117, DW_AT_GNU_all_call_sites, "DW_AT_GNU_all_call_sites");
     (0x2119, DW_AT_GNU_macros, "DW_AT_GNU_macros")
    ]


let dw_form_values = H.create 31  (* int -> dwarf_form_type *)
let dw_form_names = H.create 31  (* dwarf_form_type -> string *)
let dw_form_string_values = H.create 31   (* string -> dwarf_form_type *)

let _ =
  List.iter (fun (index, form, name) ->
      begin
        H.add dw_form_values index form;
        H.add dw_form_names form name;
        H.add dw_form_string_values name form
      end)
    [(0x01, DW_FORM_addr, "DW_FORM_addr");
     (0x03, DW_FORM_block2, "DW_FORM_block2");
     (0x04, DW_FORM_block4, "DW_FORM_block4");
     (0x05, DW_FORM_data2, "DW_FORM_data2");
     (0x06, DW_FORM_data4, "DW_FORM_data4");
     (0x07, DW_FORM_data8, "DW_FORM_data8");
     (0x08, DW_FORM_string, "DW_FORM_string");
     (0x09, DW_FORM_block, "DW_FORM_block");
     (0x0a, DW_FORM_block1, "DW_FORM_block1");
     (0x0b, DW_FORM_data1, "DW_FORM_data1");
     (0x0c, DW_FORM_flag, "DW_FORM_flag");
     (0x0d, DW_FORM_sdata, "DW_FORM_sdata");
     (0x0e, DW_FORM_strp, "DW_FORM_strp");
     (0x0f, DW_FORM_udata, "DW_FORM_udata");
     (0x10, DW_FORM_ref_addr, "DW_FORM_ref_addr");
     (0x11, DW_FORM_ref1, "DW_FORM_ref1");
     (0x12, DW_FORM_ref2, "DW_FORM_ref2");
     (0x13, DW_FORM_ref4, "DW_FORM_ref4");
     (0x14, DW_FORM_ref8, "DW_FORM_ref8");
     (0x15, DW_FORM_ref_udata, "DW_FORM_udata");
     (0x16, DW_FORM_indirect, "DW_FORM_indirect");
     (0x17, DW_FORM_sec_offset, "DW_FORM_sec_offset");
     (0x18, DW_FORM_exprloc, "DW_FORM_exprloc");
     (0x19, DW_FORM_flag_present, "DW_FORM_flag_present");
     (0x20, DW_FORM_ref_sig8, "DW_FORM_ref_sig8")
    ]


let int_to_dwarf_tag_type (v: int): dwarf_tag_type_t =
  if H.mem dw_tag_values v then
    H.find dw_tag_values v
  else
    DW_TAG_unknown (string_of_int v)


let dwarf_tag_type_to_string (tag: dwarf_tag_type_t) =
  if H.mem dw_tag_names tag then
    H.find dw_tag_names tag
  else
    match tag with
    | DW_TAG_unknown x -> "DW_TAG_unknown:" ^ x
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Error in DWARF TAG handling"]))


let string_to_dwarf_tag_type (tag: string) =
  if H.mem dw_tag_string_values tag then
    H.find dw_tag_string_values tag
  else
    DW_TAG_unknown tag


let int_to_dwarf_attr_type (v: int): dwarf_attr_type_t =
  if H.mem dw_attr_values v then
    H.find dw_attr_values v
  else
    DW_AT_unknown (string_of_int v)


let dwarf_attr_type_to_string (attr: dwarf_attr_type_t) =
  if H.mem dw_attr_names attr then
    H.find dw_attr_names attr
  else
    match attr with
    | DW_AT_unknown x -> "DW_AT_unknown:" ^ x
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Error in DWARF AT handling"]))


let string_to_dwarf_attr_type (attr: string) =
  if H.mem dw_attr_string_values attr then
    H.find dw_attr_string_values attr
  else
    DW_AT_unknown attr


let int_to_dwarf_form_type (v: int): dwarf_form_type_t =
  if H.mem dw_form_values v then
    H.find dw_form_values v
  else
    DW_FORM_unknown (string_of_int v)


let dwarf_form_type_to_string (form: dwarf_form_type_t) =
  if H.mem dw_form_names form then
    H.find dw_form_names form
  else
    match form with
    | DW_FORM_unknown x -> "DW_FORM_unknown:" ^ x
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Error in DWARF FORM handling"]))


let string_to_dwarf_form_type (form: string) =
  if H.mem dw_form_string_values form then
    H. find dw_form_string_values form
  else
    DW_FORM_unknown form


let dwarf_attr_block_to_string (len: int) (values: int list) =
  (string_of_int len)
  ^ ":["
  ^ String.concat "," (List.map string_of_int values)
  ^ "]"


let dwarf_attr_value_to_string (av: dwarf_attr_value_t) =
  match av with
  | DW_ATV_FORM_addr a -> a
  | DW_ATV_FORM_block2 (len, values) -> dwarf_attr_block_to_string len values
  | DW_ATV_FORM_block4 (len, values) -> dwarf_attr_block_to_string len values
  | DW_ATV_FORM_data2 i -> string_of_int i
  | DW_ATV_FORM_data4 dw -> dw#to_hex_string
  | DW_ATV_FORM_data8 (dw1, dw2) ->
     "(" ^ dw1#to_hex_string ^ "," ^ dw2#to_hex_string ^ ")"
  | DW_ATV_FORM_string s -> s
  | DW_ATV_FORM_block (len, values) -> dwarf_attr_block_to_string len values
  | DW_ATV_FORM_block1 (len, values) -> dwarf_attr_block_to_string len values
  | DW_ATV_FORM_data1 i -> string_of_int i
  | DW_ATV_FORM_flag i -> string_of_int i
  | DW_ATV_FORM_sdata i -> string_of_int i
  | DW_ATV_FORM_strp (offset, s) -> (string_of_int offset) ^ ":"  ^ s
  | DW_ATV_FORM_udata i -> string_of_int i
  | DW_ATV_FORM_ref_addr i -> string_of_int i
  | DW_ATV_FORM_ref1 r -> string_of_int r
  | DW_ATV_FORM_ref2 r -> string_of_int r
  | DW_ATV_FORM_ref4 dw -> "<" ^ dw#to_hex_string ^ ">"
  | DW_ATV_FORM_ref8 r -> string_of_int r
  | DW_ATV_FORM_ref_udata r -> string_of_int r
  | DW_ATV_FORM_unknown s -> "unknown:" ^ s


let abbrev_entry_to_string (e: debug_abbrev_table_entry_t) =
  (string_of_int e.dabb_index) ^ ":" ^ (dwarf_tag_type_to_string (e.dabb_tag))

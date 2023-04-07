(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
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

(* -----------------------------------------------------------------------------
   Reference:
   DWARF Debugging Information Format Version 4, June 10, 2010
   ----------------------------------------------------------------------------- *)

(* chlib *)
open CHNumerical

(* bchlib *)
open BCHLibTypes


type secoffset_kind_t =
  | LinePtr
  | LoclistPtr
  | MacPtr
  | RangelistPtr
  | UnknownSecoffsetPtr


type dwarf_tag_type_t =
  | DW_TAG_array_type              (* 0x01 *)
  | DW_TAG_class_type              (* 0x02 *)
  | DW_TAG_entry_point             (* 0x03 *)
  | DW_TAG_enumeration_type        (* 0x04 *)
  | DW_TAG_formal_parameter        (* 0x05 *)
  | DW_TAG_imported_declaration    (* 0x08 *)
  | DW_TAG_label                   (* 0x0a *)
  | DW_TAG_lexical_block           (* 0x0b *)
  | DW_TAG_member                  (* 0x0d *)
  | DW_TAG_pointer_type            (* 0x0f *)
  | DW_TAG_reference_type          (* 0x10 *)
  | DW_TAG_compile_unit            (* 0x11 *)
  | DW_TAG_string_type             (* 0x12 *)
  | DW_TAG_structure_type          (* 0x13 *)
  | DW_TAG_subroutine_type         (* 0x15 *)
  | DW_TAG_typedef                 (* 0x16 *)
  | DW_TAG_union_type              (* 0x17 *)
  | DW_TAG_unspecified_parameters  (* 0x18 *)
  | DW_TAG_variant                 (* 0x19 *)
  | DW_TAG_common_block            (* 0x1a *)
  | DW_TAG_common_inclusion        (* 0x1b *)
  | DW_TAG_inheritance             (* 0x1c *)
  | DW_TAG_inlined_subroutine      (* 0x1d *)
  | DW_TAG_module                  (* 0x1e *)
  | DW_TAG_ptr_to_member_type      (* 0x1f *)
  | DW_TAG_set_type                (* 0x20 *)
  | DW_TAG_subrange_type           (* 0x21 *)
  | DW_TAG_with_stmt               (* 0x22 *)
  | DW_TAG_access_declaration      (* 0x23 *)
  | DW_TAG_base_type               (* 0x24 *)
  | DW_TAG_catch_block             (* 0x25 *)
  | DW_TAG_const_type              (* 0x26 *)
  | DW_TAG_constant                (* 0x27 *)
  | DW_TAG_enumerator              (* 0x28 *)
  | DW_TAG_file_type               (* 0x29 *)
  | DW_TAG_friend                  (* 0x2a *)
  | DW_TAG_namelist                (* 0x2b *)
  | DW_TAG_namelist_item           (* 0x2c *)
  | DW_TAG_packed_type             (* 0x2d *)
  | DW_TAG_subprogram              (* 0x2e *)
  | DW_TAG_template_type_parameter (* 0x2f *)
  | DW_TAG_template_value_parameter (* 0x30 *)
  | DW_TAG_thrown_type             (* 0x31 *)
  | DW_TAG_try_block               (* 0x32 *)
  | DW_TAG_variant_part            (* 0x33 *)
  | DW_TAG_variable                (* 0x34 *)
  | DW_TAG_volatile_type           (* 0x35 *)
  | DW_TAG_dwarf_procedure         (* 0x36 *)
  | DW_TAG_restrict_type           (* 0x37 *)
  | DW_TAG_interface_type          (* 0x38 *)
  | DW_TAG_namespace               (* 0x39 *)
  | DW_TAG_imported_module         (* 0x3a *)
  | DW_TAG_unspecified_type        (* 0x3b *)
  | DW_TAG_partial_unit            (* 0x3c *)
  | DW_TAG_imported_unit           (* 0x3d *)
  | DW_TAG_condition               (* 0x3f *)
  | DW_TAG_shared_type             (* 0x40 *)
  | DW_TAG_type_unit               (* 0x41 *)
  | DW_TAG_rvalue_reference_type   (* 0x42 *)
  | DW_TAG_template_alias          (* 0x43 *)
  | DW_TAG_GNU_call_site           (* 0x4109 *)
  | DW_TAG_GNU_call_site_parameter (* 0x410a *)
  | DW_TAG_unknown of string


type dwarf_attr_type_t =
  | DW_AT_sibling                  (* 0x01: reference *)
  | DW_AT_location                 (* 0x02: exprloc, loclistptr *)
  | DW_AT_name                     (* 0x03: string *)
  | DW_AT_ordering                 (* 0x09: constant *)
  | DW_AT_byte_size                (* 0x0b: constant, exprloc, reference *)
  | DW_AT_bit_offset               (* 0x0c: constant, exprloc, reference *)
  | DW_AT_bit_size                 (* 0x0d: constant, exprloc, reference *)
  | DW_AT_stmt_list                (* 0x10: lineptr *)
  | DW_AT_low_pc                   (* 0x11: address *)
  | DW_AT_high_pc                  (* 0x12: address, constant *)
  | DW_AT_language                 (* 0x13: constant *)
  | DW_AT_discr                    (* 0x15: reference *)
  | DW_AT_discr_value              (* 0x16: constant *)
  | DW_AT_visibility               (* 0x17: constant *)
  | DW_AT_import                   (* 0x18: reference *)
  | DW_AT_string_length            (* 0x19: exprloc, loclistptr *)
  | DW_AT_common_reference         (* 0x1a: reference *)
  | DW_AT_comp_dir                 (* 0x1b: string *)
  | DW_AT_const_value              (* 0x1c: block, constant, string *)
  | DW_AT_containing_type          (* 0x1d: reference *)
  | DW_AT_default_value            (* 0x1e: reference *)
  | DW_AT_inline                   (* 0x20: constant *)
  | DW_AT_is_optional              (* 0x21: flag *)
  | DW_AT_lower_bound              (* 0x22: constant, exprloc, reference *)
  | DW_AT_producer                 (* 0x25: string *)
  | DW_AT_prototyped               (* 0x27: flag *)
  | DW_AT_return_addr              (* 0x2a: exprloc, loclistptr *)
  | DW_AT_start_scope              (* 0x2c: Constant, rangelistptr *)
  | DW_AT_bit_stride               (* 0x2e: constant, exprloc, reference *)
  | DW_AT_upper_bound              (* 0x2f: constant, exprloc, reference *)
  | DW_AT_abstract_origin          (* 0x31: reference *)
  | DW_AT_accessibility            (* 0x32: constant *)
  | DW_AT_address_class            (* 0x33: constant *)
  | DW_AT_artificial               (* 0x34: flag *)
  | DW_AT_base_types               (* 0x35: reference *)
  | DW_AT_calling_convention       (* 0x36: constant *)
  | DW_AT_count                    (* 0x37: constant, exprloc, reference *)
  | DW_AT_data_member_location     (* 0x38: constant, exprloc, loclistptr *)
  | DW_AT_decl_column              (* 0x39: constant *)
  | DW_AT_decl_file                (* 0x3a: constant *)
  | DW_AT_decl_line                (* 0x3b: constant *)
  | DW_AT_declaration              (* 0x3c: flag *)
  | DW_AT_discr_list               (* 0x3d: block *)
  | DW_AT_encoding                 (* 0x3e: constant *)
  | DW_AT_external                 (* 0x3f: flag *)
  | DW_AT_frame_base               (* 0x40: exprloc, loclistptr *)
  | DW_AT_friend                   (* 0x41: reference *)
  | DW_AT_identifier_case          (* 0x42: constant *)
  | DW_AT_macro_info               (* 0x43: macptr *)
  | DW_AT_namelist_item            (* 0x44: reference *)
  | DW_AT_priority                 (* 0x45: reference *)
  | DW_AT_segment                  (* 0x46: exprloc, loclistptr *)
  | DW_AT_specification            (* 0x47: reference *)
  | DW_AT_static_link              (* 0x48: exprloc, loclistptr *)
  | DW_AT_type                     (* 0x49: reference *)
  | DW_AT_use_location             (* 0x4a: exprloc, loclistptr *)
  | DW_AT_variable_parameter       (* 0x4b: flag *)
  | DW_AT_virtuality               (* 0x4c: constant *)
  | DW_AT_vtable_elem_location     (* 0x4d: exprloc, loclistptr *)
  | DW_AT_allocated                (* 0x4e: constant, exprloc, reference *)
  | DW_AT_associated               (* 0x4f: constant, exprloc, reference *)
  | DW_AT_data_location            (* 0x50: exprloc *)
  | DW_AT_byte_stride              (* 0x51: constant, exprloc, reference *)
  | DW_AT_entry_pc                 (* 0x52: address *)
  | DW_AT_use_UTF8                 (* 0x53: flag *)
  | DW_AT_extension                (* 0x54: reference *)
  | DW_AT_ranges                   (* 0x55: rangelistptr *)
  | DW_AT_trampoline               (* 0x56: address, flag, reference, string *)
  | DW_AT_call_column              (* 0x57: constant *)
  | DW_AT_call_file                (* 0x58: constant *)
  | DW_AT_call_line                (* 0x59: constant *)
  | DW_AT_description              (* 0x5a: string *)
  | DW_AT_binary_scale             (* 0x5b: constant *)
  | DW_AT_decimal_scale            (* 0x5c: constant *)
  | DW_AT_small                    (* 0x5d: reference *)
  | DW_AT_decimal_sign             (* 0x5e: constant *)
  | DW_AT_digit_count              (* 0x5f: constant *)
  | DW_AT_picture_string           (* 0x60: string *)
  | DW_AT_mutable                  (* 0x61: flag *)
  | DW_AT_linkage_name             (* 0x6e: string *)
  | DW_AT_GNU_call_site_value      (* 0x2111: vendor extension, exprloc *)
  | DW_AT_GNU_call_site_target     (* 0x2113: vendor extension *)
  | DW_AT_GNU_tail_call            (* 0x2115: vendor extension, flag_present *)
  | DW_AT_GNU_all_tail_call_sites  (* 0x2116: vendor extension, flag *)
  | DW_AT_GNU_all_call_sites       (* 0x2117: vendor extension, flag *)
  | DW_AT_GNU_macros               (* 0x2119: vendor extension *)
  | DW_AT_unknown of string


type dwarf_form_type_t =
  | DW_FORM_addr                   (* 0x01: address (absolute address) *)
  | DW_FORM_block2                 (* 0x03: block *)
  | DW_FORM_block4                 (* 0x04: block *)
  | DW_FORM_data2                  (* 0x05: constant *)
  | DW_FORM_data4                  (* 0x06: constant *)
  | DW_FORM_data8                  (* 0x07: constant *)
  | DW_FORM_string                 (* 0x08: string *)
  | DW_FORM_block                  (* 0x09: block *)
  | DW_FORM_block1                 (* 0x0a: block *)
  | DW_FORM_data1                  (* 0x0b: constant *)
  | DW_FORM_flag                   (* 0x0c: flag *)
  | DW_FORM_sdata                  (* 0x0d: constant *)
  | DW_FORM_strp                   (* 0x0e: string *)
  | DW_FORM_udata                  (* 0x0f: constant *)
  | DW_FORM_ref_addr     (* 0x10: reference (absolute address in .debug_info) *)
  | DW_FORM_ref1                   (* 0x11: reference within compilation unit *)
  | DW_FORM_ref2                   (* 0x12: reference within compilation unit *)
  | DW_FORM_ref4                   (* 0x13: reference within compilation unit *)
  | DW_FORM_ref8                   (* 0x14: reference within compilation unit *)
  | DW_FORM_ref_udata              (* 0x15: reference within compilation unit *)
  | DW_FORM_indirect
  | DW_FORM_sec_offset  (* 0x17: lineptr, loclistptr, macptr, rangelistptr *)
  | DW_FORM_exprloc                (* 0x18: exprloc *)
  | DW_FORM_flag_present           (* 0x19: flag *)
  | DW_FORM_ref_sig8               (* 0x20: reference (64-bit type signature) *)
  | DW_FORM_unknown of string


type dwarf_operand_t =
  | ConstantAddress of doubleword_int
  | OneByteUnsignedValue of int
  | OneByteSignedValue of int
  | TwoByteUnsignedValue of int
  | TwoByteSignedValue of int
  | FourByteUnsignedValue of int
  | EightByteUnsignedValue of numerical_t
  | ULEB128Constant of numerical_t
  | SLEB128Constant of numerical_t


and dwarf_operation_t =
  | DW_OP_addr of dwarf_operand_t    (* 0x03: constant address *)
  | DW_OP_deref                      (* 0x06 *)
  | DW_OP_const1u of dwarf_operand_t (* 0x08: 1-byte constant *)
  | DW_OP_const1s of dwarf_operand_t (* 0x09: 1-byte constant (signed) *)
  | DW_OP_const2u of dwarf_operand_t (* 0x0a: 2-byte constant *)
  | DW_OP_const4u of dwarf_operand_t (* 0x0c: 4-byte constant *)
  | DW_OP_dup                        (* 0x12 *)
  | DW_OP_drop                       (* 0x13 *)
  | DW_OP_over                       (* 0x14 *)
  | DW_OP_swap                       (* 0x16 *)
  | DW_OP_and                        (* 0x1a *)
  | DW_OP_minus                      (* 0x1c *)
  | DW_OP_mul                        (* 0x1e *)
  | DW_OP_or                         (* 0x21 *)
  | DW_OP_plus                       (* 0x22 *)
  | DW_OP_plus_uconst of dwarf_operand_t  (* 0x23: ULEB128 addend *)
  | DW_OP_shl                        (* 0x24 *)
  | DW_OP_shr                        (* 0x25 *)
  | DW_OP_bra of dwarf_operand_t     (* 0x28 *)
  | DW_OP_eq                         (* 0x29 *)
  | DW_OP_ge                         (* 0x2a *)
  | DW_OP_lt                         (* 0x2d *)
  | DW_OP_ne                         (* 0x2e *)
  | DW_OP_lit of int                 (* 0x30 - 0x4f *)
  | DW_OP_reg of int                 (* 0x50 - 0x6f *)
  | DW_OP_breg of int * dwarf_operand_t  (* 0x70 - 0x8f: sleb128 offset *)
  | DW_OP_regx of dwarf_operand_t    (* 0x90 *)
  | DW_OP_fbreg of dwarf_operand_t   (* 0x91: SLEB128 offset *)
  | DW_OP_piece of dwarf_operand_t   (* 0x93: ULEB128 size of piece addressed *)
  | DW_OP_call_frame_cfa             (* 0x9c *)
  | DW_OP_stack_value                (* 0x9f *)

  (* GNU extensions (some of them have been incorporated in DWARF-v5) *)
  | DW_OP_GNU_implicit_pointer of
      string * dwarf_operand_t * dwarf_operand_t (* 0xf2, offset in debug_info, sleb128 offset *)
  | DW_OP_GNU_entry_value of int * dwarf_expr_t  (* 0xf3 *)

  (* 0xf5: base-address (to be added to offset), ULEB128 register number, ULEB128
     constant offset *)
  | DW_OP_GNU_regval_type of
      doubleword_int * dwarf_operand_t * dwarf_operand_t

  (* 0xf7: base-address (to be added to offset), ULEB128 constant offset *)
  | DW_OP_GNU_convert of doubleword_int * dwarf_operand_t

  (* x0fa: base-address (to be added to offset), 4-byte offset of DIE *)
  | DW_OP_GNU_parameter_ref of doubleword_int * dwarf_operand_t
  | DW_OP_unknown of int             (* not recognized *)


and dwarf_expr_t = dwarf_operation_t list


type debug_abbrev_table_entry_t = {
    dabb_index: int;
    dabb_tag: dwarf_tag_type_t;
    dabb_has_children: bool;
    dabb_attr_specs: (dwarf_attr_type_t * dwarf_form_type_t) list
  }


(** Describes the location of an object whose lifetime is either static or
    the same as the lexical block that owns it, and that does not move during
    its lifetime.

    A simple location describes the location of one contiguous piece (or all)
    of an object. It may describe a location in addressable memory or a 
    register, or the lack of a location.

    A simple location can be
    (1) a Memory Location Description, expressed by a dwarf expression, whose
    value is the address of a piece or all of an entity in memory;
    (2) a Register Location Description, expressed by a single dwarf operation
    which can be either one of DW_OP_reg0, ..., DW_OP_reg31, or DW_OP_regx
    with an unsigned LEB128 that encodes the name of the register.
    (3) an Implicit Location Description, representing a piece or all of an
    object that has no actual location, but whose contents are either known
    or known to be undefined. A known constant or a computed value can be
    represented by:
    - DW_OP_implicit_value, which specifies an immediate value, or
    - DW_OP_stack_value, which is the at top of the DWARF expression stack as
    the result of a dwarf expression evaluated.
    (4) an Empty Location Description, represented by a dwarf expression with
    zero operations. It represents a piece or all of an object that is present
    in the source but not in the object code.

    A composite location describes the location of an object in terms of 
    pieces, each of which may be contained in part of a register or stored in
    a memory location unrelated to other pieces.

    A composite location consists of a sequence of pieces, where each piece
    consists of a simple location followed by a composition operator, which
    can be:
    - DW_OP_piece size, specifying the size in bytes of the piece, or
    - DW_OP_bit size, offset, specifying the size in bits of the piece and
      the offset in bits from the preceding location description.

    Ref: Dwarf v4, page 26-29 *)
type single_location_description_t =
  | SimpleLocation of dwarf_expr_t
  | CompositeLocation of (dwarf_expr_t * dwarf_operation_t) list


type location_list_entry_t = {
    lle_start_address: doubleword_int;
    lle_end_address: doubleword_int;
    lle_location: single_location_description_t
  }


type debug_location_list_entry_t =
  | LocationListEntry of location_list_entry_t
  | LocBaseAddressSelectionEntry of doubleword_int
  | LocEndOfListEntry


type debug_loc_description_t =
  | SingleLocation of single_location_description_t
  | LocationList of debug_location_list_entry_t list


type debug_range_list_entry_t =
  | RangeListEntry of doubleword_int * doubleword_int
  | RngBaseAddressSelectionEntry of doubleword_int
  | RngEndOfListEntry


type debug_range_description_t =
  | SingleAddress of doubleword_int
  | ContiguousAddressRange of doubleword_int * doubleword_int
  | NoncontiguousAddressRange of debug_range_list_entry_t list


type debug_aranges_table_entry_t = {
    dar_length: int;
    dar_debug_info_offset: doubleword_int;
    dar_pointer_size: int;
    dar_tuples: (doubleword_int * doubleword_int) list
  }


type debug_info_entry_t = {
    dwie_abbrev: int;
    dwie_tag: dwarf_tag_type_t;
    dwie_values: (dwarf_attr_type_t * dwarf_attr_value_t) list;
    dwie_children: debug_info_entry_t list
  }


and dwarf_attr_value_t =
  | DW_ATV_FORM_addr of doubleword_int
  | DW_ATV_FORM_block2 of int * int list
  | DW_ATV_FORM_block4 of int * int list
  | DW_ATV_FORM_data2 of int
  | DW_ATV_FORM_data4 of doubleword_int
  | DW_ATV_FORM_data8 of doubleword_int * doubleword_int
  | DW_ATV_FORM_string of string
  | DW_ATV_FORM_block of int * int list
  | DW_ATV_FORM_block1 of int * int list
  | DW_ATV_FORM_data1 of int
  | DW_ATV_FORM_flag of int
  | DW_ATV_FORM_flag_present of int
  | DW_ATV_FORM_sdata of int
  | DW_ATV_FORM_strp of doubleword_int * string (* 4-byte offset *)
  | DW_ATV_FORM_udata of int
  | DW_ATV_FORM_ref_addr of int
  | DW_ATV_FORM_ref1 of int
  | DW_ATV_FORM_ref2 of int
  | DW_ATV_FORM_ref4 of doubleword_int
  | DW_ATV_FORM_ref8 of int
  | DW_ATV_FORM_ref_udata of int
  | DW_ATV_FORM_exprloc of int * dwarf_expr_t
  | DW_ATV_FORM_sec_offset of secoffset_kind_t * doubleword_int
  | DW_ATV_FORM_sec_offset_loclist of doubleword_int * debug_loc_description_t
  | DW_ATV_FORM_sec_offset_rangelist of doubleword_int * debug_range_description_t
  | DW_ATV_FORM_unknown of string


type debug_compilation_unit_header_t = {
    dwcu_length: doubleword_int;
    dwcu_offset: doubleword_int;
    dwcu_version: int;
    dwcu_abbrev_offset: doubleword_int;
    dwcu_address_size: int
  }


type debug_compilation_unit_t = {
    cu_header: debug_compilation_unit_header_t;
    cu_unit: debug_info_entry_t
  }


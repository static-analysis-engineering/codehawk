(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
   References used:

   The standard /usr/include/elf.h in Arch Linux
   The latest draft of the System V Application Binary Interface: 
   http://www.sco.com/developers/gabi/latest/contents.html
   March 19, 1997 draft copy of the Intel Supplement to the System V 
   Application Binary Interface
   ----------------------------------------------------------------------------- *) 

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

type elf_section_header_type_t = 
  | SHT_NullSection 
  | SHT_ProgBits 
  | SHT_SymTab 
  | SHT_StrTab 
  | SHT_Rela 
  | SHT_Hash 
  | SHT_Dynamic 
  | SHT_Note 
  | SHT_NoBits 
  | SHT_Rel 
  | SHT_ShLib 
  | SHT_DynSym 
  | SHT_InitArray 
  | SHT_FiniArray
  | SHT_PreinitArray 
  | SHT_Group 
  | SHT_SymTabShndx
  | SHT_GNU_verdef
  | SHT_GNU_verneed
  | SHT_GNU_versym
  | SHT_MIPS_RegInfo
  | SHT_OSSection of doubleword_int 
  | SHT_ProcSection of doubleword_int 
  | SHT_UserSection of doubleword_int 
  | SHT_UnknownType of doubleword_int
                     
type elf_program_header_type_t =
  | PT_Null 
  | PT_Load 
  | PT_Dynamic 
  | PT_Interpreter 
  | PT_Note 
  | PT_Reference 
  | PT_ThreadLocalStorage
  | PT_RegInfo
  | PT_OSSpecific of doubleword_int 
  | PT_ProcSpecific of doubleword_int

type elf_dynamic_tag_value_t = DTV_d_val | DTV_d_ptr | DTV_d_none
                     
type elf_dynamic_tag_t =
  | DT_Null
  | DT_Needed
  | DT_PltRelSz
  | DT_PltGot
  | DT_Hash
  | DT_StrTab
  | DT_SymTab
  | DT_Rela
  | DT_RelaSz
  | DT_RelaEnt
  | DT_StrSz
  | DT_SymEnt
  | DT_Init
  | DT_Fini
  | DT_SoName
  | DT_RPath
  | DT_Symbolic
  | DT_Rel
  | DT_RelSz
  | DT_RelEnt
  | DT_PltRel
  | DT_Debug
  | DT_TextRel
  | DT_JmpRel
  | DT_VerSym
  | DT_VerNeed
  | DT_VerNeedNum
  | DT_LoProc
  | DT_HiProc
  (* MIPS-specific dynamic tags *)
  | DT_MIPS_Rld_Version
  | DT_MIPS_Flags
  | DT_MIPS_Base_Address
  | DT_MIPS_LocalGotNo
  | DT_MIPS_SymTabNo
  | DT_MIPS_UnrefExtNo
  | DT_MIPS_GotSym
  | DT_MIPS_Rld_Map
  (* Unknown *)
  | DT_Unknown of string


type elf_arm_relocation_tag_t =
  | R_ARM_NONE
  | R_ARM_PC24
  | R_ARM_ABS32
  | R_ARM_REL32
  | R_ARM_LDR_PCG0
  | R_ARM_ABS16
  | R_ARM_ABS12
  | R_ARM_THM_ABS5
  | R_ARM_ABS8
  | R_ARM_SBREL32
  | R_ARM_THM_CALL
  | R_ARM_THM_PC8
  | R_ARM_BREL_ADJ
  | R_ARM_TLS_DESC
  | R_ARM_THM_SW18
  | R_ARM_XPC25
  | R_ARM_THM_XPC22
  | R_ARM_TLS_DTPMOD32
  | R_ARM_TLS_DTPOFF32
  | R_ARM_TLS_TPOFF32
  | R_ARM_COPY
  | R_ARM_GLOB_DAT
  | R_ARM_JUMP_SLOT
  | R_ARM_RELATIVE
  | R_ARM_GOTOFF32
  | R_ARM_BASE_PREL
  | R_ARM_GOT_BREL
  | R_ARM_PLT32
  | R_ARM_CALL
  | R_ARM_JUMP24
  | R_ARM_THM_JUMP24
  | R_ARM_BASE_ABS
  | R_ARM_ALU_PCREL_7_0
  | R_ARM_ALU_PCREL_15_8
  | R_ARM_ALU_PCREL_23_15
  | R_ARM_LDR_SBREL_11_0_NC
  | R_ARM_ALU_SBREL_19_12_NC
  | R_ARM_ALU_SBREL_27_20_CK
  | R_ARM_TARGET1
  | R_ARM_SBREL31
  | R_ARM_V4BX
  | R_ARM_TARGET2
  | R_ARM_PREL31
  | R_ARM_MOVW_ABS_NC
  | R_ARM_MOVT_ABS
  | R_ARM_MOVW_PREL_NC
  | R_ARM_MOVT_PREL
  | R_ARM_THM_MOVW_ABS_NC
  | R_ARM_THM_MOVT_ABS
  | R_ARM_THM_MOVW_PREL_NC
  | R_ARM_THM_MOVT_PREL
  | R_ARM_THM_JUMP19
  | R_ARM_THM_JUMP6
  | R_ARM_THM_ALU_PREL_11_0
  | R_ARM_THM_PC12
  | R_ARM_Unknown of string    (* catch value *)


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
  | DW_AT_GNU_call_site_value      (* 0x2111: vendor extension, exprloc *)
  | DW_AT_GNU_all_tail_call_sites  (* 0x2116: vendor extension, flag *)
  | DW_AT_GNU_all_call_sites       (* 0x2117: vendor extension, flag *)
  | DW_AT_GNU_macros               (* 0x2119: vendor extension *)
  | DW_AT_unknown of string


type dwarf_form_type_t =
  | DW_FORM_addr                   (* 0x01: address *)
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
  | DW_FORM_ref_addr               (* 0x10: reference *)
  | DW_FORM_ref1                   (* 0x11: reference *)
  | DW_FORM_ref2                   (* 0x12: reference *)
  | DW_FORM_ref4                   (* 0x13: reference *)
  | DW_FORM_ref8                   (* 0x14: reference *)
  | DW_FORM_ref_udata              (* 0x15: reference *)
  | DW_FORM_indirect
  | DW_FORM_sec_offset  (* 0x17: lineptr, loclistptr, macptr, rangelistptr *)
  | DW_FORM_exprloc                (* 0x18: exprloc *)
  | DW_FORM_flag_present           (* 0x19: flag *)
  | DW_FORM_ref_sig8               (* 0x20: reference *)
  | DW_FORM_unknown of string


class type elf_dictionary_int =
  object
    method reset: unit
    method index_string: string -> int
    method get_string: int -> string
    method write_xml_string: ?tag:string -> xml_element_int -> string -> unit
    method read_xml_string: ?tag:string -> xml_element_int -> string
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end
         
class type elf_raw_section_int =
  object
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty : pretty_t
  end

class type elf_raw_segment_int =
  object
    method get_xstring: string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty : pretty_t
  end

class type elf_string_table_int =
  object
    method set_entries: unit
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_string: int -> string
    method get_string_at_address: doubleword_int -> string option
    method write_xml: xml_element_int -> unit
    method write_xml_strings: xml_element_int -> unit
    method toPretty: pretty_t
  end

class type elf_symbol_table_entry_int =
  object
    method id: int
    method read: pushback_stream_int -> unit         
    method set_name: string -> unit
    method get_name: string
    method get_st_binding: int
    method get_st_type: int
    method get_st_name: doubleword_int
    method get_st_value: doubleword_int
    method get_value: doubleword_int
    method has_address_value: bool
    method has_name: bool
    method is_function: bool
    method to_rep_record: string list * int list
    method write_xml: xml_element_int -> unit
  end

class type elf_symbol_table_int =
  object
    method read: unit
    method set_symbol_names: elf_string_table_int -> unit
    method set_function_entry_points: unit
    method set_function_names: unit
    method set_mapping_symbols: unit
    method get_xstring: string
    method get_size: int
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_symbol: int -> elf_symbol_table_entry_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method write_xml_symbols: xml_element_int -> unit
    method toPretty: pretty_t
  end

class type elf_relocation_table_entry_int =
  object
    method id: int
    method read: pushback_stream_int -> unit
    method set_symbol: elf_symbol_table_entry_int -> unit
    method get_symbol: elf_symbol_table_entry_int
    method get_symbol_string: string
    method get_symbol_index: int
    method get_address: doubleword_int
    method get_type: int
    method has_offset: doubleword_int -> bool
    method has_address: bool
    method has_symbol: bool
    method is_function: bool
    method to_rep_record: string list * int list
  end

class type elf_relocation_table_int =
  object
    method read: unit
    method set_symbols: elf_symbol_table_int -> unit
    method set_function_entry_points: unit
    method get_xstring: string
    method get_size: int
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_offset_symbol: doubleword_int -> string
    method has_offset: doubleword_int -> bool
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method write_xml_entries: xml_element_int -> unit
    method toPretty: pretty_t
  end

class type elf_dynamic_table_entry_int =
  object
    method id: int
    method read: pushback_stream_int -> unit
    method get_tag: elf_dynamic_tag_t
    method get_tag_name: string
    method get_d_tag: doubleword_int
    method get_d_ptr: doubleword_int
    method get_d_val: numerical_t
    method get_d_un: numerical_t
    method to_rep_record: string list * int list
  end

class type elf_dynamic_table_int =
  object
    method read: unit
    method get_xstring: string
    method get_size: int
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method write_xml_entries: xml_element_int -> unit
    method toPretty: pretty_t
  end

class type elf_dynamic_segment_entry_int =
  object
    method id: int
    method read: pushback_stream_int -> unit

    (* accessors *)
    method get_tag: elf_dynamic_tag_t
    method get_tag_name: string
    method get_d_tag: doubleword_int
    method get_d_ptr: doubleword_int
    method get_d_val: numerical_t
    method get_d_un: numerical_t

    method get_relocation_table: doubleword_int
    method get_relocation_table_size: numerical_t
    method get_relocation_table_entry: numerical_t
    method get_plt_relocation_table: doubleword_int
    method get_plt_relocation_table_size: numerical_t
    method get_plt_relocation_table_type: numerical_t
    method get_string_table: doubleword_int
    method get_string_table_size: numerical_t
    method get_symbol_table: doubleword_int
    method get_hash_table: doubleword_int
    method get_init: doubleword_int
    method get_fini: doubleword_int
    method get_rld_map: doubleword_int
    method get_got: doubleword_int
    method get_syment: numerical_t
    method get_symtabno: numerical_t
    method get_gnu_symbol_version_table: doubleword_int
    method get_gnu_symbol_version_reqts: doubleword_int
    method get_gnu_symbol_version_reqts_no: numerical_t

    (* predicates *)
    method is_null: bool
    method is_relocation_table: bool
    method is_relocation_table_size: bool
    method is_relocation_table_entry: bool
    method is_plt_relocation_table: bool
    method is_plt_relocation_table_size: bool
    method is_plt_relocation_table_type: bool
    method is_string_table: bool
    method is_string_table_size: bool
    method is_symbol_table: bool
    method is_hash_table: bool
    method is_init: bool
    method is_fini: bool
    method is_rld_map: bool
    method is_got: bool
    method is_syment: bool
    method is_symtabno: bool
    method is_gnu_symbol_version_table: bool
    method is_gnu_symbol_version_reqts: bool
    method is_gnu_symbol_version_reqts_no: bool

    (* printing *)
    method to_rep_record: string list * int list
    method toPretty: pretty_t
  end

class type elf_dynamic_segment_int =
  object
    method read: unit

    (* accessors  *)
    method get_xstring: string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method get_hash_address: doubleword_int
    method get_reltab_address: doubleword_int
    method get_reltab_size: numerical_t
    method get_reltab_ent: numerical_t
    method get_jmprel_address: doubleword_int
    method get_jmprel_size: numerical_t
    method get_symtab_address: doubleword_int
    method get_strtab_address: doubleword_int
    method get_init_address: doubleword_int
    method get_fini_address: doubleword_int
    method get_rld_map_address: doubleword_int
    method get_got_address: doubleword_int
    method get_syment: numerical_t
    method get_symtabno: numerical_t
    method get_string_table_size: numerical_t
    method get_gnu_symbol_version_table: doubleword_int
    method get_gnu_symbol_version_reqts: doubleword_int
    method get_gnu_symbol_version_reqts_no: numerical_t

    (* predicates *)
    method includes_VA: doubleword_int -> bool
    method has_hash_address: bool
    method has_reltab_address: bool
    method has_reltab_size: bool
    method has_reltab_ent: bool
    method has_jmprel_address: bool
    method has_jmprel_size: bool
    method has_symtab_address: bool
    method has_strtab_address: bool
    method has_init_address: bool
    method has_fini_address: bool
    method has_rld_map_address: bool
    method has_got_address: bool
    method has_syment: bool
    method has_symtabno: bool
    method has_string_table_size: bool
    method has_gnu_symbol_version_table: bool
    method has_gnu_symbol_version_reqts: bool
    method has_gnu_symbol_version_reqts_no: bool

    (* printing *)
    method write_xml: xml_element_int -> unit
    method write_xml_entries: xml_element_int -> unit
    method toPretty: pretty_t
  end

class type elf_program_section_int =
  object
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_value: doubleword_int -> doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


type debug_info_entry_t = {
    die_abbrev: int;
    die_tag: dwarf_tag_type_t;
    die_values: (dwarf_attr_type_t * dwarf_attr_value_t) list;
    die_children: debug_info_entry_t list
  }


and dwarf_attr_value_t =
  | DW_ATV_FORM_addr of string
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
  | DW_ATV_FORM_sdata of int
  | DW_ATV_FORM_strp of int * string
  | DW_ATV_FORM_udata of int
  | DW_ATV_FORM_ref_addr of int
  | DW_ATV_FORM_ref1 of int
  | DW_ATV_FORM_ref2 of int
  | DW_ATV_FORM_ref4 of doubleword_int
  | DW_ATV_FORM_ref8 of int
  | DW_ATV_FORM_ref_udata of int
  | DW_ATV_FORM_unknown of string


type debug_compilation_unit_header_t = {
    dwcu_length: doubleword_int;
    dwcu_version: int;
    dwcu_offset: doubleword_int;
    dwcu_address_size: int
  }


type debug_compilation_unit_t = {
    cu_header: debug_compilation_unit_header_t;
    cu_unit: debug_info_entry_t
  }


class type elf_debug_info_section_int =
  object
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty : pretty_t
  end


type debug_abbrev_table_entry_t = {
    dabb_index: int;
    dabb_tag: dwarf_tag_type_t;
    dabb_has_children: bool;
    dabb_attr_specs: (dwarf_attr_type_t * dwarf_form_type_t) list
  }


class type elf_debug_abbrev_section_int =
  object
    method initstream: int -> unit
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method get_abbrev_entry: debug_abbrev_table_entry_t
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty : pretty_t
  end


type debug_aranges_table_entry_t = {
    dar_length: int;
    dar_debug_info_offset: doubleword_int;
    dar_pointer_size: int;
    dar_tuples: (doubleword_int * doubleword_int) list
  }


class type elf_debug_aranges_section_int =
  object
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty : pretty_t
  end


type elf_section_t =
| ElfStringTable of elf_string_table_int
| ElfSymbolTable of elf_symbol_table_int
| ElfDynamicSymbolTable of elf_symbol_table_int
| ElfRelocationTable of elf_relocation_table_int
| ElfDynamicTable of elf_dynamic_table_int
| ElfProgramSection of elf_program_section_int
| ElfDebugInfoSection of elf_debug_info_section_int
| ElfDebugAbbrevSection of elf_debug_abbrev_section_int
| ElfOtherSection of elf_raw_section_int


type elf_segment_t  =
  | ElfDynamicSegment of elf_dynamic_segment_int
  | ElfOtherSegment of elf_raw_segment_int


class type elf_file_header_int =
object
  method read: unit

  (* accessors *)
  method get_type       : int
  method get_machine    : int
  method get_header_size: int
  method get_version    : doubleword_int
  method get_flags      : doubleword_int

  method get_program_entry_point        : doubleword_int
  method get_program_header_table_offset: doubleword_int
  method get_section_header_table_offset: doubleword_int

  method get_program_header_table_entry_size  : int
  method get_program_header_table_entry_num   : int
  method get_section_header_table_entry_size  : int
  method get_section_header_table_entry_num   : int

  method get_section_header_string_table_index: int

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

class type elf_program_header_int =
object
  method read: doubleword_int -> int -> unit

  (* accessors *)
  method get_type   : doubleword_int
  method get_offset : doubleword_int
  method get_vaddr  : doubleword_int
  method get_paddr  : doubleword_int
  method get_file_size: doubleword_int
  method get_memory_size: doubleword_int
  method get_flags  : doubleword_int
  method get_align  : doubleword_int

  method get_program_header_type: elf_program_header_type_t

  (* predicates *)
  method is_loaded: bool
  method is_executable: bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t

end

class type elf_section_header_int =
object

  (* setters *)
  method read: doubleword_int -> int -> unit
  method set_name: string -> unit
  method set_fields:
           ?sname:doubleword_int
           -> ?stype:doubleword_int
           -> ?flags:doubleword_int
           -> ?addr:doubleword_int
           -> ?offset:doubleword_int
           -> ?size:doubleword_int
           -> ?link:doubleword_int
           -> ?info:doubleword_int
           -> ?addralign:doubleword_int
           -> ?entsize:doubleword_int
           -> sectionname:string
           -> unit
           -> unit

  (* setters *)
  method set_link: doubleword_int -> unit

  (* accessors *)
  method get_name      : doubleword_int
  method get_type      : doubleword_int
  method get_flags     : doubleword_int
  method get_addr      : doubleword_int
  method get_offset    : doubleword_int
  method get_size      : doubleword_int
  method get_link      : doubleword_int
  method get_info      : doubleword_int
  method get_addralign : doubleword_int
  method get_entry_size: doubleword_int

  method get_section_name: string
  method get_section_type: elf_section_header_type_t

  (* predicates *)
  method is_executable: bool
  method is_string_table: bool
  method is_symbol_table: bool
  method is_relocation_table: bool
  method is_program_section: bool
  method is_power_vle: bool

  method is_debug_info: bool
  method is_debug_abbrev: bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

class type elf_header_int =
object

  method read: unit
  method set_code_extent: unit
  method initialize_jump_tables: unit
  method initialize_call_back_tables: unit
  method initialize_struct_tables: unit

  (* accessors *)
  method get_program_entry_point: doubleword_int
  method get_sections: (int * elf_section_header_int * elf_section_t) list
  method get_program_segments: (int * elf_program_header_int * elf_segment_t) list
  method get_executable_sections: (elf_section_header_int * string) list
  method get_executable_segments: (elf_program_header_int * string) list
  method get_string_at_address: doubleword_int -> string option
  method get_xsubstring: doubleword_int -> int -> string
  method get_relocation: doubleword_int -> string option
  method get_containing_section: doubleword_int -> elf_raw_section_int option
  method get_program_value: doubleword_int -> doubleword_int

  (* predicates *)
  method has_sections: bool
  method is_program_address: doubleword_int -> bool
  method has_xsubstring: doubleword_int -> int -> bool
  method has_debug_info: bool
  method has_debug_abbrev: bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

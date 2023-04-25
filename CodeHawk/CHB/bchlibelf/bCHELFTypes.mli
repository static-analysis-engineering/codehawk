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

(* bchlibelf *)
open BCHDwarfTypes


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
    method read_got: unit
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_value: doubleword_int -> doubleword_int
    method get_string_reference: doubleword_int -> string option
    method get_got_value: doubleword_int -> doubleword_int
    method get_got_values: (string * doubleword_int) list
    method includes_VA: doubleword_int -> bool
    method is_got: bool
    method write_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


class type elf_debug_info_section_int =
  object
    method compilation_unit_stream: doubleword_int -> pushback_stream_int
    method compilation_unit_headers:
             doubleword_int list -> debug_compilation_unit_header_t list
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty : pretty_t
  end


class type elf_debug_abbrev_section_int =
  object
    method initstream: int -> unit
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method get_abbrev_entry: debug_abbrev_table_entry_t
    method get_abbrev_table: int -> debug_abbrev_table_entry_t list
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty : pretty_t
  end


class type elf_debug_loc_section_int =
  object
    method initstream: int -> unit
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method get_loclist: int -> debug_loc_description_t
    method get_location_list: debug_location_list_entry_t list
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty : pretty_t
  end


class type elf_debug_aranges_section_int =
  object
    method read: unit
    method get_size: int
    method get_xstring: string
    method get_xsubstring: doubleword_int -> int -> string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method debug_info_compilation_unit_offsets: doubleword_int list
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


class type elf_debug_str_section_int =
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


type elf_section_t =
| ElfStringTable of elf_string_table_int
| ElfSymbolTable of elf_symbol_table_int
| ElfDynamicSymbolTable of elf_symbol_table_int
| ElfRelocationTable of elf_relocation_table_int
| ElfDynamicTable of elf_dynamic_table_int
| ElfProgramSection of elf_program_section_int
| ElfDebugARangesSection of elf_debug_aranges_section_int
| ElfDebugInfoSection of elf_debug_info_section_int
| ElfDebugAbbrevSection of elf_debug_abbrev_section_int
| ElfDebugLocSection of elf_debug_loc_section_int
| ElfDebugStringSection of elf_debug_str_section_int
| ElfOtherSection of elf_raw_section_int


type elf_segment_t  =
  | ElfDynamicSegment of elf_dynamic_segment_int
  | ElfOtherSegment of elf_raw_segment_int


class type debug_abbrev_table_int =
  object

    method offset: doubleword_int

    method abbrev_entry: int -> debug_abbrev_table_entry_t

    method entry_count: int

  end


class type debug_info_function_int =
  object

    method name: string

    method variables: (string * debug_loc_description_t) list

    method variable_location_stats: (dwarf_expr_t list * dwarf_expr_t list)

    method has_name: bool

    method toPretty: pretty_t

  end


(** Provides the main access point for data provided in the .debug
    sections of an executable (if present). *)
class type dwarf_query_service_int =
  object

    (** Initializes the service with references to the debug sections, if
        present. *)
    method initialize: (int * string * elf_section_t) list -> unit

    (* ----------------------------------------------------------- accessors *)

    (** Returns a sorted list of offsets in .debug_info at which compilation
        units start. If there is no debug, or no aranges section is present,
        the empty list is returned. *)
    method compilation_unit_offsets: doubleword_int list

    (** [abbrev_table offset] returns the table of abbrev entries that start
        at offset [offset] in .debug_abbrev. *)
    method abbrev_table: doubleword_int -> debug_abbrev_table_int

    method compilation_unit: doubleword_int -> debug_compilation_unit_t

    method compilation_units: debug_compilation_unit_t list

    (** Returns a sorted list of virtual addresses that are associated with
        DW_TAG_subprogram debug_info_entries with a nonempty body. *)
    method debug_info_function_addresses: doubleword_int list

    (** [debug_info_function faddr] returns debug information on the function
        at virtual address [faddr] if present, and [None] otherwise.*)
    method debug_info_function: doubleword_int -> debug_info_function_int option

    method debug_info_functions: debug_info_function_int list

    method variable_location_stats: (int * int * int * dwarf_expr_t list * dwarf_expr_t list)

    (* ----------------------------------------------------------- predicates *)

    (** Returns true if the executable was compiled with debug.*)
    method has_debug: bool

    method toPretty: pretty_t

  end


class type elf_file_header_int =
object
  method read: unit

  (* accessors *)
  method get_type: int
  method get_machine: int
  method get_header_size: int
  method get_version: doubleword_int
  method get_flags: doubleword_int

  method get_program_entry_point: doubleword_int
  method get_program_header_table_offset: doubleword_int
  method get_section_header_table_offset: doubleword_int

  method get_program_header_table_entry_size: int
  method get_program_header_table_entry_num: int
  method get_section_header_table_entry_size: int
  method get_section_header_table_entry_num: int

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
  method get_name: doubleword_int
  method get_type: doubleword_int
  method get_flags: doubleword_int
  method get_addr: doubleword_int
  method get_offset: doubleword_int
  method get_size: doubleword_int
  method get_link: doubleword_int
  method get_info: doubleword_int
  method get_addralign: doubleword_int
  method get_entry_size: doubleword_int

  method get_section_name: string
  method get_section_type: elf_section_header_type_t

  (* predicates *)
  method is_executable: bool
  method is_string_table: bool
  method is_symbol_table: bool
  method is_relocation_table: bool
  method is_program_section: bool
  method is_pwr_vle: bool

  method is_debug_info: bool
  method is_debug_abbrev: bool
  method is_debug_aranges: bool
  method is_debug_loc: bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml: xml_element_int -> unit

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
  method get_global_offset_table_value: doubleword_int -> doubleword_int

  (* predicates *)
  method has_sections: bool
  method is_program_address: doubleword_int -> bool
  method is_global_offset_table_address: doubleword_int -> bool
  method has_xsubstring: doubleword_int -> int -> bool
  method has_debug_info: bool
  method has_debug_abbrev: bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
  | PT_OSSpecific of doubleword_int 
  | PT_ProcSpecific of doubleword_int
                     
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
  | DT_LoProc
  | DT_HiProc
  

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
    method get_xstring: string
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
    method get_xstring: string
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
    method get_type: int
    method has_offset: doubleword_int -> bool
    method has_symbol: bool
    method to_rep_record: string list * int list
  end

class type elf_relocation_table_int =
  object
    method read: unit
    method set_symbols: elf_symbol_table_int -> unit
    method get_xstring: string
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
    method get_d_tag: numerical_t
    method get_d_ptr: doubleword_int
    method get_d_val: doubleword_int
    method get_d_un: doubleword_int
    method to_rep_record: string list * int list
  end

class type elf_dynamic_table_int =
  object
    method read: unit
    method get_xstring: string
    method get_vaddr: doubleword_int
    method get_string_reference: doubleword_int -> string option
    method includes_VA: doubleword_int -> bool
    method write_xml: xml_element_int -> unit
    method write_xml_entries: xml_element_int -> unit
    method toPretty: pretty_t
  end

type elf_section_t =
| ElfStringTable of elf_string_table_int
| ElfSymbolTable of elf_symbol_table_int
| ElfDynamicSymbolTable of elf_symbol_table_int
| ElfRelocationTable of elf_relocation_table_int
| ElfDynamicTable of elf_dynamic_table_int
| ElfOtherSection of elf_raw_section_int

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

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t

end

class type elf_section_header_int =
object

  (* setters *)
  method read    : doubleword_int -> int -> unit
  method set_name: string -> unit

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

  (* accessors *)
  method get_sections: (int * elf_section_header_int * elf_section_t) list
  method get_executable_sections: (elf_section_header_int * string) list
  method get_string_at_address: doubleword_int -> string option
  method get_relocation: doubleword_int -> string option
  method get_containing_section: doubleword_int -> elf_raw_section_int option

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

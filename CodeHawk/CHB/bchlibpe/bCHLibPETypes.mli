(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

(* chlib *)
open BCHLibTypes


(* Basic Win32 exception handling function information structure
   reference:
   Matt Pietrek. A Crash Course on the Depths of Win32 Structured Exception
   Handling.
   http://www.microsoft.com/msj/0197/exception/exception.aspx ;

   Igorsk, Reversing Microsoft Visual C++ Part I: Exception Handling
   http://www.openrce.org/articles/full_view/21
*)
class type exn_unwind_map_entry_int =
object
  (* actions *)
  method read: string -> unit

  (* accessors *)
  method get_targetstate: int
  method get_action: doubleword_int

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
end


class type exn_function_info_int =
object
  (* actions *)
  method read: string -> unit

  (* accessors *)
  method get_magicnumber: doubleword_int
  method get_maxstate: int
  method get_unwindmap: doubleword_int
  method get_ntryblocks: int
  method get_tryblockmap: doubleword_int
  method get_estypelist: doubleword_int
  method get_ehflags: int

  (* xml *)
  method write_xml : xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t
end


type xregexpattern_t = {
  xregex_s: Str.regexp ;
  xregex_f: doubleword_int -> string -> bool
}

(* ====================================================== PE string table === *)

class type string_table_int =
object
  (* reset *)
  method reset: unit

  (* setters *)
  method add: doubleword_int -> string -> unit

  (* accessors *)
  method get: doubleword_int -> string        (* raises Invocation_error *)
  method get_strings: (doubleword_int * string) list

  (* predicates *)
  method has: doubleword_int -> bool

  (* printing *)
  method toPretty: pretty_t
end

(* ====================================================== PE symbol table === *)

class type pe_symboltable_int =
object

  (* actions *)
  method read: doubleword_int -> doubleword_int -> string -> unit  (* raises IO.No_more_input *)
  method reset: unit

  (* setters *)
  method set_image_base: doubleword_int -> unit
  method set_base_of_code: doubleword_int -> unit

  (* accessors *)
  method get_function_name: doubleword_int -> string    (* raises Invocation_error *)
  method get_function_address: string -> doubleword_int    (* raises Invocation_error *)

  (* predicates *)
  method has_function_name : doubleword_int -> bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t

end

(* ======================================================= PE Export Directory === *)

class type export_directory_table_int =
object

  (* actions *)
  method read                     : string -> unit
  method read_export_address_table: string -> unit
  method read_name_ordinal_table  : string -> unit

  (* setters *)
  method set_section_RVA          : doubleword_int -> unit
  method set_export_directory_RVA : doubleword_int -> unit
  method set_export_size          : doubleword_int -> unit

  (* accessors *)
  method get_export_address_table_RVA : doubleword_int
  method get_export_address_table_size: doubleword_int

  method get_name_pointer_table_RVA   : doubleword_int
  method get_name_pointer_table_size  : doubleword_int

  method get_ordinal_table_RVA        : doubleword_int
  method get_ordinal_table_size       : doubleword_int

  method get_name_RVA                 : doubleword_int

  method get_export_name_low_high     : string -> doubleword_int * doubleword_int

  method get_exported_functions       : doubleword_int list    (* absolute addresses *)
  method get_exported_function_names  : (doubleword_int * string) list

  (* xml *)
  method write_xml_ordinal_table      : xml_element_int -> unit
  method write_xml                    : xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

(* ==================================================== Assembly table layout === *)

class type assembly_table_layout_int =
object
  (* reset *)
  method reset: unit

  (* setters *)
  method add_import_lookup_table: doubleword_int -> doubleword_int -> string -> unit

  method set_export_directory         : doubleword_int -> doubleword_int -> unit
  method set_export_address_table     : doubleword_int -> doubleword_int -> unit
  method set_export_name_pointer_table: doubleword_int -> doubleword_int -> unit
  method set_export_ordinal_table     : doubleword_int -> doubleword_int -> unit
  method set_export_name_table        : doubleword_int -> doubleword_int -> unit

  method set_import_directory         : doubleword_int -> doubleword_int -> unit
  method set_hint_name_table          : doubleword_int -> doubleword_int -> unit
  method set_dll_name_table           : doubleword_int -> doubleword_int -> unit
  method set_IAT                      : doubleword_int -> doubleword_int -> unit
  method set_debug_data               : doubleword_int -> doubleword_int -> unit
  method set_load_config_directory    : doubleword_int -> doubleword_int -> unit
  method set_SE_handler_table         : doubleword_int -> doubleword_int -> unit

  (* accessors *)
  method get_fragments_in: doubleword_int -> doubleword_int ->
    (doubleword_int * doubleword_int * string) list

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

(* ====================================================== PE import directory === *)

class type import_directory_entry_int =
object

  (* actions *)
  method read      : pushback_stream_int -> unit
  method read_name : pushback_stream_int -> unit
  method read_table: pushback_stream_int -> pushback_stream_int -> unit  (* raises IO.No_more_input, Invalid_argument, Invalid_input *)

  (* setters *)
  method set_section_RVA                 : doubleword_int -> unit
  method set_import_directory_RVA        : doubleword_int -> unit
  method register_bound_library_functions: unit

  (* accessors *)
  method get_import_lookup_table_RVA : doubleword_int
  method get_import_address_table_RVA: doubleword_int
  method get_import_lookup_table_size: doubleword_int    (* raises Invalid_argument *)
  method get_name_RVA                : doubleword_int
  method get_functions               : string list
  method get_name                    : string
  method get_hint_name_table_low_high: (doubleword_int * doubleword_int) option
  method get_imported_function       : doubleword_int -> (string * string) option

  (* predicates *)
  method has_bound_addresses: bool

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
end

(* ================================================== PE load configuration table *)

class type load_configuration_directory_int =
object

  (* actions *)
  method read: string -> unit                                     (* raises IO.No_more_input *)
  method read_SE_handler_table: doubleword_int -> string -> unit  (* raises IO.No_more_input, Invalid_argument *)

  (* setters *)
  method set_section_RVA  : doubleword_int -> unit
  method set_directory_RVA: doubleword_int -> unit

  (* accessors *)
  method get_SE_handler_table_VA   : doubleword_int
  method get_SE_handler_table_size : doubleword_int
  method get_SE_handlers           : doubleword_int list

  (* xml *)
  method write_xml : xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

(* ==================================================== PE resource directory === *)

class type resource_directory_table_int =
object

  (* actions *)
  method read: string -> unit
  method reset: unit

  (* setters *)
  method set_section_RVA  : doubleword_int -> unit
  method set_directory_RVA: doubleword_int -> unit

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t

end

(* ======================================================== PE section header === *)

class type pe_section_header_int =
object
  (* identification *)
  method index: int

  (* actions *)
  method read: pushback_stream_int -> unit

  (* accessors *)
  method get_name               : string
  method get_pointer_to_raw_data: doubleword_int
  method get_size_of_raw_data   : doubleword_int
  method get_RVA                : doubleword_int
  method get_virtual_size       : doubleword_int
  method get_size               : doubleword_int   (* larger of size_of_raw_data and virtual_size *)
  method get_characteristics_digest: string

  (* predicates *)
  method is_read_only  : bool
  method is_readable   : bool
  method is_writable   : bool
  method is_executable : bool
  method is_initialized: bool
  method includes_RVA  : doubleword_int -> bool
  method includes_VA   : doubleword_int -> bool

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t
end

(* ============================================================== PE section === *)

class type pe_section_int =
object
  (** {1 Identification} *)

  method index: int

  (** {1 Readers} *)

  method read_export_directory_table: doubleword_int -> doubleword_int -> unit

  method read_import_directory_table: doubleword_int -> unit

  method read_load_configuration_structure: doubleword_int -> unit

  method read_resource_directory_table: doubleword_int -> unit

  (** {1 Accessors} *)

  method get_name: string

  method get_header: pe_section_header_int

  method get_exe_string : string

  (** Returns the section start address as an absolute address. *)
  method get_section_VA: doubleword_int

  (** Returns the section start address relative to the image base. *)
  method get_section_RVA : doubleword_int

  method get_virtual_size: doubleword_int

  method get_import_directory_table: import_directory_entry_int list

  method get_export_directory_table: export_directory_table_int

  method get_load_configuration_directory: load_configuration_directory_int

  method get_SE_handlers: doubleword_int list

  method get_imported_functions: (string * string list) list

  method get_exported_functions: doubleword_int list

  method get_exported_data_values: doubleword_int list

  method get_imported_function: doubleword_int -> (string * string) option

  method get_imported_function_by_index:
           doubleword_int -> (string * string) option

  method get_initialized_doubleword: doubleword_int -> doubleword_int option

  method get_n_doublewords: doubleword_int -> int -> doubleword_int list

  method get_string_reference: doubleword_int -> string option

  method get_wide_string_reference: doubleword_int -> string option

  method get_data_values:
           doubleword_int
           -> data_export_spec_t
           -> (int * doubleword_int) list

  (** {1 Predicates} *)

  (** [includes_VA addr] returns true if [addr] is between [section_VA] and
      [section_VA + virtual_size].*)
  method includes_VA: doubleword_int -> bool

  method includes_RVA: doubleword_int -> bool

  method includes_VA_in_file_image: doubleword_int -> bool

  method is_read_only: bool

  method is_writable: bool

  method is_executable: bool

  method has_import_directory_table: bool

  method has_export_directory_table: bool

  method has_load_configuration_directory: bool

  (** {1 Xml / Printing} *)

  (** Writes all bytes of the section to the given node in chunks of 16.*)
  method write_xml: xml_element_int -> unit

  method raw_data_to_string: doubleword_int list -> string   (* option to mark globals written *)
  method import_directory_entry_to_pretty: string -> pretty_t       (* raises Invalid_argument *)
  method import_directory_table_to_pretty: pretty_t

  method export_directory_table_to_pretty: pretty_t

  method load_configuration_directory_to_pretty: pretty_t

  method toPretty: pretty_t

end

(* ============================================================== PE sections === *)

class type pe_sections_int =
object
  (* reset *)
  method reset: unit

  (* actions *)
  method read_import_directory_table      : doubleword_int -> doubleword_int -> unit
  method read_export_directory_table      : doubleword_int -> doubleword_int -> unit
  method read_load_configuration_structure: doubleword_int -> doubleword_int -> unit
  method read_resource_directory_table    : doubleword_int -> doubleword_int -> unit

  (* setters *)
  method add_section : pe_section_header_int -> string -> unit

  (* accessors *)
  method get_export_directory_table      : export_directory_table_int
  method get_import_directory_table      : import_directory_entry_int list
  method get_load_configuration_directory: load_configuration_directory_int

  method get_sections                    : pe_section_int list
  method get_section                     : int -> pe_section_int
  method get_imported_functions          : (string * string list) list
  method get_exported_functions          : doubleword_int list
  method get_exported_data_values        : doubleword_int list
  method get_containing_section          : doubleword_int -> pe_section_int option

  method get_SE_handlers                     : doubleword_int list
  method get_imported_function_by_index      : doubleword_int -> (string * string) option
  method get_imported_function               : doubleword_int -> (string * string) option
  method get_read_only_initialized_doubleword: doubleword_int -> doubleword_int option
  method get_n_doublewords                   : doubleword_int -> int -> doubleword_int list
  method get_string_reference                : doubleword_int -> string option
  method get_wide_string_reference           : doubleword_int -> string option

  method get_virtual_function_address        : doubleword_int -> doubleword_int option
  method get_data_values                     : doubleword_int -> data_export_spec_t ->
    (int * string) list

  (* predicates *)
  method has_import_directory_table      : bool
  method has_export_directory_table      : bool
  method has_load_configuration_directory: bool

  method includes_VA         : doubleword_int -> bool
  method is_writable_address : doubleword_int -> bool
  method is_read_only_address: doubleword_int -> bool
  method is_exported         : doubleword_int -> bool

  (* printing *)
  method import_directory_entry_to_pretty      : string -> pretty_t
  method import_directory_table_to_pretty      : pretty_t
  method export_directory_table_to_pretty      : pretty_t
  method load_configuration_directory_to_pretty: pretty_t

  method toPretty: pretty_t
end

(* ================================================================ PE header === *)

class type pe_header_int =
object
  (* actions *)
  method read: unit
  method reset: unit

  (* accessors *)
  method get_number_of_sections: int
  method get_time_date_stamp   : doubleword_int
  method get_section_headers   : pe_section_header_int list
  method get_containing_section_name: doubleword_int -> string option

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
  method coff_file_header_to_pretty  : pretty_t
  method optional_header_to_pretty   : pretty_t
  method data_directory_to_pretty    : pretty_t
  method section_headers_to_pretty   : pretty_t
  method resource_directory_to_pretty: pretty_t
  method table_layout_to_pretty      : pretty_t
end

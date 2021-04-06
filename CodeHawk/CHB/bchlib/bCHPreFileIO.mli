(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

val set_functions_file_path  : unit -> unit

val get_bch_root             : string -> xml_element_int

val get_filename             : unit -> string
val get_function_filename    : string -> string -> string
val get_disassembly_filename : string -> string
val get_asm_listing_filename  : unit -> string
val get_orphan_code_listing_filename: unit -> string
val get_duplicate_coverage_filename: unit -> string
val get_x86dictionary_filename: unit -> string

val get_mips_dictionary_filename: unit -> string
val get_mips_assembly_instructions_filename: unit -> string

val get_arm_dictionary_filename: unit -> string
val get_arm_assembly_instructions_filename: unit -> string

val get_functions_filename   : unit -> string
val get_global_state_filename: unit -> string
val get_system_info_filename : unit -> string
val get_jni_calls_filename   : unit -> string
val get_resultmetrics_filename: unit -> string   (* analysis round statistics *)
val get_resultdata_filename  : unit -> string    (* application data digest *)
val get_section_filename     : string -> string
val get_segment_filename     : int -> string
val get_pe_header_filename   : unit -> string
val get_elf_header_filename  : unit -> string
val get_elf_dictionary_filename: unit -> string
val get_ida_dbfe_filename      : unit -> string    (* data blocks, function entry points *)

val get_disassembly_status_filename: unit -> string

val load_xml_file            : string -> string -> xml_element_int option

val load_resultmetrics_file     : unit -> xml_element_int option
val load_system_file            : unit -> xml_element_int option
val load_global_state_file      : unit -> xml_element_int option

val load_userdata_system_file   : unit -> xml_element_int option
val load_annotation_system_file : unit -> xml_element_int option
val load_userdata_function_file : string -> xml_element_int option
val load_userdata_struct_file   : string -> xml_element_int option
val load_userdata_structconstant_file: string -> xml_element_int option
val load_userdata_cpp_class_file: string -> xml_element_int option
val load_userdata_jumptable_file: string -> xml_element_int option
val load_ida_dbfe_file          : unit -> xml_element_int option

val load_pe_header_file: unit -> xml_element_int option
val load_elf_header_file: unit -> xml_element_int option
val load_segment_file: int -> xml_element_int option
val load_section_file: string -> xml_element_int option
val extract_function_info_file: string -> xml_element_int option
val extract_inferred_function_summary_file: string -> xml_element_int option
val extract_inferred_function_arguments_from_summary_file:string -> xml_element_int option
val read_vars: string -> variable_manager_int
val read_invs: string -> vardictionary_int -> invariant_io_int
val read_tinvs: string -> vardictionary_int -> type_invariant_io_int

val read_memory_string_file: string -> string

val save_bdictionary: unit -> unit
val load_bdictionary: unit -> unit

val save_interface_dictionary: unit -> unit
val load_interface_dictionary: unit -> unit

val save_export_function_summary_file: string -> xml_element_int -> unit
val save_export_data_value_file      : string -> xml_element_int -> unit
val save_export_ordinal_table: xml_element_int -> unit
val load_export_ordinal_table: string -> xml_element_int option
val save_resultdata_file    : xml_element_int -> unit
val save_cfgs     : xml_element_int -> unit
val save_vars     : string -> vardictionary_int -> unit
val save_invs     : string -> invariant_io_int -> unit
val save_tinvs    : string -> type_invariant_io_int -> unit
val save_executable_dump     : xml_element_int -> unit
val save_app_function_results_file: string -> xml_element_int -> unit
val save_resultmetrics: xml_element_int -> unit
val create_userdata_system_file: string -> unit

val save_log_files: string -> unit

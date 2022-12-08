(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022      Aarno Labs LLC

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

(* API to hide differences between PE and ELF *)

(* chlib *)
open CHNumerical

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

(* bchlibpe *)
open BCHLibPETypes


val register_exn_handler: doubleword_int -> string -> unit

val get_data_values: doubleword_int -> data_export_spec_t -> (int * string) list

val get_export_directory_table: unit -> export_directory_table_int

val get_exported_data_values: unit -> doubleword_int list

val get_exported_functions: unit -> doubleword_int list

val get_import_directory_table: unit -> import_directory_entry_int list

val get_imported_function_by_index: doubleword_int -> (string * string) option

val get_read_only_initialized_doubleword: doubleword_int -> doubleword_int option

val get_string_reference: doubleword_int -> string option

val has_export_directory_table: unit -> bool

val has_import_directory_table: unit -> bool

val is_exported: doubleword_int -> bool

val is_image_address: numerical_t -> bool

val is_read_only_address: doubleword_int -> bool

val write_xml_exn_handlers: xml_element_int -> unit

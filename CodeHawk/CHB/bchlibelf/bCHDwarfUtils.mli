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
open BCHLibTypes

(* bchlibelf *)
open BCHELFTypes


val int_to_dwarf_tag_type: int -> dwarf_tag_type_t

val int_to_dwarf_attr_type: int -> dwarf_attr_type_t

val int_to_dwarf_form_type: int -> dwarf_form_type_t

val dwarf_tag_type_to_string: dwarf_tag_type_t -> string

val string_to_dwarf_tag_type: string -> dwarf_tag_type_t

val dwarf_attr_type_to_string: dwarf_attr_type_t -> string

val string_to_dwarf_attr_type: string -> dwarf_attr_type_t

val dwarf_form_type_to_string: dwarf_form_type_t -> string

val string_to_dwarf_form_type: string -> dwarf_form_type_t

val dwarf_attr_value_to_string: dwarf_attr_value_t -> string

val abbrev_entry_to_string: debug_abbrev_table_entry_t -> string

val read_dwarf_expression: pushback_stream_int -> int -> dwarf_expr_t

val single_location_description_to_string:
  single_location_description_t -> string

val debug_compilation_unit_size: debug_compilation_unit_t -> int

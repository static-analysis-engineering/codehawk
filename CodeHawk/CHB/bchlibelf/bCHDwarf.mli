(* =============================================================================
   CodeHawk Binary Analyzer 
   Henny Sipma
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

(* bchlib *)
open BCHLibTypes

(* bchlibelf *)
open BCHDwarfTypes


val decode_debug_attribute_value:
  ?get_string:(int -> string)
  -> ?get_loclist:(int -> debug_loc_description_t)
  -> attrspec:(dwarf_attr_type_t * dwarf_form_type_t)
  -> base:doubleword_int
  -> pushback_stream_int
  -> (dwarf_attr_type_t * dwarf_attr_value_t)


val decode_variable_die:
  get_abbrev_entry:(int -> debug_abbrev_table_entry_t)
  -> ?get_string:(int -> string)
  -> ?get_loclist:(int -> debug_loc_description_t)
  -> base:doubleword_int
  -> pushback_stream_int
  -> (debug_info_entry_t)


val flatten_debug_info_entry:
  debug_info_entry_t -> debug_info_entry_t list


val decode_compilation_unit:
  get_abbrev_entry:(int -> debug_abbrev_table_entry_t)
  -> get_string:(int -> string)
  -> get_loclist:(int -> debug_loc_description_t)
  -> base:doubleword_int
  -> header:debug_compilation_unit_header_t
  -> pushback_stream_int
  -> debug_compilation_unit_t

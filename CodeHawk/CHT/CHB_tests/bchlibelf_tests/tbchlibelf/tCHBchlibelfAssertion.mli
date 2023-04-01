(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
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


val equal_abbrev_entry:
  ?msg:string
  -> expected:(int * string * bool * (string * string) list)
  -> received:debug_abbrev_table_entry_t
  -> unit
  -> unit


val equal_variable_debuginfo_entry:
  ?msg:string
  -> expected:(dwarf_attr_type_t * string) list
  -> received: debug_info_entry_t
  -> unit


val equal_debug_location_list:
  ?msg:string
  -> expected:(string * string * string) list
  -> received:debug_location_list_entry_t list
  -> unit


val equal_compilation_unit_header:
  ?msg:string
  -> expected:(string * int * string * int)
  -> received: debug_compilation_unit_header_t
  -> unit
  -> unit


val equal_compilation_unit:
  ?msg:string
  -> expected:
       (string
        * string
        * int
        * dwarf_tag_type_t
        * (dwarf_attr_type_t * string) list)
  -> received: debug_compilation_unit_t
  -> unit
  -> unit

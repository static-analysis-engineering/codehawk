(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
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

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHBCTypes
open BCHLibTypes

   
val function_interface_to_prototype_string:
  ?fullname:string option -> function_interface_t -> string

val function_interface_to_pretty: function_interface_t -> pretty_t

val read_xml_function_interface: xml_element_int -> function_interface_t

val write_xml_function_interface: xml_element_int -> function_interface_t -> unit

val modify_function_interface:
  type_transformer_t -> string -> function_interface_t -> function_interface_t

val is_stack_parameter: fts_parameter_t -> int -> bool

val get_stack_parameter:
  function_interface_t -> int -> fts_parameter_t (* index starts at 1 *)

val get_stack_parameter_name :
  function_interface_t -> int -> string          (* index starts at 1 *)

val get_stack_parameter_names: function_interface_t -> (int * string) list

val get_stack_parameter_count: function_interface_t -> int

val has_fmt_parameter: function_interface_t -> bool

val get_fmt_parameter_index: function_interface_t -> int

val demangled_name_to_function_interface: demangled_name_t -> function_interface_t

val default_function_interface:
  ?cc:string
  -> ?adj:int
  -> ?returntype:btype_t
  -> ?varargs:bool
  -> string
  -> fts_parameter_t list
  -> function_interface_t


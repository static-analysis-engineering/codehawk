(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
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

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

   
val function_api_to_prototype_string: ?fullname:string option -> function_api_t -> string
val function_api_to_pretty          : function_api_t -> pretty_t

val function_api_compare: function_api_t -> function_api_t -> int

val read_xml_function_api      : xml_element_int -> function_api_t

val modify_types_api: type_transformer_t -> string -> function_api_t -> function_api_t

val is_stack_parameter: api_parameter_t -> int -> bool

val get_stack_parameter      : function_api_t -> int -> api_parameter_t (* index starts at 1 *)
val get_stack_parameter_name : function_api_t -> int -> string          (* index starts at 1 *)
val get_stack_parameter_names: function_api_t -> (int * string) list

val get_stack_parameter_count: function_api_t -> int

val demangled_name_to_function_api: demangled_name_t -> function_api_t

val default_function_api:
  ?cc:string -> ?adj:int -> string -> api_parameter_t list -> function_api_t


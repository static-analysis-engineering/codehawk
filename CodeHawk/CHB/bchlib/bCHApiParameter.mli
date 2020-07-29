(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
open CHFormatStringParser
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

val default_api_parameter: api_parameter_t

val mk_global_parameter:
  ?btype:btype_t
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> doubleword_int
  -> api_parameter_t

(* stack parameters are numbered starting from 1 
   (located at 4 bytes above the return address) *)
val mk_stack_parameter:
  ?btype:btype_t
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> int
  -> api_parameter_t

val mk_register_parameter:
  ?btype:btype_t
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> register_t
  -> api_parameter_t

val convert_fmt_spec_arg: int -> argspec_int -> api_parameter_t

val calling_convention_to_string: calling_convention_t -> string

val api_parameter_to_pretty: api_parameter_t -> pretty_t

val parameter_location_compare:
  parameter_location_t -> parameter_location_t -> int

val api_parameter_compare: api_parameter_t -> api_parameter_t -> int

val write_xml_roles: xml_element_int -> (string * string) list -> unit

val read_xml_roles: xml_element_int -> (string * string) list

val write_xml_parameter_location:
  xml_element_int -> parameter_location_t -> unit

val read_xml_parameter_location :
  xml_element_int -> parameter_location_t

val write_xml_api_parameter: xml_element_int -> api_parameter_t -> unit

val read_xml_api_parameter: xml_element_int -> api_parameter_t

val modify_types_par: type_transformer_t -> api_parameter_t -> api_parameter_t

val modify_name_par: string -> api_parameter_t -> api_parameter_t

val is_global_parameter: api_parameter_t -> bool

val is_stack_parameter: api_parameter_t -> bool

val is_register_parameter: api_parameter_t -> bool

val is_arg_parameter: api_parameter_t -> bool

val is_formatstring_parameter: api_parameter_t -> bool



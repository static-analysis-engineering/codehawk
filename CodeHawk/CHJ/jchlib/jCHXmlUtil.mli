(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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
open CHIntervals
open CHLanguage

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI


val has_control_characters: string -> bool

val hex_string: string -> string

val replace_control_characters: string -> string

val basic_type_to_asm_string: java_basic_type_t -> string

val value_type_to_asm_string: value_type_t -> string

val object_type_to_asm_string: object_type_t -> string

val value_type_to_asm_cnix_string: value_type_t -> string

val object_type_to_asm_cnix_string: object_type_t -> string

val method_arguments_to_asm_string: method_signature_int -> string

val write_xml_indices: xml_element_int -> int list -> unit

val read_xml_indices: xml_element_int -> int list

val write_xml_variable: xml_element_int -> variable_t -> unit

val read_xml_variable: xml_element_int -> variable_t

val write_xml_constant_string : xml_element_int -> string -> string -> unit

val write_xml_asm_method_signature:
  xml_element_int -> method_signature_int -> unit

val write_xml_asm_value_types: xml_element_int -> value_type_t list -> unit

val write_xml_asm_cnix_value_types: xml_element_int -> value_type_t list -> unit

val write_xml_interval: xml_element_int -> interval_t -> unit

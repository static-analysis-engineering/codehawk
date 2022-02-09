(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Arnaud Venet and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* bchcil *)
open BCHCBasicTypes

(* bchlib *)
open BCHLibTypes


val access_to_string: access_t -> string

val java_basic_type_to_string: java_basic_type_t -> string

val value_type_to_pretty: value_type_t -> pretty_t

val java_native_method_class_to_pretty: java_native_method_class_t -> pretty_t

val get_java_type_name_prefix: value_type_t -> string

val get_java_type_length: value_type_t -> int

val get_java_type_btype: value_type_t -> btype_t

val read_xml_java_native_method_class: xml_element_int -> java_native_method_class_t

val convert_to_native_method_name: string -> string option

val get_java_class_name: string -> string option

val get_java_method_name: string -> string option

val get_java_class_method_name: string -> java_method_name_int option

val get_java_native_method_signature: string -> string list -> java_native_method_api_t option

val is_java_native_method_name: string -> bool

val get_java_classes_not_found: unit -> string list

val get_java_methods_not_found: unit -> string list

val get_java_classes_loaded: unit -> java_native_method_class_t list

val write_xml_java_classes_loaded: xml_element_int -> java_native_method_class_t list -> unit

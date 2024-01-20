(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet
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
open CHLanguage
open CHPretty

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI

exception JCH_failure of pretty_t
exception JCH_not_implemented of string
exception JCH_runtime_type_error of pretty_t
exception JCH_class_structure_error of pretty_t

val raise_jch_failure: pretty_t -> unit

val hex_string: string -> string

val compare_value_types: value_type_t -> value_type_t -> int
val compare_object_types: object_type_t -> object_type_t -> int

val java_basic_type_to_string: java_basic_type_t -> string
val java_basic_type_to_signature_string: java_basic_type_t -> string

val java_basic_type_of_string: string -> java_basic_type_t
val java_basic_type_of_signature_string: string -> java_basic_type_t

val java_basic_type_to_pretty: java_basic_type_t -> pretty_t

val access_to_string: access_t -> string
val string_to_access: string -> access_t
val access_to_pretty: access_t -> pretty_t
val value_type_to_pretty: value_type_t -> pretty_t
val value_type_to_string: value_type_t -> string
val object_type_to_string: object_type_t -> string
val object_type_to_pretty: object_type_t -> pretty_t
val object_type_to_abbreviated_pretty: object_type_t -> pretty_t
val value_type_to_abbreviated_pretty: value_type_t -> pretty_t

val descriptor_to_pretty: descriptor_t -> pretty_t

val size_of_value_type     : value_type_t -> int
val size_of_java_basic_type: java_basic_type_t -> int

val write_xmlx_basic_type : xml_element_int -> java_basic_type_t -> unit
val write_xmlx_value_type : xml_element_int -> value_type_t -> unit
val write_xmlx_object_type: xml_element_int -> object_type_t -> unit

val write_xml_visibility: xml_element_int -> access_t -> unit

val write_xmlx_constant_value: xml_element_int -> constant_value_t -> unit

val compare_value_type_lists : value_type_t list -> value_type_t list -> int

val make_stackmap:(int * verification_type_t list * verification_type_t list) ->
  stackmap_int

val make_class_name: index:int -> name:string -> class_name_int

val make_field_signature_data:
  name:string ->
  field_descriptor:value_type_t -> field_signature_data_int

val make_field_signature:
  index:int ->
  field_signature_data:field_signature_data_int -> field_signature_int

val make_method_descriptor:
  arguments:value_type_t list ->
  ?return_value:value_type_t -> unit -> method_descriptor_int

val make_method_signature_data:
  is_static:bool ->
  name:string ->
  method_descriptor:method_descriptor_int -> method_signature_data_int

val make_method_signature:
  index:int ->
  method_signature_data:method_signature_data_int -> method_signature_int

val make_class_field_signature_data:
  class_name:class_name_int ->
  field_signature:field_signature_int -> class_field_signature_data_int

val make_class_method_signature_data:
  class_name:class_name_int ->
  method_signature:method_signature_int -> class_method_signature_data_int

val make_class_field_signature:
  index:int ->
  class_field_signature_data:class_field_signature_data_int -> class_field_signature_int

val make_class_method_signature:
  index:int ->
  class_method_signature_data:class_method_signature_data_int -> class_method_signature_int

val make_procname: int -> symbol_t

val make_bootstrap_method: bootstrap_method_data_t -> bootstrap_method_int

val clinit_signature_data: method_signature_data_int
val clinit_signature: method_signature_int

val constant_value_to_pretty: constant_value_t -> pretty_t
val reference_kind_to_string: reference_kind_t -> string
val method_handle_to_pretty: method_handle_type_t -> pretty_t
val constant_to_pretty: constant_t -> pretty_t
val bootstrap_argument_to_pretty: bootstrap_argument_t -> pretty_t

val jch_permissive: bool ref
val set_permissive: bool -> unit
val is_permissive: unit -> bool

val default_varname_mapping: int -> string
val default_argname_mapping: int -> string

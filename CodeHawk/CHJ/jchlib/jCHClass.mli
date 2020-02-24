(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet
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

(* jchlib *)
open JCHBasicTypesAPI

val make_class_field:
  signature:field_signature_int ->
  class_signature:class_field_signature_int ->
  generic_signature:field_type_signature_int option ->
  access:access_t ->
  is_static:bool ->
  is_final:bool ->
  is_synthetic:bool ->
  is_enum:bool ->
  kind:field_kind_t ->
  value:constant_value_t option ->
  is_transient:bool ->
  annotations:(annotation_t * bool) list ->
  other_flags:int list ->
  attributes:attributes_int -> field_int


val make_interface_field:
  signature:field_signature_int ->
  class_signature:class_field_signature_int ->
  generic_signature:field_type_signature_int option ->
  is_synthetic:bool ->
  is_final:bool ->
  value:constant_value_t option ->
  annotations: (annotation_t * bool) list ->
  other_flags: int list ->
  attributes:attributes_int -> field_int


val make_inner_class:
  ?name:class_name_int ->
  ?outer_class_name:class_name_int ->
  ?source_name:string ->
  access:access_t ->
  is_static:bool ->
  is_final:bool ->
  is_synthetic:bool ->
  is_annotation:bool ->
  is_enum:bool ->
  other_flags:int list ->
  kind:inner_class_kind_t -> unit -> inner_class_int

val make_java_class:
  name:class_name_int ->
  version:version_t ->
  access:access_t ->
  is_final:bool ->
  is_abstract:bool ->
  super_class:class_name_int option ->
  generic_signature:class_signature_int option ->
  fields:field_int list ->
  interfaces:class_name_int list ->
  consts:constant_t array ->
  ?source_file:string ->
  source_origin:string ->
  md5_digest:string ->
  is_deprecated:bool ->
  ?enclosing_method:(class_name_int * method_signature_int option) ->
  ?source_debug_extension:string ->
  inner_classes:inner_class_int list ->
  is_synthetic:bool ->
  is_enum:bool ->
  annotations:(annotation_t * bool) list ->
  bootstrapmethods:bootstrap_method_int list ->
  other_flags:int list ->
  other_attributes:(string * string) list ->
  methods:method_int list -> unit -> java_class_or_interface_int

val make_java_interface:
  name:class_name_int ->
  version:version_t ->
  access:access_t ->
  interfaces:class_name_int list ->
  generic_signature:class_signature_int option ->
  consts:constant_t array ->
  ?source_file:string ->
  source_origin:string ->
  md5_digest:string ->
  is_deprecated:bool ->
  ?source_debug_extension:string ->
  inner_classes:inner_class_int list ->
  ?initializer_method:method_int ->
  is_annotation:bool ->
  annotations:(annotation_t * bool) list ->
  bootstrapmethods:bootstrap_method_int list ->
  other_attributes:(string * string) list ->
  other_flags:int list ->
  fields:field_int list ->
  methods:method_int list -> unit -> java_class_or_interface_int

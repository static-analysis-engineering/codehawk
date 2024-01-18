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
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI


val implementation_to_pretty : implementation_t -> pretty_t

val make_attributes:
  is_synthetic:bool -> is_deprecated:bool -> other:(string * string) list ->
  attributes_int

val make_method_annotations:
  global:(annotation_t * bool) list ->
  parameters:(annotation_t * bool) list list ->
  method_annotations_int

val make_concrete_method:
  signature:method_signature_int ->
  class_method_signature:class_method_signature_int ->
  access:access_t ->
  is_static:bool ->
  is_final:bool ->
  is_synchronized:bool ->
  is_strict:bool ->
  ?generic_signature:method_type_signature_int ->
  is_bridge:bool ->
  has_varargs:bool ->
  is_synthetic:bool ->
  other_flags:int list ->
  exceptions:class_name_int list ->
  attributes:attributes_int ->
  annotations:method_annotations_int ->
  implementation:implementation_t -> unit -> method_int

val make_abstract_method:
  signature:method_signature_int ->
  class_method_signature:class_method_signature_int ->
  access:access_t ->
  ?annotation_default:element_value_t ->
  ?generic_signature:method_type_signature_int ->
  is_bridge:bool ->
  has_varargs:bool ->
  is_synthetic:bool ->
  other_flags:int list ->
  exceptions:class_name_int list ->
  attributes:attributes_int ->
  annotations:method_annotations_int -> unit -> method_int

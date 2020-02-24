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

(* chlib *)
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI


val make_type_variable: string -> type_variable_int

val make_simple_class_type_signature:
  name:string -> type_arguments:type_argument_int list -> simple_class_type_signature_int

val make_class_type_signature:
  package:string list -> enclosing_classes:simple_class_type_signature_int list ->
  simple_class_type_signature:simple_class_type_signature_int -> class_type_signature_int

val make_formal_type_parameter:
  name:string -> ?class_bound:field_type_signature_int ->
  interface_bounds:field_type_signature_int list -> unit -> formal_type_parameter_int

val make_type_argument:
  ?field_type_signature:field_type_signature_int ->
  kind:type_argument_kind_t -> unit -> type_argument_int

val make_throws_signature:
  ?class_type_signature:class_type_signature_int ->
  ?type_variable:type_variable_int -> kind:throws_signature_kind_t -> unit ->
  throws_signature_int

val make_type_signature:
  ?basic_type:java_basic_type_t -> ?object_type:field_type_signature_int ->
  kind:type_signature_kind_t -> unit -> type_signature_int

val make_field_type_signature:
  ?class_type:class_type_signature_int -> ?array_type:type_signature_int ->
  ?type_variable:type_variable_int -> kind:field_type_signature_kind_t ->
  unit -> field_type_signature_int

val make_class_signature:
  formal_type_parameters:formal_type_parameter_int list ->
  super_class:class_type_signature_int ->
  super_interfaces:class_type_signature_int list -> class_signature_int

val make_method_type_signature:
  formal_type_parameters:formal_type_parameter_int list ->
  type_signature:type_signature_int list ->
  ?return_type: type_signature_int ->
  throws:throws_signature_int list -> unit -> method_type_signature_int

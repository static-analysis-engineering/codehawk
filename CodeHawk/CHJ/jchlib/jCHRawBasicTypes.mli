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

val write_ui8 : 'a IO.output -> int -> unit
val write_i8 : 'a IO.output -> int -> unit

val write_string_with_length :
  ('a IO.output -> int -> unit) -> 'a IO.output -> string -> unit

val write_with_length :
  ('a IO.output -> int -> unit) ->
  'a IO.output -> (string IO.output -> unit) -> unit

val write_with_size :
  ('a IO.output -> int -> unit) ->
  'a IO.output -> ('b -> unit) -> 'b list -> unit

val get_constant : constant_t array -> int -> constant_t

val get_constant_value : constant_t array -> int -> constant_value_t

val get_object_type : constant_t array -> int -> object_type_t

val get_class : constant_t array -> int -> class_name_int

val get_field : constant_t array -> int -> class_name_int * field_signature_int

val get_method : constant_t array -> int -> object_type_t * method_signature_int

val get_method_handle: constant_t array -> int -> reference_kind_t * method_handle_type_t

val get_bootstrap_argument: constant_t array -> int -> bootstrap_argument_t

val get_callsite_specifier: constant_t array -> int -> (int * method_signature_int)

val get_interface_method : constant_t array -> int -> class_name_int * method_signature_int

val get_string : constant_t array -> int -> string

val get_class_ui16 : constant_t array -> IO.input -> class_name_int

val get_string_ui16 : constant_t array -> IO.input -> string

val constant_to_int : constant_t DynArray.t -> constant_t -> int

val value_to_int : constant_t DynArray.t -> constant_value_t -> int

val object_type_to_int : constant_t DynArray.t -> object_type_t -> int

val field_to_int : constant_t DynArray.t -> class_name_int * field_signature_int -> int

val method_to_int : constant_t DynArray.t -> object_type_t * method_signature_int -> int

val class_to_int : constant_t DynArray.t -> class_name_int -> int

val string_to_int : constant_t DynArray.t -> string -> int

val name_and_type_to_int : constant_t DynArray.t -> string * descriptor_t -> int

val write_constant : 'a IO.output -> constant_t DynArray.t -> constant_t -> unit

val write_value : 'a IO.output -> constant_t DynArray.t -> constant_value_t -> unit

val write_object_type : 'a IO.output -> constant_t DynArray.t -> object_type_t -> unit

val write_class : 'a IO.output -> constant_t DynArray.t -> class_name_int -> unit

val write_string : 'a IO.output -> constant_t DynArray.t -> string -> unit

val write_name_and_type : 
  'a IO.output -> constant_t DynArray.t ->  string * descriptor_t -> unit


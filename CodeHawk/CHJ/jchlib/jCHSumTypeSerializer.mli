(* =============================================================================
   CodeHawk Java Analyzer 
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
open CHLanguage
   
(* jchlib *)
open JCHBasicTypesAPI

val mk_sumtype_string_converter:
  string -> ('a * string) list -> 'a sumtype_string_converter_int

val mk_fn_sumtype_string_converter:
  string -> ('a * string) list -> ('a -> string) -> (string -> 'a) ->
  'a sumtype_string_converter_int

val java_basic_type_serializer: java_basic_type_t sumtype_string_converter_int
val reference_kind_serializer: reference_kind_t sumtype_string_converter_int
  
val object_type_serializer: object_type_t sumtype_string_converter_int
val value_type_serializer: value_type_t sumtype_string_converter_int
val constant_value_serializer: constant_value_t sumtype_string_converter_int
val descriptor_serializer: descriptor_t sumtype_string_converter_int
val method_handle_type_serializer: method_handle_type_t sumtype_string_converter_int
val constant_serializer: constant_t sumtype_string_converter_int
val bootstrap_argument_serializer: bootstrap_argument_t sumtype_string_converter_int

val opcode_serializer: opcode_t sumtype_string_converter_int
  
val arithmetic_op_serializer: arithmetic_op_t sumtype_string_converter_int
val relational_op_serializer: relational_op_t sumtype_string_converter_int
val jterm_serializer: jterm_t sumtype_string_converter_int

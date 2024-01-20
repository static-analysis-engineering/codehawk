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


val name_of_opcode: opcode_t -> string
val opcode_to_opcode_index_string: opcode_t -> string
val opcode_to_opcode_index: opcode_t -> int
val hex_of_opcode: opcode_t -> string
val hex_of_arithmetic_opcode: opcode_t -> string
val opcode_arg_types: opcode_t -> value_type_t list

val opcode_to_pretty: opcode_t -> pretty_t
val opcode_to_string: opcode_t -> string
val invert_conditional_opcode: opcode_t -> opcode_t

val is_binop_opcode: opcode_t -> bool
val is_arithmetic_binop_opcode: opcode_t  -> bool
val is_logical_binop_opcode: opcode_t -> bool
val is_converter_opcode: opcode_t -> bool
val is_test_opcode: opcode_t -> bool
val is_backward_test_opcode: opcode_t -> bool
val is_unary_test_opcode: opcode_t -> bool
val is_forward_unary_test_opcode: opcode_t -> bool
val is_binary_test_opcode: opcode_t -> bool
val is_forward_binary_test_opcode: opcode_t -> bool
val is_comparison_opcode: opcode_t -> bool

val get_target_offset: opcode_t -> int

val make_exception_handler:
  h_start:int ->
  h_end:int ->
  handler:int ->
  ?catch_type:class_name_int -> unit -> exception_handler_int

val make_opcodes: opcode_t array -> opcodes_int

val make_bytecode:
  max_stack:int ->
  max_locals:int ->
  code:opcodes_int ->
  exception_table:exception_handler_int list ->
  ?line_number_table:(int * int) list ->
  ?local_variable_table:(int * int * string * value_type_t * int) list ->
  ?local_variable_type_table:(int * int * string * field_type_signature_int * int) list ->
  ?stack_map_midp:stackmap_int list ->
  ?stack_map_java6:stackmap_int list ->
  attributes:(string * string) list -> unit -> bytecode_int

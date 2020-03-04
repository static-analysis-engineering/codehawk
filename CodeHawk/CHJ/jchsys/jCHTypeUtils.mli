(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
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
open CHIntervals
open CHLanguage
open CHUtils

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

val get_object_vt: unit -> value_type_t 
val get_string_vt: unit -> value_type_t 
val get_throwable_vt: unit -> value_type_t 

val bool_interval: interval_t
val byte_interval: interval_t
val short_interval: interval_t
val char_interval: interval_t
val integer_interval: interval_t
val long_interval: interval_t
val length_interval: interval_t

val get_interval_from_type: value_type_t option -> interval_t
val get_var_interval_from_type: variable_t -> value_type_t option -> interval_t

val is_primitive: value_type_t -> bool
val is_primitive_not_bool_opt: value_type_t option -> bool
val is_primitive_not_bool: value_type_t -> bool
val get_array_dim: value_type_t -> int option

val get_numeric_type: class_name_int -> java_basic_type_t option
val is_collection_class: class_name_int -> bool
val is_collection_type: value_type_t -> bool
val can_be_collection: value_type_t list -> bool

val merge_types: value_type_t list -> value_type_t list -> value_type_t list
val make_type_list: value_type_t -> value_type_t list
val make_int_type_list: value_type_t -> value_type_t list
val get_compact_type: value_type_t list -> value_type_t list
val equal_value_type_lists: value_type_t list -> value_type_t list -> bool

val is_float_type: value_type_t -> bool
val can_be_float: value_type_t list -> bool

val is_immutable_type: value_type_t list -> bool

val get_class_info: class_name_int -> class_info_int
val get_class_info_opt: class_name_int -> class_info_int option
val is_subclass: class_name_int -> class_name_int -> bool
val is_compatible: class_name_int -> class_name_int -> bool
val is_subtype: value_type_t -> value_type_t -> bool
val is_strict_subtype: value_type_t -> value_type_t -> bool
val is_int_subtype: value_type_t -> value_type_t -> bool

val is_bool: value_type_t -> bool
val is_byte: value_type_t -> bool
val is_short: value_type_t -> bool
val is_char: value_type_t -> bool
val is_int: value_type_t -> bool
val is_long: value_type_t -> bool

val is_array: value_type_t -> bool

val is_class_with_length: class_name_int -> bool
val is_type_with_length: value_type_t -> bool

val get_types_from_stack_info :
  symbol_t
  -> procedure_int 
  -> VariableCollections.set_t VariableCollections.table_t
  -> (int * (value_type_t list * bool)) list

val get_invocation_object_type :
  method_info_int -> instruction_info_int -> int -> value_type_t list

val get_basic_type : value_type_t list -> value_type_t option * bool

val sub_value_type_lists : value_type_t list -> value_type_t list -> bool

(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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
open JCHFile

(* jchpre *)
open JCHPreAPI

val startup_classes: string list

val is_main_method: string -> bool

val has_main_method: java_class_or_interface_int -> bool

val is_valid_class_name: string -> bool

val is_sun_class_name: string -> bool

val get_class_name_from_value_type: value_type_t -> class_name_int option

val is_same_package: class_name_int -> class_name_int -> bool

val is_descendant_of: class_name_int -> class_name_int -> bool

val implements_interface: class_name_int -> class_name_int -> bool

val get_class_summary_codependents: class_summary_int -> class_name_int list

val get_class_codependents: java_class_or_interface_int -> class_name_int list

val is_sql_interface: class_name_int -> bool

val is_dynamic_class_loading: class_method_signature_int -> bool

val is_system_getProperty_call: class_method_signature_int -> bool

val get_classes_referenced: method_info_int -> class_name_int list

val get_methods_referenced: method_info_int -> class_method_signature_int list

val get_fields_referenced: method_info_int -> class_field_signature_int list

val get_signature_classes: method_signature_int -> class_name_int list

val inherits_from_final_method: class_method_signature_int -> bool

val get_classes_referenced_in_summary:
  cp_unit_t list
  -> ((class_name_int * class_summary_int)
      * (class_field_signature_int * field_stub_int) list
      * (class_method_signature_int * loop_info_t list * function_summary_int) list)
  -> (class_name_int list * string list)

val get_invokeinterface_classes:
  class_name_int -> class_name_int list -> class_name_int list

val get_invokevirtual_classes:
  class_name_int -> class_name_int list -> class_name_int list

val get_vcall_classes: function_summary_int -> class_name_int list

val set_dynamically_dispatched_methods: unit -> unit

val set_main_method: unit -> unit

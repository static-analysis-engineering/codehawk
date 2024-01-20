(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
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
open CHIntervals
open CHLanguage
open CHUtils

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI


val dbg : bool ref

val make_numeric_analysis: bool -> unit

val is_unreachable:  symbol_t -> variable_t -> bool

val get_local_var_maps:
  symbol_t -> variable_t VariableCollections.table_t IntCollections.table_t

val get_method_arg_bounds:
  int
  -> int
  -> (jterm_t * jterm_t list) list * (jterm_t * jterm_t list) list

val get_iteration_bounds: int -> int -> jterm_t list * jterm_t list

val get_pos_terms: int -> int -> jterm_t list

val set_pos_fields: unit -> unit

val is_pos_field: jterm_t -> bool

val get_pos_field_interval: jterm_t -> interval_t option

val save_xml_class_cost_support: class_info_int -> unit

val load_xml_class_cost_support: unit -> unit

val save_xml_class_taint_support: class_info_int -> unit

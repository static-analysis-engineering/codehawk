(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny Sipma

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
open CHUtils

(* chutil *)
open CHXmlDocument

(* jchpre *)
open JCHPreAPI

val set_use_one_top_target : bool -> unit

val taint_dictionary: taint_dictionary_int

val mk_var_origin        : symbol_t -> variable_t -> taint_origin_int
val mk_field_origin      : field_info_int -> string -> symbol_t -> int -> taint_origin_int
val mk_call_origin       : method_info_int -> string -> symbol_t -> int -> taint_origin_int
val mk_top_target_origin : method_target_int -> symbol_t -> int -> taint_origin_int
val mk_stub_origin       : symbol_t -> symbol_t -> int -> taint_origin_int

val mk_taint_origin    : taint_origin_type_t -> taint_origin_int
val mk_taint_origin_set: taint_origin_int list -> taint_origin_set_int

val mk_tainted_variable: tainted_variable_data_t -> tainted_variable_int

val get_taint_origin: int -> taint_origin_int
val get_taint_origin_set: int -> taint_origin_set_int
val join_taint_origin_sets: taint_origin_set_int -> taint_origin_set_int -> taint_origin_set_int
val is_taint_origin_subset: taint_origin_set_int -> taint_origin_set_int -> bool
val get_tainted_variable: int -> tainted_variable_int

val get_number_origins: unit -> int
val get_taint_origins: unit -> (int, taint_origin_int) Hashtbl.t
val taint_origins_to_pretty: unit -> pretty_t  

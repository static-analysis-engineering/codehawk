(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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
open CHLogger

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

val set_dbg_on : unit -> unit
val is_dbg_on : unit -> bool
val pr__debug : pretty_t list -> unit

val op_args_to_pretty :
  (string * < toPretty : pretty_t; .. > * arg_mode_t) list -> pretty_t

val operation_to_pretty : operation_t -> pretty_t

val pp_bool : bool -> pretty_t

val bl : pretty_t

val option_to_pretty :
  < toPretty : pretty_t; .. > option -> pretty_t

val option_to_pretty_str : string option -> pretty_t

val postcond_preds_to_pretty : postcondition_predicate_t list -> pretty_t
val precond_preds_to_pretty  : precondition_predicate_t list -> pretty_t
val side_effects_to_pretty   : sideeffect_t list -> pretty_t

val proc_name_str : symbol_t -> string
val proc_name_pp : symbol_t -> pretty_t
val proc_set_pp :
  SymbolCollections.set_t -> pretty_t
val proc_table_pp :
  < toPretty : pretty_t; .. > SymbolCollections.table_t -> pretty_t
val proc_ltable_pp :
  < toPretty : pretty_t; size : int; .. > SymbolCollections.table_t -> pretty_t
val proc_list_pp : symbol_t list -> pretty_t

val dot_name : symbol_t -> string

val pp_var_table :
  (int * int * string * value_type_t * int) list option -> pretty_t

val pp_pc_table : < toPretty : pretty_t; .. > IntCollections.table_t ->
  pretty_t

val pp_procpc_table :
  < toPretty : pretty_t; .. > IntCollections.table_t SymbolCollections.table_t ->
  pretty_t


class pretty_int_t :
  int ->
  object
      method int : int
      method toPretty : pretty_t
  end

class pretty_string_t :
  string ->
  object
      method str : string
      method toPretty : pretty_t
  end

class pretty_var_list_t :
  variable_t list ->
  object
    method vars : variable_t list
    method toPretty : pretty_t
  end

class pretty_op_t :
  operation_t ->
  object
    method op : operation_t
    method toPretty : pretty_t
  end


val string_of_pretty : pretty_t list -> string

val string_of_sym : symbol_t -> string

val pp_var_table_pred :
  < toPretty : pretty_t ; ..>  VariableCollections.table_t
                          -> (variable_t -> bool)
                          -> pretty_t

val pp_assoc_list_vars : (variable_t * variable_t) list -> pretty_t

val pp_assoc_list_ints : (int * int) list -> pretty_t

val pp_assoc_list_var_int : (variable_t * int) list -> pretty_t

val read_int_to_var_set :
  string -> VariableCollections.set_t IntCollections.table_t

val read_int_to_int_set :
  string -> IntCollections.set_t IntCollections.table_t

val read_int_to_var_to_var :
  string -> variable_t VariableCollections.table_t IntCollections.table_t

val read_int_to_string_set :
  string -> StringCollections.set_t IntCollections.table_t

val jch_stats_log : logger_int

val jterm_to_string : jterm_t -> string
val relational_expr_to_string : relational_expr_t -> string

val pr__debug_large_table :
  ('a -> unit) -> < listOfPairs : (int * 'a) list; .. > -> unit

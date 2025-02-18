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
open CHIntervals
open CHLanguage
open CHPretty
open CHUtils

(* jchpre *)
open JCHPreAPI

type stub_condition_t =
  | CheckReturnType
  | CopyInfo of variable_t * variable_t
  | JoinInfo of variable_t * variable_t * variable_t
  | PostInterval of variable_t * interval_t
  | Abstract of variable_t

val stub_condition_to_pretty : stub_condition_t -> CHPretty.pretty_t

class int_stub_t :
  stub_name:symbol_t ->
  vars:variable_t list ->
  vars_with_lengths:variable_t list ->
  lengths:variable_t list ->
  return_var_opt:variable_t option ->
  return_lengths_ope:variable_t option ->
    object
      method get_extra_conds : stub_condition_t list
      method get_lengths : variable_t list
      method get_poly_int_array : JCHPolyIntervalArray.poly_interval_array_t
      method get_stub_name : symbol_t
      method get_vars : variable_t list
      method get_vars_with_lengths : variable_t list
      method set_extra_conds : stub_condition_t list -> unit
      method set_poly_int_array :
               JCHPolyIntervalArray.poly_interval_array_t -> unit
      method toPretty : pretty_t
    end

class int_stub_manager_t :
  object
    method are_recursive_calls_included_in_calls : symbol_t -> bool
    method get_all_call_vars :
             symbol_t
             -> variable_t list
                * variable_t list
                * variable_t VariableCollections.table_t

    method get_lib_stubs : int_stub_t list
    method get_lib_func_summaries : function_summary_int list
    method get_stub : symbol_t -> int_stub_t option
    method get_widening_call_poly_int_array :
             bool
             -> symbol_t
             -> bool
             -> JCHPolyIntervalArray.poly_interval_array_t option

    method get_narrowing_call_poly_int_array :
             symbol_t
             -> bool
             -> JCHPolyIntervalArray.poly_interval_array_t option

    method invoke_poly_int_array :
             JCHProcInfo.jproc_info_t
             -> symbol_t list
             -> function_summary_int list
             -> (JCHPolyIntervalArray.poly_interval_array_t option)
                * (variable_t list)
                * (variable_t list)
                * (JCHPolyIntervalArray.poly_interval_array_t option)
                * (variable_t list) * (variable_t list)
                * stub_condition_t list

    method mk_lib_stub : function_summary_int -> int_stub_t
    method mk_poly_int_array_stub :
             procedure_int
             -> JCHPolyIntervalArray.poly_interval_array_t
             -> unit

    method record_poly_int_array_call :
             symbol_t
             -> symbol_t
             -> JCHPolyIntervalArray.poly_interval_array_t -> unit

    method mk_proc_call : procedure_int -> unit
    method reset_calls : unit
    method reset_recursive_calls : symbol_t -> unit
    method toPretty : pretty_t
  end

val int_stub_manager : int_stub_manager_t

val dbg : bool ref

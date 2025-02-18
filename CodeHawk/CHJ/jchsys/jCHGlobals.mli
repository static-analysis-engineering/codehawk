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
open CHNumerical

val make_variable : string -> variable_type_t -> variable_t

val exception_var : variable_t
val num_return_var : variable_t
val sym_return_var : variable_t

val exception_var_index : int
val num_return_var_index : int
val sym_return_var_index : int

val exception_sym : symbol_t
val return_sym : symbol_t
val throw_sym : symbol_t

val exception_sym_index : int
val return_sym_index : int
val throw_sym_index : int

val cN0 : numerical_t
val cN1 : numerical_t
val cN_1 : numerical_t
val cN_MAX_CHAR : numerical_t
val cN_MAX_BYTE : numerical_t
val cN_MIN_BYTE : numerical_t
val cN_MAX_SHORT : numerical_t
val cN_MIN_SHORT : numerical_t
val cN_MAX_INT : numerical_t
val cN_MIN_INT : numerical_t
val cN_MAX_LONG : numerical_t
val cN_MIN_LONG : numerical_t

val cN0_var : variable_t
val cN1_var : variable_t
val cN_1_var : variable_t
val cN_MAX_CHAR_var : variable_t
val cN_MAX_BYTE_var : variable_t
val cN_MIN_BYTE_var : variable_t
val cN_MAX_SHORT_var : variable_t
val cN_MIN_SHORT_var : variable_t
val cN_MAX_INT_var : variable_t
val cN_MIN_INT_var : variable_t
val cN_MAX_LONG_var : variable_t
val cN_MIN_LONG_var : variable_t

val initialize_sym : symbol_t
val finalize_sym : symbol_t
val phi_sym : symbol_t
val final_phi_sym : symbol_t
val initial_assigns_sym : symbol_t
val final_assigns_sym : symbol_t
val enter_state_sym : symbol_t
val enter_final_state_sym : symbol_t
val exit_state_sym : symbol_t
val init_consts_sym : symbol_t
val normal_exit_sym : symbol_t
val method_exit_sym : symbol_t
val exceptional_exit_sym : symbol_t
val method_entry_sym : symbol_t
val top_sym : symbol_t
val root_sym : symbol_t
val proc_name_sym : symbol_t
val state_name_sym : symbol_t
val check_cast_sym : symbol_t

val init_params_sym : symbol_t
val init_assumptions_sym : symbol_t
val loop_cond_sym : symbol_t
val check_loop_sym : symbol_t
val exit_loop_sym : symbol_t
val new_array_sym : symbol_t
val exit_sym : symbol_t
val add_vars_sym : symbol_t
val remove_vars_sym : symbol_t
val save_interval_sym : symbol_t

val taint_dom_name : string
val int_dom_name : string
val lin_dom_name : string
val poly_dom_name : string
val lin_eqs_dom_name : string

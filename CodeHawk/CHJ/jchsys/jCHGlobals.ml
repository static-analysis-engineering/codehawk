(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2025  Henny B. sipma

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

open Big_int_Z

(* chlib *)
open CHLanguage
open CHNumerical


let make_variable str vt =
  let sym =
    match vt with
    | SYM_VAR_TYPE -> new symbol_t ~atts:["sym"] str
    | _ -> new symbol_t ~atts:["num"] str in
  new variable_t sym vt

let exception_var =
  let name = new symbol_t ~atts:["sym"] "exception" in
  new variable_t name SYM_VAR_TYPE

let num_return_var =
  let name = new symbol_t ~atts:["num"] "return" in
  new variable_t name NUM_VAR_TYPE

let sym_return_var =
  let name = new symbol_t ~atts:["sym"] "return" in
  new variable_t name SYM_VAR_TYPE

let exception_var_index = exception_var#getIndex
let num_return_var_index = num_return_var#getIndex
let sym_return_var_index = sym_return_var#getIndex

let return_sym = new symbol_t "return"
let exception_sym = new symbol_t "exception"
let throw_sym = new symbol_t "throw"

let return_sym_index = return_sym#getIndex
let exception_sym_index = exception_sym#getIndex
let throw_sym_index = throw_sym#getIndex

let cN0 = mkNumerical_big (big_int_of_int 0)
let cN1 = mkNumerical_big (big_int_of_int 1)
let cN_1 = mkNumerical_big (big_int_of_int (-1))
let cN_MAX_CHAR = mkNumerical_big (big_int_of_int 65535)
let cN_MAX_BYTE = mkNumerical_big (big_int_of_int 127)
let cN_MIN_BYTE = mkNumerical_big (big_int_of_int (-128))
let cN_MAX_SHORT = mkNumerical_big (big_int_of_int 32767)
let cN_MIN_SHORT = mkNumerical_big (big_int_of_int (-32768))
let cN_MAX_INT = mkNumerical_big (big_int_of_int 2147483647)
let cN_MIN_INT = mkNumerical_big (big_int_of_int (-2147483648))
let cN_MAX_LONG = mkNumerical_big (big_int_of_string "9223372036854775807")
let cN_MIN_LONG = mkNumerical_big (big_int_of_string "-9223372036854775808")

let cN0_var = make_variable "cN0" NUM_VAR_TYPE
let cN1_var = make_variable "cN1" NUM_VAR_TYPE
let cN_1_var = make_variable "cN-1" NUM_VAR_TYPE
let cN_MAX_CHAR_var = make_variable "cN_MAX_CHAR" NUM_VAR_TYPE
let cN_MAX_BYTE_var = make_variable "cN_MAX_BYTE" NUM_VAR_TYPE
let cN_MIN_BYTE_var = make_variable "cN_MIN_BYTE" NUM_VAR_TYPE
let cN_MAX_SHORT_var = make_variable "cN_MAX_SHORT" NUM_VAR_TYPE
let cN_MIN_SHORT_var = make_variable "cN_MIN_SHORT" NUM_VAR_TYPE
let cN_MAX_INT_var = make_variable "cN_MAX_INT" NUM_VAR_TYPE
let cN_MIN_INT_var = make_variable "cN_MIN_INT" NUM_VAR_TYPE
let cN_MAX_LONG_var = make_variable "cN_MAX_LONG" NUM_VAR_TYPE
let cN_MIN_LONG_var = make_variable "cN_MIN_LONG" NUM_VAR_TYPE

let initial_assigns_sym = new symbol_t "initial_assigns"
let final_assigns_sym = new symbol_t "final_assigns"
let enter_state_sym = new symbol_t "enter_state"
let enter_final_state_sym = new symbol_t "enter_final_state"
let exit_state_sym = new symbol_t "exit_state"
let init_consts_sym = new symbol_t "init_consts"
let normal_exit_sym = new symbol_t "normal-exit"
let method_exit_sym = new symbol_t "method-exit"
let exceptional_exit_sym = new symbol_t "exceptional-exit"
let method_entry_sym = new symbol_t "method_entry_pc=0"
let check_cast_sym = new symbol_t "check_cast"

let initialize_sym = new symbol_t "initialize"
let finalize_sym = new symbol_t "finalize"
let phi_sym = new symbol_t "phi"
let final_phi_sym = new symbol_t "final_phi"
let init_params_sym = new symbol_t "init_params"
let init_assumptions_sym = new symbol_t "init_assumptions"
let loop_cond_sym = new symbol_t "loop_cond"
let check_loop_sym = new symbol_t "check_loop"
let exit_loop_sym = new symbol_t "exit_loop"
let new_array_sym = new symbol_t "new_array"
let exit_sym = new symbol_t "exit"
let add_vars_sym = new symbol_t "add_vars"
let remove_vars_sym = new symbol_t "remove_vars"
let save_interval_sym = new symbol_t "save_interval"
let root_sym = new symbol_t "root"
let top_sym = new symbol_t "top"
let proc_name_sym = new symbol_t "proc_name"
let state_name_sym = new symbol_t "state_name"

let taint_dom_name = "taint"
let int_dom_name = "tintervals"
let lin_dom_name = "karr"
let poly_dom_name = "poly"
let lin_eqs_dom_name = "lin_eqs"

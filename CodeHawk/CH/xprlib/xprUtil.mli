(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHPEPRTypes

(* chutil *)
open CHNestedCommands

(* xprlib *)
open XprTypes

val substitute_expr: substitution_t -> xpr_t -> xpr_t
val occurs_check: variable_t -> xpr_t -> bool

val xpr2numexpr: tmp_provider_t -> cst_provider_t -> xpr_t -> code_num_t
val xpr2numvar : tmp_provider_t -> cst_provider_t -> xpr_t -> code_var_t
val xpr2boolexpr: tmp_provider_t -> cst_provider_t -> xpr_t -> code_bool_t

val xpr_to_numexpr: tmp_provider_t -> cst_provider_t -> xpr_t -> (cmd_t list * numerical_exp_t)
val xpr_to_numvar : tmp_provider_t -> cst_provider_t -> xpr_t -> (cmd_t list * variable_t)
val xpr_to_boolexpr: tmp_provider_t -> cst_provider_t -> xpr_t -> (cmd_t list * boolean_exp_t)

val get_pepr_range_xprs: pepr_params_int -> pepr_range_int -> pepr_xpr_extract
val get_pepr_dependency_xprs: pepr_params_int -> param_constraint_set_int -> xpr_t list

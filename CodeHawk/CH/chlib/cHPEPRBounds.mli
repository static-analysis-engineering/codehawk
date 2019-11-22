(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Henny Sipma
   -----------------------------------------------------------------------------
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
  ============================================================================== *)

(* chlib *)
open CHIntervals
open CHLanguage
open CHNumerical
open CHPEPRTypes
open CHPretty

val mk_pepr_params: variable_t list -> pepr_params_int

val mk_param_constraint_set: param_constraint_int list -> param_constraint_set_int
val top_param_constraint_set: param_constraint_set_int

val mk_pex: coeff_vector_int -> numerical_t -> bound_type_t -> pex_int
val mk_number_pex_lb: numerical_t -> pex_int
val mk_number_pex_ub: numerical_t -> pex_int

val xtop_pepr_bound: pepr_bound_int
val mk_number_pepr_bound_lb: numerical_t -> pepr_bound_int
val mk_number_pepr_bound_ub: numerical_t -> pepr_bound_int
val mk_parameter_pepr_bound_lb: int -> int -> pepr_bound_int
val mk_parameter_pepr_bound_ub: int -> int -> pepr_bound_int

(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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

(* xprlib *)
open XprTypes


val int_constant_expr: int -> xpr_t
val num_constant_expr: numerical_t -> xpr_t
val sym_constant_expr: symbol_t -> xpr_t
val random_constant_expr: xpr_t
val unknown_int_constant_expr: xpr_t
val zero_constant_expr: xpr_t
val one_constant_expr: xpr_t
val true_constant_expr: xpr_t
val false_constant_expr: xpr_t

val get_const: xpr_t -> numerical_t option

val get_conjuncts: xpr_t -> xpr_t list
val get_disjuncts: xpr_t -> xpr_t list

val variables_in_expr: xpr_t -> variable_t list
val vars_in_expr_list: xpr_t list -> variable_t list

val loop_counters_in_expr: xpr_t -> variable_t list

val is_zero: xpr_t -> bool
val is_one: xpr_t -> bool
val is_intconst: xpr_t -> bool
val is_random: xpr_t -> bool
val is_true: xpr_t -> bool
val is_false: xpr_t -> bool

val is_conjunction: xpr_t -> bool
val is_disjunction: xpr_t -> bool

val syntactic_comparison: xpr_t -> xpr_t -> int
val syntactically_equal : xpr_t -> xpr_t -> bool

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

open Big_int_Z

(* chlib *)
open CHIntervals
open CHLanguage
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

class linear_constraint_t :
bool -> (int * big_int) list -> big_int ->
object ('a)
  method compare : 'a -> int
  method get_max_and_nr_coeffs : big_int * int
  method get_pairs_const : (int * big_int) list * big_int
  method get_used_indices : int list
  method get_v_interval : (int * interval_t) option
  method has_index : int -> bool
  method is_1_geq_0 : bool
  method is_0_geq_0 : bool
  method is_const : bool
  method is_const_equality : bool
  method is_equality : bool
  method is_interval : bool
  method is_small : bool
  method number_pairs : int
  method remap : (int * int) list -> linear_constraint_t
  method toPretty : pretty_t
  method to_array : int -> bool * big_int array
  method to_pretty :  variable_t array -> pretty_t
  method to_string : string

  method to_pre_predicate :
           (int * int) list
           -> (int * int) list
           -> (int * int) list
           -> (int * string) list
           -> (int * string) list
	   -> precondition_predicate_t

  method to_post_predicate :
           (int * int) list
           -> (int * int) list
           -> (int * int) list
           -> (int * string) list
           -> (int * string) list
	   -> postcondition_predicate_t

  method to_relational_expr :
           (int * int) list
           -> (int * int) list
           -> (int * int) list
           -> (int * string) list
           -> (int * string) list
	   -> JCHBasicTypesAPI.relational_expr_t

  method replace_consts : (int * big_int) list -> 'a
end

val mk_arg_constraint_from_rel_expr :
  (string * int) list
  -> (int * value_type_t list) list
  -> relational_expr_t
  -> linear_constraint_t

val mk_arg_constraint_from_post_predicate :
  (string * int) list
  -> (int * value_type_t list) list
  -> postcondition_predicate_t
  -> linear_constraint_t

val mk_constraints_from_interval :
  bool -> int -> interval_t -> linear_constraint_t list

val linear_constraints_of_matrix :
  bool -> big_int array array -> linear_constraint_t list

val linear_constraints_to_matrices:
  int -> linear_constraint_t list ->  big_int array array * big_int array array

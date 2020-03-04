(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* jchpre *)
open JCHPreAPI

class poly_t :
 object ('a)
   method add_constraints : JCHLinearConstraint.linear_constraint_t list -> 'a
   method add_constrs_from_interval : int -> interval_t -> 'a
   method add_mult_constr:
            int -> int -> int -> int option -> big_int option -> bool -> 'a 
   method affine_increment :  int -> big_int -> 'a
   method affine_image:
            int -> big_int -> (int * big_int) list -> big_int -> interval_t -> 'a
   method affine_preimage:
            int -> big_int -> (int * big_int) list -> big_int -> 'a
   method change_inds : (int * int) list -> 'a
   method clone : 'a
   method copy : 'a
   method copy_other_col_constrs : int -> int -> 'a
   method equal : 'a -> bool
   method get_constraints : JCHLinearConstraint.linear_constraint_t list 
   method get_eq_matrix : big_int array array
   method get_ineq_matrix : big_int array array
   method get_index_map : (int * int) list
   method get_interval : int -> interval_t
   method get_pair_combinations : JCHLinearConstraint.linear_constraint_t list
   method get_poly_inds : int list
   method is_bottom : bool
   method is_top : bool
   method is_used_ind : int -> bool
   method join : 'a -> 'a
   method leq : 'a -> bool
   method meet : 'a -> 'a
   method meet_simple : 'a -> 'a
   method minimize : 'a
   method mk_bottom : 'a
   method mk_poly:
            int list
            -> (int * int) list
            -> big_int array array
            -> big_int array array
            -> 'a
   method mk_poly_from_constraints:
            bool -> JCHLinearConstraint.linear_constraint_t list -> 'a
   method mk_top : 'a
   method mk_top_large : int list -> (int * int) list -> 'a
   method narrowing : 'a -> 'a
   method project_out : int list -> 'a
   method project_out_and_remove : int list -> 'a
   method remap_indices : (int * int) list -> 'a
   method remove_duplicates : 'a
   method remove_trivial_ineqs : 'a
   method restrict_number_constraints : 'a * bool
   method restrict_number_vars : 'a * bool
   method toPretty : pretty_t
   method to_string : string
   method to_pretty : variable_t list -> pretty_t 
   method widening : 'a -> 'a
 end

val bottom_poly : poly_t
val top_poly : poly_t
val top_poly_large : int list -> poly_t
  
val mk_poly_from_constraints :
  bool -> JCHLinearConstraint.linear_constraint_t list -> poly_t
  
val move_simple_ineqs_to_intervals :
  poly_t
  -> JCHIntervalArray.interval_array_t
  -> poly_t * JCHIntervalArray.interval_array_t

val dbg : bool ref


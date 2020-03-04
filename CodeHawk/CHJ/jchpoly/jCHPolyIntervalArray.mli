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
open CHNumerical
open CHLanguage
open CHPretty
open CHUtils

(* jchpre *)
open JCHPreAPI

val set_local_vars : variable_t list -> unit

class poly_interval_array_t :
  (int * CHNumerical.numerical_t) list -> 
  variable_t list ->
    object ('a)
      method add_empty_collection : variable_t -> 'a
      method add_ineq : bool -> variable_t -> big_int -> 'a
      method add_intervals_to_poly :  'a
      method add_field : variable_t -> field_info_int -> 'a
      method add_val_to_collection :
               bool -> variable_t -> variable_t -> interval_t -> 'a
      method add_vars : JCHProcInfo.jproc_info_t -> variable_t list -> 'a
           
      method affine_increment :
               variable_t
               -> big_int
               -> 'a * variable_t option * variable_t option
           
      method affine_image : 
               variable_t option
               -> variable_t * big_int
               -> (variable_t * big_int) list
               -> big_int
               -> 'a * variable_t option * variable_t option
           
      method affine_preimage :
               variable_t * big_int
               -> (variable_t * big_int) list
               -> big_int
               -> 'a
           
      method affine_subst : 
               variable_t
               -> variable_t option
               -> big_int
               -> big_int
               -> 'a * variable_t option * variable_t option
           
      method array_load : variable_t -> variable_t -> 'a
      method assert_eq : variable_t -> variable_t -> 'a
      method assert_geq : variable_t -> variable_t -> 'a
      method assert_gt : variable_t -> variable_t -> 'a
      method assert_neq : variable_t -> variable_t -> 'a
      method assert_non_const_eq : variable_t -> variable_t -> 'a
      method can_be_0 : variable_t -> bool
      method change_vars :
               symbol_t -> symbol_t -> variable_t list -> variable_t list -> 'a
           
      method check_type : variable_t -> 'a
      method clone : 'a 
      method copy_info : variable_t -> interval_t -> numerical_t list -> 'a
      method copy_num_info : variable_t -> variable_t -> 'a
      method div :
               bool
               -> variable_t
               -> variable_t
               -> variable_t
               -> 'a * variable_t option * variable_t option * variable_t option
           
      method down_cast_float : variable_t -> variable_t -> 'a * bool
      method drop_all : 'a
      method drop_poly : 'a
      method equal : 'a -> bool
      method float_const : variable_t -> float -> 'a
      method get_best_interval : IntCollections.ObjectSet.elt -> interval_t
      method get_call : JCHProcInfo.jproc_info_t -> variable_t list -> 'a
      method get_const_val : variable_t -> big_int
      method get_const_val_n : variable_t -> numerical_t 
      method get_excluded_vals : variable_t -> numerical_t list
      method get_extra_infos : JCHNumericInfo.numeric_info_t
      method get_field :
               JCHProcInfo.jproc_info_t
               -> field_info_int
               -> interval_t list
               -> variable_t
               -> 'a
           
      method get_index : variable_t -> int
      method get_interval : variable_t -> interval_t
      method get_interval_array : JCHIntervalArray.interval_array_t
      method set_join : variable_t -> variable_t -> variable_t -> 'a
      method set_type_intervals:
               JCHProcInfo.jproc_info_t -> variable_t list -> 'a
           
      method set_type_intervals_and_restrict:
               JCHProcInfo.jproc_info_t -> variable_t list -> 'a
           
      method get_poly : JCHPoly.poly_t
      method get_poly_vars : variable_t list
      method get_var_to_const : (int * numerical_t) list
      method get_var_to_index : (int * int) list
      method get_vars_with_fields : JCHProcInfo.jproc_info_t -> variable_t list
      method has_var : variable_t -> bool
      method init_assumptions : JCHProcInfo.jproc_info_t -> 'a
      method is_bottom : bool
      method is_const : variable_t -> bool 
      method is_top : bool
      method join : 'a -> 'a
      method join_with_old : 'a -> 'a -> 'a 
      method leq : 'a -> bool
      method log_and : variable_t -> variable_t -> variable_t -> 'a
      method log_or : variable_t -> variable_t -> variable_t -> 'a
      method meet : bool -> 'a -> 'a
      method meet' : 'a -> variable_t list -> 'a
      method meet_invoked :
               'a
               -> int list
               -> int
               -> variable_t list
               -> variable_t list
               -> variable_t list
               -> variable_t list
               -> variable_t list
               -> 'a
           
      method mk_empty : (int * numerical_t) list -> variable_t list -> 'a
      method move_simple_ineqs : 'a
      method mult :
               variable_t
               -> variable_t
               -> variable_t
               -> 'a * variable_t option * variable_t option * bool
           
      method new_array : variable_t -> variable_t list -> 'a
      method project_out : variable_t list -> 'a
      method project_out_array : variable_t -> 'a
      method pr__debug_large_poly_interval_array : unit
      method rem :
               bool
               -> variable_t
               -> variable_t
               -> variable_t
               -> 'a * variable_t option
           
      method remove : variable_t list -> 'a
      method remove_duplicates : 'a
      method remove_field : variable_t -> field_info_int -> 'a
      method restrict_to_type : variable_t list -> 'a
      method restrict_to_vars : JCHProcInfo.jproc_info_t -> variable_t list -> 'a
      method restrict_to_vars_2 : variable_t list -> 'a
      method set_best_intervals : 'a
      method set_extra_infos : JCHNumericInfo.numeric_info_t -> 'a
      method set_interval : variable_t -> interval_t -> 'a
      method set_interval_array : JCHIntervalArray.interval_array_t -> 'a
      method set_fields : variable_t -> field_info_int list -> 'a
      method set_poly : JCHPoly.poly_t -> 'a 
      method shr :  variable_t -> variable_t -> 'a
      method simple_join : 'a -> 'a
      method simple_widening : 'a ->  'a
      method simplify_with_intervals : 'a
      method transfer_fields : bool -> variable_t -> variable_t  -> 'a
      method to_postconditions :
               bool
               -> JCHProcInfo.jproc_info_t
               -> (variable_t * variable_t) list
               -> variable_t list 
	-> postcondition_predicate_t list
      method to_postconditions2 :
               JCHProcInfo.jproc_info_t -> postcondition_predicate_t list
      method to_pretty : pretty_t
      method toPretty : pretty_t
      method widening : 'a ->  'a
    end

val bottom_poly_interval_array : poly_interval_array_t
val top_poly_interval_array : 
  (int * numerical_t) list
  -> variable_t list
  -> poly_interval_array_t

val bottom_poly_int_array : poly_interval_array_t
val top_poly_int_array : poly_interval_array_t

val dbg : bool ref



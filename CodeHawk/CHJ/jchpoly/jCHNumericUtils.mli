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

(* chlib *)
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

val get_constants : 
  JCHProcInfo.jproc_info_t -> (int * numerical_t) list 

val mk_var_to_index : variable_t list -> (int * int) list

val pp_var_to_index : (int * int) list -> pretty_t

val interval_to_summary_post_predicates : 
  int -> interval_t -> interval_t -> postcondition_predicate_t list

val interval_to_summary_post_predicates2 : 
  is_loc:bool
  -> is_lc:bool
  -> is_length:bool
  -> is_aux:bool
  -> is_aux_length:bool
  -> var_index:int
  -> name:string
  -> interval:interval_t
  -> postcondition_predicate_t list

val excluded_vals_to_summary_pre_predicates : 
  int -> numerical_t list -> precondition_predicate_t list

val excluded_vals_to_summary_post_predicates : 
  int -> numerical_t list -> postcondition_predicate_t list

val equality_to_summary_post_predicate : int -> int -> postcondition_predicate_t

val has_return_pre_predicate : precondition_predicate_t -> bool

val pre_to_post_predicate :
  precondition_predicate_t -> postcondition_predicate_t
  
val post_predicate_to_relational_expr :
  postcondition_predicate_t -> relational_expr_t

val var_to_abstract_side : (int * int) list -> int -> sideeffect_t

val postcondition_predicate_to_pretty: postcondition_predicate_t -> pretty_t

val get_loop_counter_bounds :
  relational_expr_t list -> int -> jterm_t list * jterm_t list

val negate_jterm : jterm_t -> jterm_t

val get_jterm_vars : jterm_t -> jterm_t list

val get_field_term : int -> field_info_int -> jterm_t

val change_to_fields :
  int
  -> (variable_t * JCHPreAPI.field_info_int) list
  -> postcondition_predicate_t
  ->  postcondition_predicate_t

val is_numeric : field_info_int -> bool

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
open CHUtils

(* jchpre *)
open JCHPreAPI
   
class num_info_t : 
  object ('a)
    method add_excluded_val : numerical_t -> 'a
    method add_excluded_vals : numerical_t list -> 'a
    method add_field : field_info_int -> 'a
    method change_vars : variable_t list -> 'a
    method divisions : (variable_t * variable_t) list
    method fields : field_info_int list
    method is_changed_sym_param : bool
    method is_empty_collection : bool
    method excluded : numerical_t list
    method has_only_excluded : bool
    method is_empty : bool
    method join : 'a -> 'a
    method meet : 'a -> 'a
    method remove_excluded : 'a
    method remove_excluded_val : numerical_t -> 'a
    method remove_field :  field_info_int -> 'a
    method remove_var : variable_t -> interval_t -> 'a
    method remove_vars : variable_t list -> 'a
    method replace_vars : (variable_t * variable_t) list -> 'a
    method set_changed_sym_param : bool -> 'a
    method set_divisions : (variable_t * variable_t) list -> 'a
    method set_empty_collection : bool -> 'a
    method set_excluded_vals : numerical_t list -> 'a
    method set_fields : field_info_int list -> 'a
    method toPretty : pretty_t
    method to_pretty_no_excluded : pretty_t
  end

class numeric_info_t :
  object ('a) 
    method add_changed_sym_params : variable_t list -> 'a
    method add_div_info :
             variable_t VariableCollections.table_t VariableCollections.table_t -> 'a
    method add_empty_collection : variable_t -> 'a
    method add_excluded_val : variable_t -> numerical_t -> 'a
    method add_excluded_vals : variable_t -> numerical_t list -> 'a
    method add_field : variable_t -> field_info_int -> 'a
    method change_vars : variable_t list -> 'a
    method clone : 'a
    method get_divisions : variable_t -> (variable_t * variable_t) list 
    method get_excluded_vals : variable_t -> numerical_t list
    method get_excluded_vals_ind : int -> numerical_t list
    method get_fields : variable_t -> field_info_int list
    method get_info_map : (int * num_info_t) list 
    method get_num_info : variable_t -> num_info_t
    method get_num_info_ind : int -> num_info_t option
    method has_fields : variable_t -> bool
    method initialize :
             variable_t VariableCollections.table_t VariableCollections.table_t -> 'a
    method is_changed_sym_param : variable_t-> bool
    method is_empty_collection : variable_t -> bool
    method join : 'a -> 'a
    method meet : 'a -> 'a
    method remove_all_excluded : variable_t -> 'a
    method remove_empty_collection : variable_t -> 'a
    method remove_excluded_val : variable_t -> numerical_t -> 'a
    method remove_field : variable_t -> field_info_int -> 'a
    method remove_out_of_interval_excluded : variable_t -> interval_t -> 'a
    method remove_vars : variable_t list -> 'a
    method remove_var : variable_t -> interval_t -> 'a
    method replace_vars : (variable_t * variable_t) list -> (int * variable_t) list -> 'a
    method set_excluded_vals : variable_t -> numerical_t list -> 'a
    method set_fields : variable_t -> field_info_int list -> 'a
    method set_num_info : variable_t -> num_info_t -> 'a
    method set_same_info : variable_t -> variable_t -> 'a
    method to_pretty : variable_t list -> pretty_t
    method to_pretty_no_excluded : variable_t list -> pretty_t
    method toPretty : pretty_t
  end


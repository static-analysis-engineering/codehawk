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
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI

(* jchcost *)
open JCHCostUtils

val dbg : bool ref

class cost_bound_t :
    bool -> numerical_t JTermTableCollections.table_t ->
      numerical_t -> numerical_t ->
  object ('a)
    method add : 'a -> 'a
    method compare : 'a -> int
    method div : 'a -> 'a
    method equal : 'a -> bool
    method has_pos_coeffs : bool
    method has_pos_jterms : bool
    method get_const : numerical_t
    method get_div : numerical_t
    method has_only_jterms_to_keep :  (jterm_t -> bool) -> bool
    method find_const_lb_no_div : numerical_t option
    method find_const_lb : (numerical_t * numerical_t) option
    method get_jterms : JTermCollections.set_t
    method get_terms : numerical_t JTermTableCollections.table_t
    method get_term_pairs : (numerical_t JTermCollections.table_t * numerical_t) list
    method geq : 'a -> bool
    method has_negative_coefficient : bool
    method is_const : bool
    method is_lb : bool
    method is_local_var_linear : bool
    method is_non_0_const : bool
    method is_pos_const : bool
    method is_small : bool
    method is_zero_const: bool
    method leq : 'a -> bool
    method make_opposite : 'a
    method make_small_div : 'a
    method mult : 'a -> 'a
    method neg : 'a
    method number_terms : int
    method power : 'a -> numerical_t -> 'a
    method simple_join : 'a -> 'a
    method split_pos_neg : 'a * 'a
    method sub : 'a -> 'a
    method subst : (jterm_t * 'a) list list -> (jterm_t -> bool) -> 'a list
    method toPretty : pretty_t
    method to_evx : CHExternalValues.external_value_exchange_format_t
    method to_linear_constraint :
	     (int * numerical_t JTermCollections.table_t) list
             -> JCHLinearConstraint.linear_constraint_t
    method to_jterm: jterm_t
    method to_pretty_all : pretty_t
    method to_pretty_small : pretty_t
    method to_string : string
    method write_xml : xml_element_int -> unit
  end

val bounds_from_linear_constraint :
  (int * numerical_t JTermCollections.table_t) list
  -> JCHLinearConstraint.linear_constraint_t
  -> cost_bound_t list

val cost_bound_from_num : bool -> numerical_t -> cost_bound_t

val bound_from_jterm : bool -> jterm_t -> cost_bound_t

val cost_bound_to_string : cost_bound_t -> string

module CostBoundCollections :
sig
     class set_t :
       object ('a)
         method add : cost_bound_t -> unit
         method addList : cost_bound_t list -> unit
         method addSet : 'a -> unit
         method choose : cost_bound_t option
         method clone : 'a
         method diff : 'a -> 'a
         method equal : 'a -> bool
         method filter : (cost_bound_t -> bool) -> 'a
         method fold : ('b -> cost_bound_t -> 'b) -> 'b -> 'b
         method has : cost_bound_t -> bool
         method inter : 'a -> 'a
         method isEmpty : bool
         method iter : (cost_bound_t -> unit) -> unit
         method remove : cost_bound_t -> unit
         method removeList : cost_bound_t list -> unit
         method singleton : cost_bound_t option
         method size : int
         method subset : 'a -> bool
         method toList : cost_bound_t list
         method toPretty : pretty_t
         method union : 'a -> 'a
       end

     class ['a] table_t :
       object ('b)
	 constraint 'a = < toPretty : pretty_t; .. >
         method clone : 'b
         method fold : ('c -> cost_bound_t -> 'a -> 'c) -> 'c -> 'c
         method get : cost_bound_t -> 'a option
         method has : cost_bound_t -> bool
         method iter : (cost_bound_t -> 'a -> unit) -> unit
         method keys : set_t
         method listOfKeys : cost_bound_t list
         method listOfPairs : (cost_bound_t * 'a) list
         method listOfValues : 'a list
         method map : ('a -> 'a) -> 'b
         method mapi : (cost_bound_t -> 'a -> 'a) -> 'b
         method remove : cost_bound_t -> unit
         method removeList : cost_bound_t list -> unit
         method set : cost_bound_t -> 'a -> unit
         method setOfKeys : set_t
         method size : int
         method toPretty : pretty_t
       end
      val set_of_list : cost_bound_t list -> set_t
   end

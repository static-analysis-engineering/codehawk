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
open CHLanguage
open CHNumerical
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI

exception JCH_cost_out_of_time of string

val max_num : numerical_t
val margin_num : numerical_t
val max_int_num : numerical_t
val max_long_num : numerical_t
val sym_max_int: jterm_t
val sym_max_long: jterm_t

val make_sym_lc :
  int -> int -> numerical_t -> numerical_t option -> jterm_t

val is_sym_lc: jterm_t -> bool
val make_sym_lp: int -> int -> numerical_t -> jterm_t
val is_sym_lp: jterm_t -> bool
val make_sym_call: int -> int -> numerical_t -> jterm_t
val is_sym_call: jterm_t -> bool
val is_sym_cost: jterm_t -> bool
val make_sym_cost : int list -> numerical_t -> int -> jterm_t

val set_cost_var : variable_t -> unit
val get_cost_var : unit -> variable_t

val compare_num : numerical_t -> numerical_t -> int

val compare_tables :
    ('a -> 'a -> int)
    -> ('b -> 'c -> int)
    -> < get: 'a -> 'b option; keys: < union : 'd -> < toList : 'a list; .. >; .. >; .. >
    -> < get: 'a -> 'c option; keys : 'd; .. >
    -> int

module JTermCollections :
   sig
     class set_t :
       object ('a)
         method add: jterm_t -> unit
         method addList: jterm_t list -> unit
         method addSet : 'a -> unit
         method choose: jterm_t option
         method clone : 'a
         method diff : 'a -> 'a
         method equal : 'a -> bool
         method filter: (jterm_t -> bool) -> 'a
         method fold: ('b -> jterm_t -> 'b) -> 'b -> 'b
         method has: jterm_t -> bool
         method inter: 'a -> 'a
         method isEmpty: bool
         method iter: (jterm_t -> unit) -> unit
         method remove: jterm_t -> unit
         method removeList: jterm_t list -> unit
         method singleton: jterm_t option
         method size : int
         method subset : 'a -> bool
         method toList: jterm_t list
         method toPretty: pretty_t
         method union: 'a -> 'a
       end

     class ['a] table_t :
       object ('b)
	 constraint 'a = < toPretty : pretty_t; .. >
         method clone: 'b
         method fold: ('c -> jterm_t -> 'a -> 'c) -> 'c -> 'c
         method get: jterm_t -> 'a option
         method has: jterm_t -> bool
         method iter: (jterm_t -> 'a -> unit) -> unit
         method keys: set_t
         method listOfKeys: jterm_t list
         method listOfPairs: (jterm_t * 'a) list
         method listOfValues : 'a list
         method map: ('a -> 'a) -> 'b
         method mapi: (jterm_t -> 'a -> 'a) -> 'b
         method remove: jterm_t -> unit
         method removeList: jterm_t list -> unit
         method set: jterm_t -> 'a -> unit
         method setOfKeys: set_t
         method size: int
         method toPretty: pretty_t
       end
     val set_of_list: jterm_t list -> set_t
   end

module JTermTableCollections :
   sig
     class set_t :
       object ('a)
         method add : numerical_t JTermCollections.table_t -> unit
         method addList : numerical_t JTermCollections.table_t list -> unit
         method addSet : 'a -> unit
         method choose : numerical_t JTermCollections.table_t option
         method clone : 'a
         method diff : 'a -> 'a
         method equal : 'a -> bool
         method filter : (numerical_t JTermCollections.table_t -> bool) -> 'a
         method fold : ('b -> numerical_t JTermCollections.table_t -> 'b) -> 'b -> 'b
         method has : numerical_t JTermCollections.table_t -> bool
         method inter : 'a -> 'a
         method isEmpty : bool
         method iter : (numerical_t JTermCollections.table_t -> unit) -> unit
         method remove : numerical_t JTermCollections.table_t -> unit
         method removeList : numerical_t JTermCollections.table_t list -> unit
         method singleton : numerical_t JTermCollections.table_t option
         method size : int
         method subset : 'a -> bool
         method toList : numerical_t JTermCollections.table_t list
         method toPretty : pretty_t
         method union : 'a -> 'a
       end

     class ['a] table_t :
       object ('b)
	 constraint 'a = < toPretty : pretty_t; .. >
         method clone : 'b
         method fold : ('c -> numerical_t JTermCollections.table_t -> 'a -> 'c) -> 'c -> 'c
         method get : numerical_t JTermCollections.table_t -> 'a option
         method has : numerical_t JTermCollections.table_t -> bool
         method iter : (numerical_t JTermCollections.table_t -> 'a -> unit) -> unit
         method keys : set_t
         method listOfKeys : numerical_t JTermCollections.table_t list
         method listOfPairs : (numerical_t JTermCollections.table_t * 'a) list
         method listOfValues : 'a list
         method map : ('a -> 'a) -> 'b
         method mapi : (numerical_t JTermCollections.table_t -> 'a -> 'a) -> 'b
         method remove : numerical_t JTermCollections.table_t -> unit
         method removeList : numerical_t JTermCollections.table_t list -> unit
         method set : numerical_t JTermCollections.table_t -> 'a -> unit
         method setOfKeys : set_t
         method size : int
         method toPretty : pretty_t
       end
     val set_of_list : numerical_t JTermCollections.table_t list -> set_t
   end

val is_length: jterm_t -> bool
val is_field: jterm_t -> bool
val is_sym_lc_or_call_term: jterm_t -> bool
val is_local_var: bool -> jterm_t -> bool

val add_not_pos_jterm: int -> jterm_t -> unit
val record_not_pos_jterms : unit -> unit
val is_pos_jterm: jterm_t -> bool
val is_const: jterm_t -> bool

val is_large_const: jterm_t -> bool
val pp_list_jterm: jterm_t list -> pretty_t
val no_local_vars: jterm_t -> bool

val no_calls_or_lcs: JTermCollections.set_t -> jterm_t -> bool
val no_cost_calls_or_lcs:  JTermCollections.set_t -> jterm_t -> bool

val no_loop_costs:  jterm_t -> bool

val set_max_cost_analysis_time : float -> unit

val start_cost_analysis : unit -> unit
val check_cost_analysis_time : string -> unit

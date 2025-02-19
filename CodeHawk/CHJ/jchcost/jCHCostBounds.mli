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
open JCHCostBound

val dbg : bool ref

val set_instr_pc : int -> unit
val get_instr_pc : unit -> int

val set_cmsix : int -> unit

val eliminate_duplicates : bool -> cost_bound_t list -> cost_bound_t list

class cost_bounds_t :
        bottom:bool
        -> simplify:bool
        -> inflb:bool
        -> infub:bool
        -> lbounds:cost_bound_t list
        -> ubounds:cost_bound_t list ->
  object ('a)
    method equal : 'a -> bool
    method isBottom : bool
    method isTop : bool
    method join : 'a -> 'a
    method kind : string
    method leq : 'a -> bool
    method marshal : CHExternalValues.external_value_exchange_format_t
    method meet : 'a -> 'a
    method narrowing : 'a -> 'a
    method toPretty: pretty_t
    method widening : 'a -> 'a
  end

val bottom_cost_bounds : cost_bounds_t

val top_cost_bounds : cost_bounds_t

val inf_lb_cost_bounds : cost_bounds_t

val cost_bounds_from_num: numerical_t -> cost_bounds_t

val cost_bounds_from_jterm_range: jterm_range_int -> cost_bounds_t

val get_bounds:
  cost_bounds_t
  -> CostBoundCollections.set_t
     * CostBoundCollections.set_t
     * bool
     * bool

val add_cost_bounds : cost_bounds_t -> cost_bounds_t -> cost_bounds_t

val mult_cost_bounds : cost_bounds_t -> cost_bounds_t -> cost_bounds_t

val div_cost_bounds : cost_bounds_t -> cost_bounds_t -> cost_bounds_t

val write_xml_bounds: ?tag:string -> cost_bounds_t -> xml_element_int -> unit

val write_xml_atlas_bounds:
  xml_element_int -> method_signature_int -> cost_bounds_t -> unit

val bounds_from_jterms :
    bool -> jterm_t list -> jterm_t list -> cost_bounds_t

val read_xml_bounds : ?tag:string -> xml_element_int -> cost_bounds_t

val bounds_from_jterm_range : bool -> jterm_range_int -> cost_bounds_t

val is_const_range : cost_bounds_t -> bool

val subst_pos_bounds : int -> cost_bounds_t -> bool -> cost_bounds_t

val subst_pos_bounds_final : int -> cost_bounds_t -> cost_bounds_t

val subst_local_vars :
  int
  -> cost_bounds_t
  -> (jterm_t * cost_bound_t list) list
  -> (jterm_t * cost_bound_t list) list -> cost_bounds_t

val add_pos_jterm : int -> jterm_t -> cost_bounds_t -> unit

val add_pos_jterm_final : int -> jterm_t -> cost_bounds_t -> cost_bounds_t

val get_jterms : cost_bounds_t -> jterm_t list

val make_small_divs : cost_bounds_t -> cost_bounds_t

val find_const_lb : bool -> cost_bounds_t -> numerical_t

val full_join : cost_bounds_t -> cost_bounds_t -> cost_bounds_t

val costbounds_to_string : cost_bounds_t -> string

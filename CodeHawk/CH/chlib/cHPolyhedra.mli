(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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

module Cherni :
  sig
    val conversion :
      CHMatrix.matrix_t ->
      int -> CHMatrix.matrix_t -> CHSaturationMatrix.satmat_t -> int -> int
    val gauss : int array -> CHMatrix.matrix_t -> int -> int
    val backsubstitute : int array -> CHMatrix.matrix_t -> int -> unit
    val simplify :
      CHMatrix.matrix_t ->
      CHMatrix.matrix_t -> CHSaturationMatrix.satmat_t -> int -> int
    val minimize :
      bool ->
      CHMatrix.matrix_t option ref ->
      CHMatrix.matrix_t option ref ->
      CHSaturationMatrix.satmat_t option ref -> int ref -> int ref -> unit
    val add_dimensions :
      CHMatrix.matrix_t option ->
      CHMatrix.matrix_t option ->
      CHSaturationMatrix.satmat_t option ref ->
      CHSaturationMatrix.satmat_t option ->
      int ->
      CHMatrix.matrix_t option ref ->
      CHMatrix.matrix_t option ref ->
      CHSaturationMatrix.satmat_t option ref -> unit
    val checksatmat :
      bool ->
      CHMatrix.matrix_t ->
      CHMatrix.matrix_t -> CHSaturationMatrix.satmat_t -> bool
    val checksat :
      bool ->
      CHMatrix.matrix_t ->
      int -> CHMatrix.matrix_t -> int -> CHSaturationMatrix.satmat_t -> bool
    val add_and_minimize :
      bool ->
      CHMatrix.matrix_t ->
      CHMatrix.matrix_t ->
      CHSaturationMatrix.satmat_t ->
      int ->
      CHMatrix.matrix_t ->
      CHMatrix.matrix_t option ref ->
      CHMatrix.matrix_t option ref ->
      CHSaturationMatrix.satmat_t option ref -> int ref -> int ref -> unit
    val buildsatline :
      CHMatrix.matrix_t ->
      CHVector.vector_t -> CHBitstring.bitstring_t array -> unit
  end

type tsign_t =
  | Tsign_bottom
  | Tsign_gt
  | Tsign_eq
  | Tsign_lt
  | Tsign_geq
  | Tsign_leq
  | Tsign_top

val tsign_is_leq : tsign_t -> tsign_t -> bool

val tsign_union : tsign_t -> tsign_t -> tsign_t

class polyhedron_t :
  int ->
  object ('a)
    val _c : CHMatrix.matrix_t option ref
    val _dim : int
    val _f : CHMatrix.matrix_t option ref
    val _nbeq : int ref
    val _nbline : int ref
    val _satC : CHSaturationMatrix.satmat_t option ref
    val _satF : CHSaturationMatrix.satmat_t option ref
    method add_constraints : CHMatrix.matrix_t -> 'a
    method add_dimensions_and_embed : int -> 'a
    method c : CHMatrix.matrix_t option ref
    method check : unit
    method check_dims : 'a -> 'a -> string -> unit
    method convex_hull : 'a -> 'a
    method copy : 'a
    method dim : int
    method f : CHMatrix.matrix_t option ref
    method frames_versus_constraint :
      CHMatrix.matrix_t -> CHVector.vector_t -> CHPolyhedraGlobalData.tbool_t
    method get_constraints : CHMatrix.matrix_t
    method intersection : 'a -> 'a
    method is_empty : bool
    method is_equal : 'a -> bool
    method is_included_in : 'a -> bool
    method is_minimal : bool
    method is_universe : bool
    method minimize : unit
    method mkNew : int -> 'a
    method mkUniverse : int -> 'a
    method nbeq : int
    method nbeq_ref : int ref
    method nbline : int
    method nbline_ref : int ref
    method obtain_satF : unit
    method obtain_sorted_C : unit
    method obtain_sorted_C_with_satC : unit
    method obtain_sorted_F : unit
    method obtain_sorted_F_with_satF : unit
    method permute_remove_dimensions : int -> int array -> 'a
    method reduce_polyhedra : 'a -> 'a -> 'a * 'a * CHMatrix.matrix_t
    method reset_c : unit
    method reset_f : unit
    method reset_satC : unit
    method reset_satF : unit
    method satC : CHSaturationMatrix.satmat_t option ref
    method satF : CHSaturationMatrix.satmat_t option ref
    method set_c : CHMatrix.matrix_t -> unit
    method set_f : CHMatrix.matrix_t -> unit
    method set_nbeq : int -> unit
    method set_nbline : int -> unit
    method set_satC : CHSaturationMatrix.satmat_t -> unit
    method set_satF : CHSaturationMatrix.satmat_t -> unit
    method toPretty : CHPretty.pretty_t
    method widening : 'a -> 'a
  end

val universe : int -> polyhedron_t

val empty_polyhedron : int -> polyhedron_t

val of_constraints : CHMatrix.matrix_t -> polyhedron_t

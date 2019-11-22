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

class matrix_t :
  int ->
  int ->
  bool ->
  object ('a)
    val mutable _empty : bool
    val mutable _maxrows : int
    val mutable _nbcolumns : int
    val mutable _nbrows : int
    val mutable _p : CHVector.vector_t array
    val mutable _sorted : bool
    method add_dimensions : int -> matrix_t
    method clear : unit
    method combine_rows : int -> int -> int -> int -> unit
    method copy : 'a
    method empty : bool
    method exch_rows : int -> int -> unit
    method get : int -> int -> CHNumerical.numerical_t
    method get_constraints : int -> 'a
    method get_inequality_constraints : 'a
    method get_linear_constraints : 'a
    method get_row : int -> CHVector.vector_t
    method has_constraint : CHVector.vector_t -> bool
    method intersect_constraints : 'a -> 'a
    method is_sorted : bool
    method maxrows : int
    method mkNew : int -> int -> bool -> 'a
    method nbcolumns : int
    method nbrows : int
    method p : int -> CHVector.vector_t
    method permute_remove_dimensions : int -> int array -> 'a
    method reduce_constraints : 'a -> unit
    method reset : int -> int -> bool -> unit
    method row_echelon : int
    method set : int -> int -> CHNumerical.numerical_t -> unit
    method set_empty : bool -> unit
    method set_nbcolumns : int -> unit
    method set_nbrows : int -> unit
    method set_p : CHVector.vector_t array -> unit
    method set_row : int -> CHVector.vector_t -> unit
    method set_sorted : bool -> unit
    method sort_rows : unit
    method sort_rows_with_sat : CHSaturationMatrix.satmat_t -> unit
    method toPretty : CHPretty.pretty_t
  end

val empty_matrix : matrix_t

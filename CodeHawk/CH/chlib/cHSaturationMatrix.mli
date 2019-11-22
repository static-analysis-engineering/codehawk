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

class satmat_t :
  int ->
  int ->
  object ('a)
    val _nbcolumns : int
    val mutable _nbrows : int
    val _p : CHBitstring.bitstring_t array array
    method copy : 'a
    method exch_rows : int -> int -> unit
    method get : int -> CHBitstring.bitindex_t -> CHBitstring.bitstring_t
    method get_row : int -> CHBitstring.bitstring_t array
    method index_in_sorted_rows : CHBitstring.bitstring_t array -> int
    method is_empty : bool
    method mkNew : int -> int -> 'a
    method nbcolumns : int
    method nbrows : int
    method p : int -> int -> CHBitstring.bitstring_t
    method set : int -> CHBitstring.bitindex_t -> unit
    method set_nbrows : int -> unit
    method set_p : int -> int -> CHBitstring.bitstring_t -> unit
    method set_row : int -> CHBitstring.bitstring_t array -> unit
    method sort_rows : unit
    method transpose : int -> 'a
  end

val empty_satmat : satmat_t

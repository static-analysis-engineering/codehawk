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

val bitstring_size : int

val bitindex_size : int -> int

class bitstring_t :
  int32 ->
  object ('a)
    val _b : int32
    method b : int32
    method equal : 'a -> bool
    method gt : 'a -> bool
    method is_zero : bool
    method logical_and : 'a -> 'a
    method logical_not : 'a
    method logical_or : 'a -> 'a
    method lt : 'a -> bool
    method shift_left : int -> 'a
    method shift_right : int -> 'a
  end

val zero_bitstring : bitstring_t

val one_bitstring : bitstring_t

val bitstring_msb : bitstring_t

val bitstring_cmp : bitstring_t array -> bitstring_t array -> int

class bitindex_t :
  int ->
  object
    val mutable _bit : bitstring_t
    val mutable _index : int
    val mutable _word : int
    method bit : bitstring_t
    method dec : unit
    method inc : unit
    method index : int
    method word : int
  end

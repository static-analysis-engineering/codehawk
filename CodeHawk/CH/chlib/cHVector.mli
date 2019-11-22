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

class vector_t :
  int ->
  object ('a)
    val _size : int
    val _v : CHNumerical.numerical_t array
    method add_dimensions : int -> 'a
    method clear : unit
    method combine : 'a -> 'a -> int -> unit
    method compare : 'a -> int
    method copy : 'a
    method gcd : CHNumerical.numerical_t
    method get : int -> CHNumerical.numerical_t
    method get_head : int
    method get_v : CHNumerical.numerical_t array
    method is_null_strict : bool
    method mkVector : int -> 'a
    method normalize : unit
    method permute_remove_dimensions : vector_t -> int -> int array -> unit
    method product : 'a -> CHNumerical.numerical_t
    method product_strict : 'a -> CHNumerical.numerical_t
    method set : int -> CHNumerical.numerical_t -> unit
    method size : int
    method subvector : int -> 'a
    method toPretty : CHPretty.pretty_t
  end

val empty_vector : vector_t

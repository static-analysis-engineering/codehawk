(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
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
  ------------------------------------------------------------------------------ *)

type bounds_t = MINUS_INF | PLUS_INF | NUMBER of CHNumerical.numerical_t
                                               
type polarity_t = POS | NEG | BOTH
                            
class bound_t :
  bounds_t ->
  object ('a)
    val bound : bounds_t
    method add : 'a -> 'a
    method div_ceiling : 'a -> 'a
    method div_floor : 'a -> 'a
    method equal : 'a -> bool
    method geq : 'a -> bool
    method getBound : bounds_t
    method gt : 'a -> bool
    method leq : 'a -> bool
    method lt : 'a -> bool
    method isInfinite: bool
    method max : 'a -> 'a
    method min : 'a -> 'a
    method private mkNew : bounds_t -> 'a
    method mult : 'a -> 'a
    method neg : 'a
    method polarity : 'a -> polarity_t
    method sub : 'a -> 'a
    method toNumber : CHNumerical.numerical_t
    method toPretty : CHPretty.pretty_t
  end

val minus_inf_bound : bound_t

val plus_inf_bound : bound_t

val bound_of_num : CHNumerical.numerical_t -> bound_t

val min_in_bounds : bound_t list -> bound_t

val max_in_bounds : bound_t list -> bound_t

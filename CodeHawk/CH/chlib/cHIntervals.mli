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

class interval_t :
  CHBounds.bound_t ->
  CHBounds.bound_t ->
  object ('a)
    val bottom : bool
    val max : CHBounds.bound_t
    val min : CHBounds.bound_t
    method add : 'a -> 'a
    method clone : 'a
    method contains : CHNumerical.numerical_t -> bool
    method div : 'a -> 'a
    method equal : 'a -> bool
    method getMax : CHBounds.bound_t
    method getMin : CHBounds.bound_t
    method isBottom : bool
    method isTop : bool
    method isBounded: bool
    method iter : (CHNumerical.numerical_t -> unit) -> unit
    method join : 'a -> 'a
    method leq : 'a -> bool
    method lowerBound : CHBounds.bound_t -> 'a
    method meet : 'a -> 'a
    method mkBottom : 'a
    method mkInterval : CHBounds.bound_t -> CHBounds.bound_t -> 'a
    method mkTop : 'a
    method mult : 'a -> 'a
    method narrowing : 'a -> 'a
    method neg : 'a
    method singleton : CHNumerical.numerical_t option
    method strictLowerBound : CHBounds.bound_t -> 'a
    method strictUpperBound : CHBounds.bound_t -> 'a
    method sub : 'a -> 'a
    method toPretty : CHPretty.pretty_t
    method upperBound : CHBounds.bound_t -> 'a
    method widening : 'a -> 'a
  end

val mkSingletonInterval : CHNumerical.numerical_t -> interval_t

val topInterval : interval_t

val bottomInterval : interval_t

val mkInterval :
  CHNumerical.numerical_t -> CHNumerical.numerical_t -> interval_t

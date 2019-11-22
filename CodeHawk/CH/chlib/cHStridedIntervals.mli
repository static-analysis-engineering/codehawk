(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet and Anca Browne
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

open Big_int_Z
   
val adjustMin :
  CHBounds.bound_t ->
  CHNumerical.numerical_t -> CHNumerical.numerical_t -> CHBounds.bound_t
  
val adjustMax :
  CHBounds.bound_t ->
  CHNumerical.numerical_t -> CHNumerical.numerical_t -> CHBounds.bound_t
  
val isBottom : CHBounds.bound_t -> CHBounds.bound_t -> bool
  
val adjustStride :
  CHBounds.bound_t ->
  CHBounds.bound_t -> CHNumerical.numerical_t -> CHNumerical.numerical_t
  
val adjustRem :
  CHBounds.bound_t ->
  CHBounds.bound_t ->
  CHNumerical.numerical_t ->
  CHNumerical.numerical_t -> CHNumerical.numerical_t
  
val diophantine :
  big_int ->
  big_int -> big_int -> big_int * big_int

val prediophantine :
  big_int -> big_int -> big_int -> big_int
  
class strided_interval_t :
        CHBounds.bound_t ->
        CHBounds.bound_t ->
        CHNumerical.numerical_t ->
        CHNumerical.numerical_t ->
        object ('a)
          val bottom : bool
          val max : CHBounds.bound_t
          val min : CHBounds.bound_t
          val rem : CHNumerical.numerical_t
          val stride : CHNumerical.numerical_t
          method add : 'a -> 'a
          method adjust : 'a
          method clone : 'a
          method contains : CHNumerical.numerical_t -> bool
          method div : 'a -> 'a
          method equal : 'a -> bool
          method findMultMinMax : 'a -> CHBounds.bound_t * CHBounds.bound_t
          method findMultRem :
                   'a -> CHNumerical.numerical_t -> CHNumerical.numerical_t
          method findMultStride : 'a -> CHNumerical.numerical_t
          method getMax : CHBounds.bound_t
          method getMin : CHBounds.bound_t
          method getRem : CHNumerical.numerical_t
          method getStride : CHNumerical.numerical_t
          method isBottom : bool
          method isBoundInInterval : CHBounds.bound_t -> bool
          method isInInterval : CHNumerical.numerical_t -> bool
          method isInStrideWithRem : CHNumerical.numerical_t -> bool
          method isSingleton : bool
          method isTop : bool
          method iter : (CHNumerical.numerical_t -> unit) -> unit
          method join : 'a -> 'a
          method leq : 'a -> bool
          method lowerBound : CHBounds.bound_t -> 'a
          method meet : 'a -> 'a
          method mkBottom : 'a
          method mkInterval :
                   CHBounds.bound_t ->
                   CHBounds.bound_t ->
                   CHNumerical.numerical_t -> CHNumerical.numerical_t -> 'a
          method mkNonstridedInterval : CHIntervals.interval_t
          method mkSingleton : CHNumerical.numerical_t -> 'a
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
    
val mkSingletonStridedInterval :
  CHNumerical.numerical_t -> strided_interval_t
  
val mkSingletonStridedIntervalN : int -> strided_interval_t
  
val topStridedInterval : strided_interval_t
  
val bottomStridedInterval : strided_interval_t
  
val mkStridedInterval :
  CHNumerical.numerical_t ->
  CHNumerical.numerical_t ->
  CHNumerical.numerical_t -> CHNumerical.numerical_t -> strided_interval_t
  
val mkStridedIntervalN : int -> int -> int -> int -> strided_interval_t
  
val intervalToStridedInterval : CHIntervals.interval_t -> strided_interval_t
  
val stridedIntervalToInterval : strided_interval_t -> CHIntervals.interval_t
  

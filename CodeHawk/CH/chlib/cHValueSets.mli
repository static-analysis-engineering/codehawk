(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet and Henny Sipma
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

type base_offset_t = CHLanguage.symbol_t * CHIntervals.interval_t

type base_offset_null_t = CHLanguage.symbol_t * CHIntervals.interval_t * bool

type zero_offset_t = CHIntervals.interval_t

val add_zero_offset_to_base_offsets :
  zero_offset_t ->
  base_offset_t list -> (CHLanguage.symbol_t * CHIntervals.interval_t) list

val subtract_zero_offset_from_base_offsets :
  zero_offset_t ->
  base_offset_t list -> (CHLanguage.symbol_t * CHIntervals.interval_t) list

val base_offsets_to_top :
  base_offset_t list -> (CHLanguage.symbol_t * CHIntervals.interval_t) list

val subtract_base_offsets :
  base_offset_t list -> base_offset_t list -> CHIntervals.interval_t

val join_base_offsets :
  base_offset_t list -> base_offset_t list -> base_offset_t list

val interval_upper_bound :
  CHIntervals.interval_t -> CHIntervals.interval_t -> CHIntervals.interval_t

val interval_lower_bound :
  CHIntervals.interval_t -> CHIntervals.interval_t -> CHIntervals.interval_t

val interval_strict_upper_bound :
  CHIntervals.interval_t -> CHIntervals.interval_t -> CHIntervals.interval_t

val interval_strict_lower_bound :
  CHIntervals.interval_t -> CHIntervals.interval_t -> CHIntervals.interval_t

class valueset_t :
  CHIntervals.interval_t ->
  base_offset_t list ->
  bool ->
  object ('a)
    val base_offsets : base_offset_t list
    val top : bool
    val zero_offset : CHIntervals.interval_t
    method add : 'a -> 'a
    method baseOffsets : base_offset_t list
    method clone : 'a
    method div : 'a -> 'a
    method equal : 'a -> bool
    method getMultipleBase : base_offset_t list
    method getOffsetFromBase : CHLanguage.symbol_t -> CHIntervals.interval_t
    method getSingleBase : base_offset_t
    method getSingleBaseNull :
      CHLanguage.symbol_t * CHIntervals.interval_t * bool
    method getValue : CHIntervals.interval_t * base_offset_t list
    method getZeroOffset : CHIntervals.interval_t
    method private hasNull : bool
    method hasSingleBase : CHLanguage.symbol_t -> bool
    method includesZero : bool
    method isBottom : bool
    method isMultipleBase : bool
    method isNull : bool
    method isSingleBase : bool
    method isSingleBaseNull : bool
    method isTop : bool
    method isZeroOffset : bool
    method join : 'a -> 'a
    method length : int
    method leq : 'a -> bool
    method lowerBound : 'a -> 'a
    method meet : 'a -> 'a
    method mkBottom : 'a
    method mkTop : 'a
    method mkValueSet : CHIntervals.interval_t -> base_offset_t list -> 'a
    method mult : 'a -> 'a
    method narrowing : 'a -> 'a
    method removeNull : 'a
		method removeZeroOffset : 'a
    method strictLowerBound : 'a -> 'a
    method strictUpperBound : 'a -> 'a
    method sub : 'a -> 'a
    method toPretty : CHPretty.pretty_t
    method upperBound : 'a -> 'a
    method widening : 'a -> 'a
    method zeroOffset : CHIntervals.interval_t
    method zeroOffsetSingleton : CHNumerical.numerical_t option
  end

val topValueSet : valueset_t

val bottomValueSet : valueset_t

val topZeroOffset : valueset_t

val mkZeroOffsetSingletonInterval : CHNumerical.numerical_t -> valueset_t

val mkBaseOffsetSingletonInterval :
  CHLanguage.symbol_t -> CHNumerical.numerical_t -> valueset_t

val mkBaseOffsetNullSingletonInterval :
  CHLanguage.symbol_t -> CHNumerical.numerical_t -> valueset_t

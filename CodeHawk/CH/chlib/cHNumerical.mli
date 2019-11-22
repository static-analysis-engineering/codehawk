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

open Big_int_Z

class numerical_t :
  big_int ->
  object ('a)
    val num : Big_int_Z.big_int
    method abs : 'a
    method add : 'a -> 'a
    method compare : 'a -> int
    method div : 'a -> 'a
    method equal : 'a -> bool
    method gcd : 'a -> 'a
    method geq : 'a -> bool
    method getNum : big_int
    method gt : 'a -> bool
    method is_zero : bool
    method is_int  : bool
    method lcm : 'a -> 'a
    method leq : 'a -> bool
    method lt : 'a -> bool
    method private mkNew : big_int -> 'a
    method modulo : 'a -> 'a
    method mult : 'a -> 'a
    method neg : 'a
    method sgn : int
    method sub : 'a -> 'a
    method toInt : int
    method toInt32 : Int32.t
    method toInt64 : Int64.t
    method toPretty : CHPretty.pretty_t
    method toRational : rational_t
    method toString : string
  end
and rational_t :
  big_int ->
  object ('a)
    val num : Q.t
    method add : 'a -> 'a
    method ceiling : numerical_t
    method compare : 'a -> int
    method div : 'a -> 'a
    method equal : 'a -> bool
    method floor : numerical_t
    method geq : 'a -> bool
    method getNum : Q.t
    method gt : 'a -> bool
    method leq : 'a -> bool
    method lt : 'a -> bool
    method private mkNew : Q.t -> 'a
    method mult : 'a -> 'a
    method neg : 'a
    method sub : 'a -> 'a
    method toPretty : CHPretty.pretty_t
    method toString : string
  end

val mkNumerical : int -> numerical_t

val numerical_zero : numerical_t

val numerical_one : numerical_t

val mkNumerical_big : big_int -> numerical_t

val mkRational : int -> rational_t

val mkNumericalFromInt32 : int32 -> numerical_t

val mkNumericalFromInt64 : int64 -> numerical_t

val mkNumericalFromString: string -> numerical_t

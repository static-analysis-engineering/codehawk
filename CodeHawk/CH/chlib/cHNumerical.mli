(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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
    method quomod : 'a -> 'a * 'a
    method mult : 'a -> 'a
    method neg : 'a
    method sgn : int
    method shift_left: int -> 'a
    method shift_right: int -> 'a
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


(** Numerical for 0 *)
val numerical_zero : numerical_t


(** Numerical for 1 *)
val numerical_one : numerical_t


(** Numerical for 2^8 (256) *)
val numerical_e8: numerical_t


(** Numerical for 2^15 *)
val numerical_e15: numerical_t


(** Numerical for 2^16 *)
val numerical_e16: numerical_t


(** Numerical for 2^31 *)
val numerical_e31: numerical_t


(** Numerical for 2^32 *)
val numerical_e32: numerical_t


(** Numerical for 2^64 *)
val numerical_e64: numerical_t


(** [mkNumerical i] returns the numerical for value [i]. *)
val mkNumerical : int -> numerical_t


(** [mkNumerical i] returns the numerical for value [i]. *)
val mkNumerical_big : big_int -> numerical_t


(** [mkRational r] returns the rational for value [r]. *)
val mkRational : int -> rational_t


val mkNumericalFromInt32 : int32 -> numerical_t

val mkNumericalFromInt64 : int64 -> numerical_t

val mkNumericalFromString: string -> numerical_t


(** [mkNumericalPowerOf2 n] returns the numerical for [2^n] *)
val mkNumericalPowerOf2: int -> numerical_t


(** [mkNumericalFromBitString s] returns the numerical for the value represented
    by the bitstring [s]. [s] must be a string consisting solely of 0's and 1's
    (no leading 0b).

    Maximumum length currently supported is 64 characters.*)
val mkNumericalFromBitString: string -> numerical_t

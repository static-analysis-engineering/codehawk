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

(* chlib *)
open CHCommon
open CHPretty


class numerical_t n =
object (self: 'a)

  val num =  n

  method getNum = num

  method private mkNew n = {< num = n >}

  method add (n: 'a) = self#mkNew (add_big_int num n#getNum)

  method sub (n: 'a) = self#mkNew (sub_big_int num n#getNum)

  method mult (n: 'a) = self#mkNew (mult_big_int num n#getNum)

  method div (n: 'a) =
    try
      self#mkNew (div_big_int num n#getNum)
    with
    | Division_by_zero ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Numerical division by zero: ";
                 self#toPretty;
                 STR " / ";
                 n#toPretty]))

  method modulo (n: 'a) =
    try
      self#mkNew (mod_big_int num n#getNum)
    with
    | Division_by_zero ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Numerical division by zero (modulo): ";
                 self#toPretty;
                 STR " % ";
                 n#toPretty]))

  method quomod (n: 'a) =
    let (quo, modd) = quomod_big_int num n#getNum in
    (self#mkNew quo, self#mkNew modd)

  method gcd (n: 'a) =
    let zero = self#mkNew (big_int_of_int 0) in
    if self#equal zero && n#equal zero then
      raise (CHFailure (LBLOCK [STR "Gcd(0,0) is not defined"]))
    else
      if self#equal zero then
        n
      else if n#equal zero then
        self
    else
      try
        self#mkNew (gcd_big_int num n#getNum)
      with
      | Division_by_zero ->
         raise
           (CHFailure
              (LBLOCK [
                   STR "Numerical division by zero (gcd): ";
                   self#toPretty;
                   STR " gcd ";
                   n#toPretty]))

  method lcm (n: 'a) =
    try
      self#mkNew (div_big_int (mult_big_int num n#getNum) (gcd_big_int num n#getNum))
    with
    | Division_by_zero ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Numerical division by z ero (lcm): ";
                 self#toPretty;
                 STR " lcm ";
                 n#toPretty]))

  method shift_left (n: int): 'a =
    if n >= 0 then
      self#mkNew (shift_left_big_int num n)
    else
      raise
        (CHFailure
           (LBLOCK [
                STR "Numerical shift left with negative shift amount: "; INT n]))

  (* arithmetic shift *)
  method shift_right (n: int): 'a =
    if n >= 0 then
      self#mkNew (shift_right_big_int num n)
    else
      raise
        (CHFailure
           (LBLOCK [
                STR "Numerical shift right with negative shift amount: "; INT n]))

  method leq (n: 'a) = le_big_int num n#getNum

  method lt (n: 'a) = lt_big_int num n#getNum

  method geq (n: 'a) = ge_big_int num n#getNum

  method gt (n: 'a) = gt_big_int num n#getNum

  method equal (n: 'a) = eq_big_int num n#getNum

  method compare (n: 'a) = compare_big_int num n#getNum

  method sgn = compare_big_int num zero_big_int
    
  method abs = self#mkNew (abs_big_int num)

  method is_zero = eq_big_int num zero_big_int

  method is_int = is_int_big_int num

  method toString = string_of_big_int num

  method toPretty = STR (self#toString)

  method neg = self#mkNew (minus_big_int num)    

  method toInt = 
    try
      int_of_big_int num
    with
    | Failure _ ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Numerical to int conversion failure: ";
                 self#toPretty]))

  method toInt64 =
    try
      Int64.of_string self#toString
    with
    | Failure _ ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Numerical to int64 conversion failure: ";
                 self#toPretty]))

  method toInt32 =
    try
      Int32.of_string self#toString
    with
    | Failure _ ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Numerical to int32 conversion failure: ";
                 self#toPretty]))

  method toRational =
    new rational_t num

end

and rational_t n =
object (self: 'a)

  val num = Q.of_bigint n

  method getNum: Q.t = num

  method private mkNew n = {< num = n >}

  method add (n: 'a) = self#mkNew (Q.add num n#getNum)

  method sub (n: 'a) = self#mkNew (Q.sub num n#getNum)

  method mult (n: 'a) = self#mkNew (Q.mul num n#getNum)

  method div (n: 'a) =
    try
      self#mkNew (Q.div num n#getNum)
    with
    | Division_by_zero ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Rational division by zero: ";
                 self#toPretty;
                 STR " / ";
                 n#toPretty]))

  method leq (n: 'a): bool = Q.leq num n#getNum

  method lt (n: 'a): bool = Q.lt num n#getNum

  method geq (n: 'a): bool = Q.geq num n#getNum

  method gt (n: 'a): bool = Q.gt num n#getNum

  method equal (n: 'a): bool = Q.equal num n#getNum

  method compare (n: 'a): int = Q.compare num n#getNum

  method toString = Q.to_string num

  method toPretty = STR (self#toString)

  method neg = self#mkNew (Q.neg num)    

  method floor:numerical_t =
    let truncated = Q.of_bigint (Q.to_bigint num) in
    if Q.gt truncated num then
      new numerical_t (Q.to_bigint (Q.sub truncated Q.one))
    else
      new numerical_t (Q.to_bigint truncated)
    (* match Q.floor num with
      | Q.Big_int n -> new numerical_t n
      | Q.Int n -> new numerical_t (big_int_of_int n)
      | _ -> raise (CHFailure (STR "Rational error #1")) *)

  method ceiling:numerical_t =
    let truncated = Q.of_bigint (Q.to_bigint num) in
    if Q.gt truncated num then
      new numerical_t (Q.to_bigint truncated)
    else
      new numerical_t (Q.to_bigint (Q.add truncated Q.one))
   (* match Q.ceiling num with
      | Q.Big_int n -> new numerical_t n
      | Q.Int n -> new numerical_t (big_int_of_int n)
      | _ -> raise (CHFailure (STR "Rational error #1")) *)

end


let mkNumerical n = new numerical_t (big_int_of_int n)

let numerical_zero = mkNumerical 0

let numerical_one = mkNumerical 1


let mkNumericalPowerOf2 (n: int) =
  new numerical_t (power_int_positive_int 2 n)


let numerical_e8 = mkNumerical 256

let numerical_e15 = mkNumericalPowerOf2 15

let numerical_e16 = mkNumericalPowerOf2 16

let numerical_e31 = mkNumericalPowerOf2 31

let numerical_e32 = mkNumericalPowerOf2 32

let numerical_e64 = mkNumericalPowerOf2 64


let mkNumerical_big n = new numerical_t n

let mkNumericalFromString s = new numerical_t (big_int_of_string s)

let mkRational n = new rational_t (big_int_of_int n)


let mkNumericalFromInt32 (n: int32) =
  new numerical_t (big_int_of_string (Int32.to_string n))


let mkNumericalFromInt64 (n: int64) =
  new numerical_t (big_int_of_string (Int64.to_string n))


let mkNumericalFromBitString s =
  if (String.length s) > 64 then
    raise
      (CHFailure
         (LBLOCK [
              STR "mkNumericalFromBitString: string is too long: ";
              INT (String.length s);
              STR " (currently only supports strings less than or equal to 64 chars"]))
  else if (String.length s) = 64 then
    try
      let s1 = String.sub s 0 32 in
      let s2 = String.sub s 32 32 in
      let i1 = Int64.of_string("0b" ^ s1) in
      let i2 = Int64.of_string("0b" ^ s2) in
      let n1 = mkNumericalFromInt64 i1 in
      let n2 = mkNumericalFromInt64 i2 in
      (n1#mult numerical_e32)#add n2
    with
    | Failure _ ->
       raise
         (CHFailure
            (LBLOCK [
                 STR "Error in 64-bit string to numerical conversion: ";
                 STR s]))
  else
    try
      let i64 = Int64.of_string ("0b" ^ s) in
      mkNumericalFromInt64 i64
    with
    | Failure _ ->
       raise
         (CHFailure
            (LBLOCK [STR "Error in bitstring to numerical conversion: "; STR s]))

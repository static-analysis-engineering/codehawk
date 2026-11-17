(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024-2026 Aarno Labs LLC

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
   ============================================================================= *)


(* cchlib *)
open CCHBasicTypes

val zero: exp
val unknown_location: location
val call_sink: location   (* used to collapse all potential free locations *)

val mk_int_constant: int -> constant

val mk_disequality : exp -> exp -> exp

val mk_equality: exp -> exp -> exp

val mk_logical_and : exp -> exp -> exp

val mk_location_string: location -> string

(** returns true if the expression is known to be zero, false otherwise *)
val exp_is_zero : exp -> bool

val char_const_to_int: char -> constant

val char_const_to_big: char -> Big_int_Z.big_int

(** [cint_to_big i64 ik] returns the mathematical value of the integer
    constant [CInt (i64, ik, _)].

    The parser stores integer constants as [int64]; an unsigned constant
    in [2^63, 2^64 - 1] (e.g., [0xffffffffffffffffUL]) is stored in
    two's-complement form, that is, as a negative [int64]. For an unsigned
    [ik] a negative [i64] is therefore read as [i64 + 2^64]. *)
val cint_to_big: int64 -> ikind -> Big_int_Z.big_int

(** [big_to_cint ~ik b] returns the representation [(i64, ik')] of the
    integer [b] as a constant [CInt (i64, ik', _)], consistent with
    [cint_to_big]: values in the [int64] range keep [ik] (default [IInt]);
    values in [2^63, 2^64 - 1] are stored in two's-complement form with
    [IULongLong]; other values cannot be represented and give [None]. *)
val big_to_cint: ?ik:ikind -> Big_int_Z.big_int -> (int64 * ikind) option

(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

open Big_int_Z

(* chlib *)
open CHPretty
open CHNumerical
open CHLanguage

(* bchlib *)
open BCHLibTypes

val e15: int
val e16: int
val e31: int
val e32: int

val nume32: numerical_t

val dw_index_to_pretty: dw_index_t -> pretty_t
val dw_index_to_string: dw_index_t -> string
val string_to_dw_index: string -> dw_index_t

val dw_index_to_int:
  dw_index_t -> int  (* only works on 64 bit architecture *)

val int_to_dw_index: int -> dw_index_t

(** doubleword representation for negative one.*)
val wordnegone: doubleword_int


(** doubleword representation for negative two.*)
val wordnegtwo: doubleword_int


(** doubleword representation for zero.*)
val wordzero: doubleword_int


(** doubleword representation for maximum value representable in 32 bits
    (0xffffffff).*)
val wordmax: doubleword_int


(** converts an integer to doubleword.*)
val index_to_doubleword:dw_index_t -> doubleword_int


(** [make_doubleword low high] constructs a doubleword by concatenating the
    bits from [high] and [low], that is, the value is [high << 16 + low]

    Causes an assertion failure if low or high are less than zero or greater
    than [2^16]
 *)
val make_doubleword:
  int -> int -> doubleword_int


(** [int_to_doubleword i] converts [i] to a doubleword.

    [i] must be greater than -2^31 and less than 2^32. If [i] is negative
    the doubleword is the 2's complement of the value (that is, 2^32 is
    added to the value).

    Causes an assertion failure if [i] is less than [-2^31] or if [i] is greater
    than or equal to [2^32].
 *)
val int_to_doubleword:
  int -> doubleword_int


(** [big_int_to_doubleword bi] converts [bi] to a doubleword.

    [bi] must be representable by a 64-bit ocaml integer and must satisfy the
    requirements for a doubleword.

    Causes an assertion failure if [bi] is less than [-2^31] or if [bi] is
    greater than or equal to [2^32].
 *)
val big_int_to_doubleword:
  big_int -> doubleword_int


val string_to_doubleword:
  string -> doubleword_int


(**[numerical_to_doubleword num] converts num to a doubleword.

   [num] must be less than [2^32] and greater than or equal [-2^31].
   Negative numbers are represented by their two's complement 
   representation.

   Causes an assertion failure if [num] is less than [-2^31] or if [num]
   is greater than or equal to [2^32].
 *)
val numerical_to_doubleword:
  numerical_t -> doubleword_int


(** [numerical_to_hex_string num] converts num to a hexadecimal string
    representation via a doubleword representation.

    [num] must be less than [2^32] and greater than or equal [-2^31].
    Negative numbers are represented by their two's complement 
    representation.

    Causes an assertion failure if [num] is less than [-2^31] or if [num]
    is greater than or equal to [2^32].
 *)
val numerical_to_hex_string:
  numerical_t -> string


(** [numerical_to_signed_hex_string num] converts [num] to a hexadecimal
    string. If [num] is negative it returns [-hex(-num)] otherwise it
    returns [hex(num)].

    Causes an assertion failure if [num] is less than [-2^31] or if [num]
    is greater than or equal to [2^32].
 *)
val numerical_to_signed_hex_string:
  numerical_t -> string


val symbol_to_doubleword: symbol_t -> doubleword_int

val doubleword_to_symbol:
  string -> ?atts:string list -> doubleword_int -> symbol_t

val align_doubleword: doubleword_int -> int -> doubleword_int

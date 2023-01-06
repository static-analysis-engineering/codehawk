(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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

(* chutil *)
open CHTraceResult

(* bchlib *)
open BCHLibTypes

val e15: int
val e16: int
val e31: int
val e32: int

val nume32: numerical_t

val dw_index_to_pretty: dw_index_t -> pretty_t

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
val index_to_doubleword:dw_index_t -> doubleword_result


(** [make_doubleword low high] constructs a doubleword by concatenating the
    bits from [high] and [low], that is, the value is [high << 16 + low].
    If either [low] or [high] is outside the range [0; 2^16-1], [Error] is
    returned.*)
val make_doubleword:
  int -> int -> doubleword_result


(** [int_to_doubleword i] converts [i] to a doubleword.

    [i] must be greater than -2^31 and less than 2^32. If [i] is negative
    the doubleword is the 2's complement of the value (that is, 2^32 is
    added to the value). If [i] is outside the range [-(2^31-1); 2^32-1].
    [Error] is returned. *)
val int_to_doubleword: int -> doubleword_result


(** [big_int_to_doubleword bi] converts [bi] to a doubleword.

    [bi] must be representable by a 64-bit ocaml integer and must satisfy the
    requirements for a doubleword, otherwise [Error] is returned.*)
val big_int_to_doubleword: big_int -> doubleword_result


(** [string_to_doubleword s] converts [s] to a doubleword. Returns
    [Error] if [s] is not a valid representation of a number or if
    the number represented is out of range for a doubleword.*)
val string_to_doubleword: string -> doubleword_result


(**[numerical_to_doubleword num] converts num to a doubleword.

   [num] must be less than [2^32] and greater than or equal [-2^31].
   Negative numbers are represented by their two's complement 
   representation. If [num] is outside this range, [Error] is
   returned.*)
val numerical_to_doubleword: numerical_t -> doubleword_result


(** [numerical_to_hex_string num] converts num to a hexadecimal string
    representation via a doubleword representation.

    [num] must be less than [2^32] and greater than or equal [-2^31].
    Negative numbers are represented by their two's complement 
    representation. If [num] is out-of-range [Error] is returned.*)
val numerical_to_hex_string: numerical_t -> string traceresult


(** [numerical_to_signed_hex_string num] converts [num] to a hexadecimal
    string. If [num] is negative it returns [-hex(-num)] otherwise it
    returns [hex(num)]. If [num] is out-of-range, [Error] is returned.*)
val numerical_to_signed_hex_string: numerical_t -> string traceresult


val symbol_to_doubleword: symbol_t -> doubleword_result

val doubleword_to_symbol:
  string -> ?atts:string list -> doubleword_int -> symbol_t


(** [align_doubleword dw a] returns the smallest doubleword that is
    a multiple of [a] and greater than or equal to [dw]. If [a] is
    less than or equal to zero [Error] is returned.*)
val align_doubleword: doubleword_int -> int -> doubleword_result

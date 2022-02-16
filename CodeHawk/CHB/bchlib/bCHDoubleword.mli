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

val wordnegone: doubleword_int
val wordnegtwo: doubleword_int

val wordzero: doubleword_int
val wordmax: doubleword_int

val index_to_doubleword:dw_index_t -> doubleword_int

val make_doubleword:
  int -> int -> doubleword_int  (* raises Invalid_argument *)

val int_to_doubleword:
  int -> doubleword_int    (* raises Invalid_argument *)

val big_int_to_doubleword:
  big_int -> doubleword_int    (* raises Invalid_argument *)

val string_to_doubleword:
  string -> doubleword_int    (* raises Invalid_argument *)

val numerical_to_doubleword:
  numerical_t -> doubleword_int   (* raises Invalid_argument *)

val numerical_to_hex_string:
  numerical_t -> string   (* raises Invalid_argument *)

val numerical_to_signed_hex_string:
  numerical_t -> string   (* raises Invalid_argument *)

val symbol_to_doubleword: symbol_t -> doubleword_int

val doubleword_to_symbol:
  string -> ?atts:string list -> doubleword_int -> symbol_t

val align_doubleword: doubleword_int -> int -> doubleword_int

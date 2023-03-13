(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
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
   ============================================================================= *)

(* chlib *)
open CHLanguage

(* chutil *)
open CHTraceResult

(* bchlib *)
open BCHLibTypes


val e7: int
val e8: int
val e15: int
val e16: int
val e31: int
val e32: int


val equal_doubleword: ?msg:string -> doubleword_int -> doubleword_int -> unit


val equal_doubleword_result:
  ?msg:string -> doubleword_int -> doubleword_result -> unit


val equal_location: ?msg:string -> location_int -> location_int -> unit


val equal_int_hexstring: ?msg:string -> int -> string -> unit


val equal_string_imm_result_hexstring:
  ?msg:string -> string -> immediate_result -> unit


val equal_string_imm_result_string:
  ?msg:string -> string -> immediate_result -> unit


val equal_assignments:
  ?msg:string
  -> function_info_int
  -> expected:(string * string) list
  -> received:(variable_t * numerical_exp_t) list
  -> unit


val returns_error:
  ?msg:string -> ('a -> string) -> (unit -> 'a traceresult) -> unit

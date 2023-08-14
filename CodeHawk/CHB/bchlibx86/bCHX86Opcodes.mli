(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019  Kestrel Technology LLC
   Copyright (c) 2020-2022  Henny Sipma
   Copyright (c) 2023       Aarno Labs LLC

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
open CHPretty

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types


val not_code_to_string: not_code_t -> string
val not_code_to_pretty: not_code_t -> pretty_t
val not_code_length: not_code_t -> int
val not_code_set_string: not_code_t -> string -> unit

val index_to_condition_code: int -> condition_code_t
val condition_code_to_suffix_string: condition_code_t -> string
val condition_code_to_name: condition_code_t -> string
val flags_used_by_condition: condition_code_t -> eflag_t list

val width_suffix_string: int -> string

val is_nop_instruction: opcode_t -> bool

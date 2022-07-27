(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
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


(* string functions *)
val string_replace: char -> string -> string -> string
val string_nsplit: char -> string -> string list

val has_control_characters: string -> bool
val byte_to_string: int -> string
val value_from_byte: int -> int

val hex_string: string -> string
val dehex_string: string -> string

val encode_string: string -> bool * string
val decode_string: bool * string -> string

(* list functions *)
val list_split: int -> 'a list -> ('a list * 'a list)
val list_split_p: ('a -> bool) -> 'a list -> ('a list * 'a list)

val list_sub: 'a list -> int -> int -> 'a list

val list_suffix: int -> 'a list -> 'a list

val list_maxf: 'a list -> ('a -> 'a -> int) -> 'a
val list_compare: 'a list -> 'a list -> ('a -> 'a -> int) -> int
val list_compare_r: 'a list -> 'a list -> ('a -> 'a -> int) -> int

val list_union_f: 'a list -> 'a list -> ('a -> 'a -> bool) -> 'a list
val list_difference: 'a list -> 'a list -> ('a -> 'a -> bool) -> 'a list
  
val remove_duplicates: 'a list -> 'a list
val remove_duplicates_f: 'a list -> ('a ->'a -> bool) -> 'a list

val array_fold_lefti: ('b -> int -> 'a -> 'b) -> 'b ->  'a array -> 'b

val xproduct: 'a list -> 'a list -> ('a * 'a) list


(* other comparison functions *)
val optvalue_compare: 'a option -> 'a option -> ('a -> 'a -> int) -> int

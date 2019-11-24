(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
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
   ============================================================================= *)

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

exception CCHFailure of pretty_t

val replace_dot     : string -> string
val open_path       : string -> (string * Zip.in_file) option
val lookup_summary  : string -> (string * Zip.in_file) -> string
val has_summary_file: (string * Zip.in_file) list -> string -> bool
val get_summary_file: (string * Zip.in_file) list -> string -> string
val apply_to_xml_jar: 
  (string -> string -> unit) -> (Zip.in_file -> Zip.entry -> unit) -> string -> unit

val time_to_string     : float -> string
val date_time_to_string: float -> string

(* get a slice from a list: 
    - arg 1: list
    - arg 2: starting index (counting from 0)
    - arg 3: number of elements in the slice 
   return None if the arg2 or arg3 is negative, or if the list does not have
   sufficient elements *)
val get_slice: 'a list -> int -> int -> 'a list option

val has_control_characters: string -> bool
val hex_string: string -> string

(* return a list of all numbers from lb to ub-1 *)
val mk_num_range: numerical_t -> numerical_t -> numerical_t list

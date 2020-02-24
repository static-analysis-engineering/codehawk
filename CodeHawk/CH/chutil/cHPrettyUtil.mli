(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma, Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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


type string_alignment_t =
  | StrCenter
  | StrLeft
  | StrRight

class type string_printer_int =
  object
    method print: pretty_t -> string
  end

val fixed_length_string: ?alignment:string_alignment_t -> string -> int -> string
val fixed_length_pretty: ?alignment:string_alignment_t -> pretty_t -> int -> pretty_t

val fixed_length_int_string: string -> int -> string
val string_suffix: string -> int -> string

val string_repeat: string -> int -> string
val nsplit: char -> string -> string list

val list_to_pretty: ('a -> pretty_t) -> pretty_t -> 'a list -> pretty_t

val string_printer: string_printer_int
  
val pretty_to_string: pretty_t -> string

val pp_quantity: int -> ?numwidth:int -> string -> string -> pretty_t

val pp_list : < toPretty : pretty_t; .. > list -> pretty_t
val pp_list_str : string list -> pretty_t
val pp_list_int : int list -> pretty_t
val pp_array :
  < toPretty : pretty_t; .. > array -> pretty_t
val pp_array_int : int array -> pretty_t
val pp_array_big_int : Z.t array -> pretty_t
val pp_matrix_int : int array array -> pretty_t
val pp_matrix_big_int : Z.t array array -> pretty_t
val pp_stack :
  < toPretty : pretty_t; .. > Stack.t -> pretty_t
val pp_assoc_int_int : (int * int) list -> pretty_t
val pp_assoc_int_big_int : (int * Z.t) list -> pretty_t
  

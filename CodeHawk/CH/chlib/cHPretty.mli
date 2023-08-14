(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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

type pretty_t =
  | STR of string
  | INT of int
  | NL
  | LBLOCK of pretty_t list
  | ABLOCK of pretty_t array
  | INDENT of int * pretty_t

val pretty_print_list :
  'a list -> ('a -> pretty_t) -> string -> string -> string -> pretty_t

val pretty_print_array :
  'a array -> ('a -> pretty_t) -> string -> string -> string -> pretty_t

class pretty_printer_t :
  out_channel ->
  object
    val mutable do_tab : bool
    val out : out_channel
    method print : pretty_t -> unit
  end

val pr_debug: pretty_t list -> unit

val set_trace_level: int -> unit
val pr_trace: int -> pretty_t list -> unit

val pr_info: pretty_t list -> unit

val pr_error: pretty_t list -> unit

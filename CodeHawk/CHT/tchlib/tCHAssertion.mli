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

(* tchlib *)
open TCHTestApi

(** Provides functions evaluating assertions. *)


(** The exception raised when an assertion fails. *)
exception Failed of failure_t


(** Raises [Failed] with the passed parameters
    (expected value, actual value, and message). *)                  
val fail: string -> string -> string -> 'a

(** [fail_msg m] is equivalent to [fail "" "" m]. *)
val fail_msg: string -> 'a


(** Default printer, always return [""]. *)
val default_printer: 'a -> string


(** [equal ~eq:e ~prn:p ~msg:m x y] raises [Failed] if [x] and [y] are not equal,
    relative to the equality function [e]. [p] is used to convert [x] and [y] 
    into strings (used only upon failure), and [m] is the message associated with
    the assertion.
    
    Default parameter values:
    - [e] defaults to [(=)]
    - [p] defaults to [default_printer];
    - [m] defaults to [""]
 *)
val equal:
  ?eq:('a -> 'a -> bool)
  -> ?prn:('a -> string)
  -> ?msg:string
  -> 'a
  -> 'a
  -> unit

  
val not_equal:
  ?eq:('a -> 'a -> bool)
  -> ?prn:('a -> string)
  -> ?msg:string
  -> 'a
  -> 'a
  -> unit


val same: ?prn:('a -> string) -> ?msg:string -> 'a -> 'a -> unit

val not_same: ?prn:('a -> string) -> ?msg:string -> 'a -> 'a -> unit


val make_equal:
  ('a -> 'a -> bool) -> ('a -> string) -> ?msg:string -> 'a -> 'a -> unit


val make_equal_list:
  ('a -> 'a -> bool)
  -> ('a -> string)
  -> ?msg:string
  -> 'a list
  -> 'a list
  -> unit


val equal_string: ?msg:string -> string -> string -> unit


(* [raise ~msg:m f] raise [Failed] if [f ()] evaluates without raising an exception *)
val raises: ?msg:string -> (unit -> 'a) -> unit


val assertionfailure: ?msg:string -> (unit -> 'a) -> unit

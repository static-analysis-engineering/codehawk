(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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

(** Result values with a list of strings as error value.*)


(** The type for result values. Either a value [Ok v] or an error 
    [Error <string-list>].*)
type 'a traceresult = ('a, string list) result


(** [tget_ok r] is [v] if [r] is [Ok v] and
    @raise [Invalid_argument] otherwise.*)
val tget_ok: 'a traceresult -> 'a


(** [tget_error r] is [e] if [r] is [Error e] and
    @raise [Invalid_argument] otherwise.*)
val tget_error: 'a traceresult -> string list


(** [tvalue r ~default] is [v] if r is [Ok v] and [default] otherwise.*)
val tvalue: 'a traceresult -> default:'a -> 'a


(** [tmap f r] is [Ok (f v)] if [r] is [Ok v] and [r] if [r] is [Error _];
    [tmap msg f r] is [Ok (f v)] if [r] is [Ok v] and [Error (msg::e)] if
    [r] is [Error e].*)
val tmap: ?msg:string -> ('a -> 'c) -> ('a traceresult) -> 'c traceresult


(** [tfold ~ok ~error r] is [ok v] if [r] is [Ok v] and [error e] if [r] is
    [Error e].*)
val tfold: ok:('a -> 'c) -> error:(string list -> 'c) -> 'a traceresult -> 'c


(** [tfold_default f d r] is [f v] if [r] is [Ok v] and [d] if [r] is
    [Error _].*)
val tfold_default: ('a -> 'c ) -> 'c -> 'a traceresult -> 'c


(** [tprop r] is [v] if [r] is [Ok v] and [Error (msg :: e)] if r is [Error e].*)
val tprop: 'a traceresult -> string -> 'a traceresult


(** [tbind f r] is [f v] if [r] is [Ok v] and [r] if [r] is [Error _]; 
    [tbind msg f r], is [f v] if [r] is [Ok v] and [Error (msg::e)] if
    [r] is [Error e].*)
val tbind:
  ?msg:string -> ('a -> 'c traceresult) -> ('a traceresult) -> 'c traceresult


(** [titer f r] is [f v] if [r] is [Ok v] and [()] otherwise.*)
val titer: ('a -> unit) -> ('a traceresult) -> unit  


(** [tfold_list ~ok init rl] folds [Ok] values left to right, starting from
    [init], ignoring [Error] values.*)
val tfold_list: ok:('c -> 'a -> 'c) -> 'c -> ('a traceresult) list -> 'c


(** [to_bool f r] is [f v] if [r] is [Ok v] and [false] otherwise.*)
val to_bool: ('a -> bool) -> 'a traceresult -> bool


(** [to_option r] is [Some v] if [r] is [Ok v] and None otherwise.*)
val to_option: 'a traceresult -> 'a option

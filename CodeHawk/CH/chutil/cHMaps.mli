(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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

exception Duplicate_found of string


module type STRINGMAP =
  sig
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val get : string -> 'a t -> 'a option
    val add : string -> 'a -> 'a t -> 'a t
    val keys : 'a t -> string list
    val fold : (string -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val addUnique : string -> 'a -> 'a t -> 'a t
    val addUniquePairs : (string * 'a) list -> 'a t -> 'a t
    val listOfPairs : 'a t -> (string * 'a) list
    val listOfKeys : 'a t -> string list
    val toPretty : 'a t -> ('a -> CHPretty.pretty_t) -> CHPretty.pretty_t
  end


module StringMap : STRINGMAP


module type INTMAP =
  sig
    type +'a t
    val mapMerge : 'a t -> 'a t -> ('a -> 'a -> 'a) -> 'a t
    val get : int -> 'a t -> 'a option
    val add : int -> 'a -> 'a t -> 'a t
    val empty : 'a t
    val toPretty: 'a t -> ('a -> CHPretty.pretty_t) -> CHPretty.pretty_t
  end


module IntMap : INTMAP

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

(** Serialization of sum types *)

(* chlib *)
open CHLanguage


(** Data structure that aids in marshaling enumeration sum types to and from
    strings.*)
class type ['a] mfts_int =
  object
    method name: string
    method ts: 'a -> string    (* to-string *)
    method fs: string -> 'a    (* from-string *)
    method tags: string list   (* recognized tags *)
  end


(** Data structure that aids in marshaling complex sum type tags to and from
    strings.*)
class ['a] mcts_t:
           string ->
object
  method name: string
  method ts: 'a -> string
  method fs: string -> 'a
  method tags: string list
end


(** [mk_fts name f] returns a marshaler for enumeration sumtypes with name
    [name] and map from sumtype to string [f].*)
val mk_mfts: string -> ('a * string) list -> 'a mfts_int


val mk_fn_mfts:
  string -> ('a * string) list -> ('a -> string) -> (string -> 'a) -> 'a mfts_int


(** marshaler for the [variable_type_t] enumeration sumtype.*)
val variable_type_mfts: variable_type_t mfts_int

(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHCommon
open CHLanguage

module H = Hashtbl


class type ['a] mfts_int =
  object
    method name: string
    method ts: 'a -> string
    method fs: string -> 'a
    method tags: string list
  end


class ['a] mfts_t
           (name:string) (pairs:('a * string) list):['a] mfts_int =
object

  val tstable = H.create (List.length pairs)
  val sttable = H.create (List.length pairs)

  initializer
    List.iter (fun (t,s) ->
        begin
          H.add tstable t s;
          H.add sttable s t
        end) pairs

  method name = name

  method ts (t:'a) =
    if H.mem tstable t then
      H.find tstable t
    else
      raise (CHFailure (LBLOCK [STR "Type not found for sumtype "; STR name]))

  method fs (s:string) =
    if H.mem sttable s then
      H.find sttable s
    else
      raise
        (CHFailure
           (LBLOCK [STR "No sumtype "; STR name; STR " for string "; STR s]))

  method tags =
    let tags = H.fold (fun k _ a -> k::a) sttable  [] in
    List.sort (fun s1 s2 -> Stdlib.compare s1 s2) tags

end

let mk_mfts = new mfts_t


(* Converter that can be used when only a few types have
   additional data, which can be encoded into and decoded
   from the strin
 *)
class ['a] fn_mfts_t
           (name:string)
           (pairs:('a * string) list)
           (f:'a -> string)
           (g:string -> 'a):['a] mfts_int =
object

  inherit ['a] mfts_t name pairs as super

  method! ts (t:'a) =
    try
      super#ts t
    with
    | CHFailure _ -> f t

  method! fs (s:string) =
    try
      super#fs s
    with
    | CHFailure _ -> g s

end

let mk_fn_mfts = new fn_mfts_t


class ['a] mcts_t (name:string) =
object

  inherit ['a] mfts_t name []

  method! fs (_:string):'a =
    raise
      (CHFailure
         (LBLOCK [STR "No reverse construction possible for "; STR name]))

end


let variable_type_mfts: variable_type_t mfts_int =
  mk_mfts
    "variable_type_t"
    [(NUM_LOOP_COUNTER_TYPE, "nlc");
     (NUM_TMP_VAR_TYPE, "ntv");
     (SYM_TMP_VAR_TYPE, "stv");
     (NUM_TMP_ARRAY_TYPE, "nta");
     (SYM_TMP_ARRAY_TYPE, "sta");
     (NUM_VAR_TYPE, "nv");
     (SYM_VAR_TYPE, "sv");
     (NUM_ARRAY_TYPE, "na");
     (SYM_ARRAY_TYPE, "sa")]

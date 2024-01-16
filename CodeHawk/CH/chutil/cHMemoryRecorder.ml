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

(** Utility to take snapshots of memory usage *)

open Gc

(* chlib *)
open CHPretty

(* chutil *)
open CHPrettyUtil


class type memory_recorder_int =
object
  method take_snapshot: string -> unit
  method toPretty     : pretty_t
end


class memory_recorder_t:memory_recorder_int =
object

  val mutable recordings = []

  method take_snapshot (tag:string) =
    let stat = Gc.quick_stat () in
    recordings <- (tag,stat.heap_words) :: recordings

  method toPretty =
    List.fold_left
      (fun a (k,v) ->
        LBLOCK [a; NL; fixed_length_pretty (STR k) 30; STR ": "; INT v])
      (LBLOCK [STR "Memory snapshots"])
      (List.rev recordings)
end

let chmemory_recorder = new memory_recorder_t

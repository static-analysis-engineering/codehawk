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

(** Utilities to output a GraphViz dot file *)

(* chlib *)
open CHLanguage
open CHPretty


class type dot_graph_int =
object ('a)
  method setPreamble: pretty_t -> unit
  method setRankdir : string -> unit
  method addEdge:
           ?bidirectional:bool -> ?label:string -> string -> string -> unit
  method addNode: ?label:string -> ?shaded:bool -> string -> unit
  method hasNode: string -> bool
  method hasEdge: string -> string -> bool
  method subgraph: string -> string -> 'a
  method revsubgraph: string -> string -> 'a
  method toPretty: pretty_t
end

val mk_dot_graph: ?enable_bidirectional_edges:bool -> string -> dot_graph_int


val cfg_to_dot: cfg_int -> dot_graph_int

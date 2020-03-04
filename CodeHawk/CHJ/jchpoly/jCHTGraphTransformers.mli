(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
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

(* jchpre *)
open JCHPreAPI

val init_calls_graph : JCHTGraph.taint_graph_t -> JCHTGraph.taint_graph_t 
val make_stub :
  JCHTGraph.taint_graph_t
  -> (JCHTGraph.taint_graph_t
      * (taint_node_int * taint_node_int) list)

val remove_calls : 
  JCHTGraph.taint_graph_t 
  -> (int, JCHTGraph.taint_graph_t) Hashtbl.t
  -> (int, JCHTGraph.taint_graph_t) Hashtbl.t
  -> (int, JCHTGraph.taint_graph_t) Hashtbl.t
  -> CHUtils.SymbolCollections.set_t 
  -> JCHTGraph.taint_graph_t * bool
  
val prune_vars:
  JCHTGraph.taint_graph_t -> JCHTGraph.taint_graph_t
  
val make_env:
  JCHTGraph.taint_graph_t -> JCHTGraph.taint_graph_t -> JCHTGraph.taint_graph_t 

val propagate_taint : JCHTGraph.taint_graph_t -> unit

val dbg : bool ref

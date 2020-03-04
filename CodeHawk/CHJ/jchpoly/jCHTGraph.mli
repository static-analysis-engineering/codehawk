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

(* chlib *)
open CHLanguage
open CHPretty

(* jchpre *)
open JCHPreAPI

class taint_graph_t :
  proc_name:symbol_t
  -> sig_nodes:taint_node_int list
  -> fields:JCHTNode.TaintNodeCollections.set_t
  -> call_nodes:JCHTNode.TaintNodeCollections.set_t
  -> calls:JCHTNode.TaintNodeCollections.set_t
  -> var_nodes:JCHTNode.TaintNodeCollections.set_t
  -> edges:JCHTNode.TaintNodeCollections.set_t JCHTNode.TaintNodeCollections.table_t
  -> rev_edges:JCHTNode.TaintNodeCollections.set_t JCHTNode.TaintNodeCollections.table_t
  -> sources:JCHTNode.TaintNodeCollections.set_t
  ->  object ('a)
      method add_edge:taint_node_int -> taint_node_int -> unit
      method equal : 'a -> bool 
      method get_arg_nodes:taint_node_int list
      method get_call_nodes : JCHTNode.TaintNodeCollections.set_t
      method get_calls : JCHTNode.TaintNodeCollections.set_t
      method get_var_nodes : JCHTNode.TaintNodeCollections.set_t
      method get_edges :
          JCHTNode.TaintNodeCollections.set_t JCHTNode.TaintNodeCollections.table_t
      method get_fields : JCHTNode.TaintNodeCollections.set_t
      method get_proc_name:symbol_t
      method get_return_node:taint_node_int option
      method get_sources : JCHTNode.TaintNodeCollections.set_t
      method get_ret_and_arg_nodes:taint_node_int list
      method get_rev_edges :
          JCHTNode.TaintNodeCollections.set_t JCHTNode.TaintNodeCollections.table_t
      method get_sig_nodes:taint_node_int list
      method leq : 'a -> bool 
      method toPretty:pretty_t
    end

val make_tgraph : JCHProcInfo.jproc_info_t -> taint_graph_t 

val mk_empty_tgraph:symbol_t -> taint_graph_t

val add_edges_to_big_graph:(taint_node_int * taint_node_int) list -> unit
val connect_to_big_graph : taint_graph_t -> unit 
val taint_big_graph:taint_node_int list -> taint_node_int list -> unit

val restrict_big_graph_to_proc : 
  symbol_t 
  -> JCHTNode.TaintNodeCollections.set_t JCHTNode.TaintNodeCollections.table_t

val dbg : bool ref 

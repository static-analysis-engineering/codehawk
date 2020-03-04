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
open CHPretty
open CHPrettyUtil
open CHLanguage
open CHUtils

(* jchlib *)
open JCHBasicTypes

(* jchpre *)
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils
open JCHSystemUtils

module H = Hashtbl

let dbg = ref false

let tgraphs = ref (H.create 0)
let calls_tgraphs = ref (H.create 0)
let no_call_tgraphs = ref (H.create 0)
let stub_tgraphs = ref (H.create 0)
let env_tgraphs = ref (H.create 0)

let make_no_call_tgraphs () =
  let (procs, _) =
    JCHSystem.jsystem#get_call_graph_manager#get_bottom_up_list in
  let size = JCHSystem.jsystem#get_number_procs in
  
  tgraphs := H.create size ;
  calls_tgraphs := H.create size ;
  no_call_tgraphs := H.create size ;
  stub_tgraphs := H.create size ;
  env_tgraphs := H.create size ;

  let procs_with_calls = new SymbolCollections.set_t in

  (* Make a graph for each method *)
  let make_graph proc_name =
    
    (if !dbg then
       pr__debug [STR "make_graph "; proc_name#toPretty; NL]) ;
    
    let proc_info = JCHSystem.jsystem#get_jproc_info proc_name in
    
    (if !dbg then
       pr__debug [STR "proc_info = "; NL; proc_info#toPretty; NL]) ;
    
    let tgraph = JCHTGraph.make_tgraph proc_info in
    
    (if !dbg then
       pr__debug [STR "tgraph = "; tgraph#toPretty; NL]) ;
    
    let calls_tgraph = JCHTGraphTransformers.init_calls_graph tgraph in
    H.replace !tgraphs proc_name#getSeqNumber tgraph ; 
    H.replace !calls_tgraphs proc_name#getSeqNumber calls_tgraph ;
  in
  List.iter make_graph procs ;

  (* Make a stub graph for each method the nodes of which are signature 
   * variables and fields
   * If this is not possible because the method is part of a loop then the 
   * stub graph will also involve the signature variables of other methods 
   * called by this method *)
  let make_no_calls proc_name =
    
    (if !dbg then
       pr__debug [(JCHSystem.jsystem#get_jproc_info proc_name)#toPretty; NL]) ;
    
    let tgraph = 
      try
	H.find !tgraphs proc_name#getSeqNumber
      with
	Not_found ->
	raise
          (JCH_failure
             (LBLOCK [ STR "taint graph for " ; proc_name#toPretty ;
		       STR " not found in JCHTaintGraphAnalysis.make_no_calls" ])) in
    let (no_call_tgraph, has_calls) =
      JCHTGraphTransformers.remove_calls
        tgraph !tgraphs !calls_tgraphs !stub_tgraphs procs_with_calls in
    H.replace !no_call_tgraphs proc_name#getSeqNumber no_call_tgraph ;
    
    (if !dbg then
       pr__debug [STR "no_call_tgraph = "; no_call_tgraph#toPretty; NL]) ;
    
    let (stub_tgraph, field_edges) = 
      JCHTGraphTransformers.propagate_taint no_call_tgraph ;
      let pg = JCHTGraphTransformers.prune_vars no_call_tgraph in
      let res = JCHTGraphTransformers.make_stub pg in
      res in
    if has_calls then 
      begin
	procs_with_calls#add proc_name ;
	let edges = stub_tgraph#get_edges in
	let edge_list = ref [] in
	let add_edges nd set = 
	  set#iter (fun nd1 -> edge_list := (nd, nd1) :: !edge_list) in
	edges#iter add_edges ;
	JCHTGraph.add_edges_to_big_graph !edge_list ;
      end
    else JCHTGraph.add_edges_to_big_graph field_edges ;
    H.replace !stub_tgraphs proc_name#getSeqNumber stub_tgraph in 
  List.iter make_no_calls procs ; 
  procs_with_calls


(* Collect all the relationships between fields and the arguments of the
 *  top graphs in one graph
 * Propagate the taint from the arguments fields *)
let make_big_graph () = 
  JCHTGraph.dbg := !dbg;
  JCHTNode.dbg := !dbg ;
  pr__debug [STR "make_big_graph"; NL] ; 
  let unknown_input_nodes = ref [] in
  let untrusted_input_nodes = ref [] in
  let add_graph proc_name = 
    let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
    let method_info = jproc_info#get_method_info in
    let g = 
      try
	H.find !stub_tgraphs proc_name#getSeqNumber
      with
	Not_found ->
	raise
          (JCH_failure
             (LBLOCK [ STR "graph for " ; proc_name#toPretty ;
		       STR " not found in JCHTGraphAnalysis.make_big_graph" ])) in
    let arg_nodes = g#get_arg_nodes in
    let set_untrusted str (nd : JCHPreAPI.taint_node_int) = 
      match nd#get_node_type with
      | TN_VAR (cmsix, var, _) ->
         let proc_name = make_procname cmsix in
	 let orig = JCHTaintOrigin.mk_var_origin proc_name var in
	 let _ =
           nd#add_untrusted_origins (JCHTaintOrigin.mk_taint_origin_set [orig])  in
	 ()
      | _ ->
         raise
           (JCH_failure (STR "Expected untrusted arguments of main")) in
    if method_info#is_main_method then
      begin
	untrusted_input_nodes := arg_nodes @ !untrusted_input_nodes ;
	List.iter (set_untrusted "") arg_nodes;
      end
    else 
      begin
	unknown_input_nodes := arg_nodes @ !unknown_input_nodes ;
	if method_info#is_dynamically_dispatched then 
	  List.iter (set_untrusted "dynamically dispatched") arg_nodes;
	if method_info#is_called_by_reflection then
	  List.iter (set_untrusted "called by reflection") arg_nodes;
	if method_info#is_indirectly_called then 
	  List.iter (set_untrusted "indirectly caled") arg_nodes;
	if JCHAnalysisUtils.has_untranslated_caller proc_name then 
	    List.iter (set_untrusted "untranslated caller") arg_nodes
      end ;
    JCHTGraph.connect_to_big_graph g ;
  in
  List.iter add_graph JCHSystem.jsystem#get_procedures ;

  pr__debug [STR "Added top graphs. Start connecting fields. " ; NL] ;
  JCHTGraph.taint_big_graph !untrusted_input_nodes !unknown_input_nodes    

(* Taint every graph from the fields and the propgated taint from the tainted 
 * inputs of the top methods *)
let make_env_tgraphs () = 
  let (procs, _) = JCHSystem.jsystem#get_call_graph_manager#get_top_down_list in
  let done_procs = new IntCollections.set_t in
  let taint_graph proc_name = 
    let no_call_tgraph = 
      try
	H.find !no_call_tgraphs proc_name#getSeqNumber
      with
      | Not_found ->
	 raise
           (JCH_failure
              (LBLOCK [ STR "call graph for " ; proc_name#toPretty ;
			STR " not found in JCHTGraphAnalysis.make_env_tgraphs" ])) in
    let calls_tgraph = 
      try
	H.find !calls_tgraphs proc_name#getSeqNumber
      with
	Not_found ->
	raise
          (JCH_failure
             (LBLOCK [ STR "calls graph fro " ; proc_name#toPretty ;
		       STR " not found in JCHTGraphAnalysis.make_env_tgraphs" ])) in
    let env_tgraph = JCHTGraphTransformers.make_env no_call_tgraph calls_tgraph in
    JCHTGraphTransformers.propagate_taint env_tgraph ;
    H.replace !env_tgraphs proc_name#getSeqNumber env_tgraph ; 
    done_procs#add proc_name#getSeqNumber in
  List.iter taint_graph procs 


(* Set taint in the analysis_results *)
let set_taint_proc proc_name = 
  let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
  let analysis_results = jproc_info#get_analysis_results in
  let env_tgraph = 
    try
      H.find !env_tgraphs proc_name#getSeqNumber
    with
    | Not_found ->
       raise
         (JCH_failure
            (LBLOCK [ STR "env tgraph for " ; proc_name#toPretty ;
		      STR " not found in JCHTGraphAnalysis.set_taint_proc" ])) in
  let pc_to_loop_vars = JCHTaintLoopUtils.get_pc_to_loop_vars jproc_info in
  let local_var_maps = JCHNumericAnalysis.get_local_var_maps proc_name in
  let set_pc (pc, local_var_map) = 
    let taint_list = ref [] in
    let lc_vars = 
      match pc_to_loop_vars#get pc with 
      |	Some set -> set#toList
      |	_ -> [] in
    let add_var_taint (original_var, var) = 
      let var_node = JCHTNode.mk_var_node proc_name var in
      taint_list := (original_var, var_node#get_untrusted_origins) :: !taint_list ;
    in
    List.iter add_var_taint local_var_map#listOfPairs ;
    List.iter add_var_taint (List.map (fun lc -> (lc, lc)) lc_vars);
    analysis_results#set_taint_origins pc !taint_list in
  List.iter set_pc local_var_maps#listOfPairs ;
  (match env_tgraph#get_return_node with 
  | Some rnode -> 
     analysis_results#set_return_origins
       rnode#get_untrusted_origins (* rnode#get_unknown_origins *)
  | _ -> ())
  
let set_taint () = 
  let (procs, _) = JCHSystem.jsystem#get_call_graph_manager#get_top_down_list in
  List.iter set_taint_proc procs 
 
let make_tgraphs save_results =
  
  pr__debug [STR "Start making stub tgraphs "; NL] ;
  let _ = make_no_call_tgraphs () in
  JCHSystemUtils.add_timing "make stub tgraphs" ;

  pr__debug [STR "Start making the top tgraph"; NL] ;
  make_big_graph () ;
  JCHSystemUtils.add_timing "make big graph" ;

  pr__debug [STR "Start making env tgraphs "; NL] ;
  make_env_tgraphs ();
  JCHSystemUtils.add_timing "env tgraphs" ;

  if save_results then
    begin
      pr__debug [STR "Start setting taint "; NL] ;
      set_taint ();
      JCHSystemUtils.add_timing "set taint" ;
    end ;

  pr__debug [ JCHTaintOrigin.taint_origins_to_pretty () ; NL ] ;
  calls_tgraphs := H.create 0 ;
  no_call_tgraphs := H.create 0 ;
  stub_tgraphs := H.create 0 ;
  env_tgraphs := H.create 0 ; 
  pr__debug [STR "Finished making the graphs"; NL]  
    

let get_tgraphs () = !tgraphs

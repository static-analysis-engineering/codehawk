(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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

(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

module H = Hashtbl


let tgraphs = ref (Hashtbl.create 0)

let taint_origin_ind = ref (-1)
let _unknown_rev_edges = ref (new JCHTNode.TaintNodeCollections.table_t)
let untrusted_rev_edges = ref (new JCHTNode.TaintNodeCollections.table_t)

(* populates untrusted_origin_to_rev_edges *)
let make_taint_origin_graphs taint_origin_index =
  tgraphs := JCHTGraphAnalysis.get_tgraphs ();
  taint_origin_ind := taint_origin_index;
  untrusted_rev_edges := new JCHTNode.TaintNodeCollections.table_t;

   let add_edge node1 node2 =
   if node1#compare node2 != 0 then
   begin
     pr__debug [STR "add_edge "; node1#toPretty; STR " "; node2#toPretty; NL];
     let (rev_edges, set1, set2) =
       let untrusted1 = node1#get_untrusted_origins in
       let untrusted2 = node2#get_untrusted_origins in
       (!untrusted_rev_edges, untrusted1, untrusted2) in
     let has_taint set = set#has_origin_index taint_origin_index in
     if has_taint set1 && has_taint set2 then
       match rev_edges#get node2 with
       | Some set -> set#add node1
       | _ ->
          rev_edges#set node2 (JCHTNode.TaintNodeCollections.set_of_list [node1])
   end in

   let add_graph tgraph =

    pr__debug [NL; NL; STR "mk_taint_origin_graphs add_graph ";
               tgraph#get_proc_name#toPretty; NL; tgraph#toPretty; NL];

    let graph_edges: JCHTNode.TaintNodeCollections.set_t JCHTNode.TaintNodeCollections.table_t =
      tgraph#get_edges in

    let add_graph_edge node1 node2 =

      pr__debug [
          STR "add_graph_edge "; node1#toPretty; STR " "; node2#toPretty; NL];

      begin
	match (node1#get_node_type, node2#get_node_type) with
	| (TN_VAR (cmsix , v, _), TN_CALL (_, _, _, tgtix, ret_opt, args)) ->
           let pn = make_procname cmsix in
           let tinfo = JCHApplication.app#get_method (retrieve_cms tgtix) in
	   let tproc_name = tinfo#get_procname in
	   if tinfo#is_stubbed then
	     begin
	       let tgraph =
                 JCHTGraphStubs.get_lib_stub
                   tproc_name tinfo#get_class_method_signature in
	       let arg_nodes = tgraph#get_arg_nodes in
	       try (* For the case v is a return node *)
		 let arg_node = List.assoc v (List.combine args arg_nodes) in
		 let succ_stub_nodes =
		   match tgraph#get_edges#get arg_node with
		   | Some set -> set#toList
		   | _ -> [] in
		 let get_arg_node stub_node : taint_node_int =
		   match stub_node#get_node_type with
		   | TN_VAR (_, v, _) ->
		      let var =
			if JCHSystemUtils.is_return v then
                          Option.get ret_opt
			else
                          List.assoc stub_node (List.combine arg_nodes args) in
		      JCHTNode.mk_var_node pn var
		   | _ -> stub_node in
		 let succ_nodes = List.map get_arg_node succ_stub_nodes in
		 List.iter (add_edge node1) succ_nodes
	       with _ -> ()
	     end
	   else
	     begin
	       let tgraph =
		 try
		   H.find !tgraphs tproc_name#getSeqNumber
		 with
		 | Not_found ->
		    raise
                      (JCH_failure
                         (LBLOCK [
                              STR "taint graph for "; tproc_name#toPretty;
			      STR " not found in JCHTGraphAnalysis.mk_taint_origin_graph"])) in
	       let arg_nodes = tgraph#get_arg_nodes in
	       let pairs = List.combine args arg_nodes in
	       begin
		 try (* This is a return node *)
		   let arg_node = List.assoc v pairs in
		   add_edge node1 arg_node
		 with _ -> ()
	       end
	     end
	| (TN_CALL (_, _, _callerix, tgtix, _ret_opt, args), TN_VAR (_, v, _)) ->
           let tinfo = app#get_method (retrieve_cms tgtix) in
	   let tproc_name = tinfo#get_procname in
	   if tinfo#is_stubbed then
	     begin
	       let tgraph =
                 JCHTGraphStubs.get_lib_stub
                   tproc_name tinfo#get_class_method_signature in
	       let add_source source =
		 let _ =
                   node1#add_untrusted_origins source#get_untrusted_origins in
		 () in
	       tgraph#get_sources#iter add_source;

	       add_edge node1 node2;
	     end
	   else
	     begin
	       let tgraph = H.find !tgraphs tproc_name#getSeqNumber in
	       try (* This is an argument node which could get tainted in the
                    * calling method but we do not cover that yet *)
		 let ret_node = Option.get tgraph#get_return_node in
		 let ref_eq_node = JCHTNode.mk_ref_equal_node () in
		 add_edge ret_node ref_eq_node;
		 add_edge ref_eq_node node2
		  with _ ->
		    let arg_nodes = tgraph#get_arg_nodes in
		    let pairs = List.combine args arg_nodes in
		    let arg_node = List.assoc v pairs in
		    let ref_eq_node = JCHTNode.mk_ref_equal_node () in
		    add_edge arg_node ref_eq_node;
		    add_edge ref_eq_node node2
		end
	  | _ -> add_edge node1 node2
	end in
    graph_edges#iter (fun n s -> s#iter (add_graph_edge n)) in

  let (procs, _) = JCHSystem.jsystem#get_call_graph_manager#get_bottom_up_list in

  List.iter (fun proc_name ->
      add_graph (H.find !tgraphs proc_name#getSeqNumber)) procs;

  pr__debug [
      NL; STR "after make_taint_origin_graphs, untrusted_origin_to_rev_edges = ";
      !untrusted_rev_edges#toPretty; NL]


let remove_stack_vars edges rev_edges =
  let get_assoc table node =
    match table#get node with
    | Some set -> set#toList
    | _ -> [] in

  let remove_from_table table node keys =
    let remove_key key =
      match table#get key with
      | Some set -> set#remove node
      | _ -> () in
    List.iter remove_key keys;
    table#remove node in

  let add_edge_t table node1 node2 =
    match table#get node1 with
    | Some set -> set#add node2
    | _ -> table#set node1 (JCHTNode.TaintNodeCollections.set_of_list [node2]) in

  let add_edge table rev_table node1 node2 =
    add_edge_t table node1 node2;
    add_edge_t rev_table node2 node1 in

  let remove node =
    let prevs =
      List.filter (fun n -> (node#compare n) <> 0) (get_assoc rev_edges node) in
    let succs =
      List.filter (fun n -> (node#compare n) <> 0) (get_assoc edges node) in
    remove_from_table edges node prevs;
    remove_from_table rev_edges node succs;

    List.iter (fun n1 -> List.iter (add_edge edges rev_edges n1) succs) prevs in

  let nodes = new JCHTNode.TaintNodeCollections.set_t in
  nodes#addList edges#listOfKeys;
  nodes#addList rev_edges#listOfKeys;

  let not_needed node =
    match node#get_node_type with
    | TN_VAR (cmsix, v, _) ->
       let pn = make_procname cmsix in
       let jproc_info = JCHSystem.jsystem#get_jproc_info pn in
       let jvar_info = jproc_info#get_jvar_info v in
       not (jvar_info#is_return
            || jvar_info#is_parameter
            || jvar_info#is_local_var
            || JCHSystemUtils.is_loop_counter v)
    | TN_FIELD _ -> false
    | TN_CALL _ -> false (* leave the STUB_CALL sources *)
    | TN_CONDITIONAL _ -> false
    | _ -> true in

  let nodes_to_remove = List.filter not_needed nodes#toList in

  List.iter remove nodes_to_remove;
  let new_edges =  new JCHTNode.TaintNodeCollections.table_t in
  let new_rev_edges =  new JCHTNode.TaintNodeCollections.table_t in
  let remove_version_var var =
    if JCHSystemUtils.is_loop_counter var then var
    else make_variable var#getName#getBaseName var#getType in
  let remove_version_node node =
    match node#get_node_type with
    | TN_VAR (cmsix, v, pc) ->
	let pn = make_procname cmsix in
	let orig_node =
	  try
	    let index = v#getIndex in
	    let var_map =
              (Option.get
                 ((JCHNumericAnalysis.get_local_var_maps pn)#get pc))#listOfPairs in
	    let orig_v =
              fst
                (List.find
                   (fun (_, version_v) -> version_v#getIndex = index) var_map) in
	    JCHTNode.mk_var_node_pc pc pn orig_v
	  with _ -> JCHTNode.mk_var_node_pc pc pn (remove_version_var v) in
	let _ = node#add_all_untrusted_origins orig_node in
	orig_node
    | _ -> node in
  let remove_version_edges node1 set =
    let new_node1 = remove_version_node node1 in
    let remove_version_edge node2 =
      add_edge new_edges new_rev_edges new_node1 (remove_version_node node2) in
    set#iter remove_version_edge in
  edges#iter remove_version_edges;
  (new_edges, new_rev_edges)

let make_graph () =
  let reverse_edges rev_edges =
    let edges = new JCHTNode.TaintNodeCollections.table_t in
    let add_edges node prev_nodes =
      let add_edge prev_node =
	match edges#get prev_node with
	| Some set -> set#add node
	| _ ->
	    let set = JCHTNode.TaintNodeCollections.set_of_list [node] in
	    edges#set prev_node set in
      prev_nodes#iter add_edge in
    rev_edges#iter add_edges;
    edges in
  let (rev_edges, edges) =
    (untrusted_rev_edges, ref (reverse_edges !untrusted_rev_edges)) in
  let (_, res) = (remove_stack_vars !edges !rev_edges) in
  rev_edges := res;
  edges := reverse_edges !rev_edges;
  let remove_empty table node set =
    if set#isEmpty then table#remove node in
  !rev_edges#iter (remove_empty !rev_edges);
  !edges#iter (remove_empty !edges);

  let taint_origin = JCHTaintOrigin.get_taint_origin !taint_origin_ind in
  let found node =
    match (taint_origin#get_origin, node#get_node_type) with
    | (T_ORIG_FIELD (cfsix1, _, _, _), TN_FIELD cfsix2) -> cfsix1 = cfsix2
    | (T_ORIG_VAR (cmsix1, v1), TN_VAR (cmsix2, v2, _)) ->
       cmsix1 = cmsix2 && v1#equal v2
    | (T_ORIG_CALL (cmsix, _, _, _), TN_CALL (_, _, _, tgtix , _, _)) ->
       cmsix = tgtix
    | (T_ORIG_STUB (cmsix, _, _), TN_CALL (_, _, _, tgtix, _, _)) ->
       cmsix = tgtix
    | _ -> false in

  let new_edges = new JCHTNode.TaintNodeCollections.table_t in
  let added = ref [] in
  let rec work ns =
    match ns with
    | n :: rest_ns ->
	if not (List.mem n !added) then
	  begin
	    added := n :: !added;
	    match !edges#get n with
	    | Some succs ->
		new_edges#set n succs;
		work (succs#toList @ rest_ns)
	    | _ -> work rest_ns
	  end
	else work rest_ns
    | _ -> () in
  work (List.filter found !edges#listOfKeys);
  rev_edges := reverse_edges new_edges;

  pr__debug [
      NL; STR "after prune_graph, rev_edges = "; NL; !rev_edges#toPretty; NL];
  !rev_edges

    (* produces the graph from to a given taint origin to all the nodes touched
       by this taint *)
let get_taint_origin_graph
      local_vars_only taint_origin_ind:
      JCHTNode.TaintNodeCollections.set_t JCHTNode.TaintNodeCollections.table_t =

  pr__debug [NL; STR "get_taint_origin_graph "; INT taint_origin_ind; NL];

  make_taint_origin_graphs taint_origin_ind;
  let res =
    if local_vars_only then
      make_graph ()
    else
      !untrusted_rev_edges in
  begin
    pr__debug [NL; STR "res: "; INT (res#size); NL; res#toPretty; NL];
    res
  end

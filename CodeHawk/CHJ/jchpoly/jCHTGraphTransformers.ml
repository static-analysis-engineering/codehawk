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
open CHLanguage
open CHUtils
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHMethod
open JCHPreAPI
open JCHTaintOrigin


open JCHTNode
open JCHTGraph
open JCHPrintUtils

module H = Hashtbl

let dbg = ref false


class tgraph_transformer_t (tgraph: taint_graph_t) =
  object (self: 'a)
    val proc_name = tgraph#get_proc_name
    val sig_nodes = tgraph#get_sig_nodes
    val arg_nodes = tgraph#get_arg_nodes
    val return_node_opt = tgraph#get_return_node
    val ret_and_arg_nodes = tgraph#get_ret_and_arg_nodes
    val fields = tgraph#get_fields
    val call_nodes = tgraph#get_call_nodes
    val calls = tgraph#get_calls
    val var_nodes = tgraph#get_var_nodes
    val edges = tgraph#get_edges
    val rev_edges = tgraph#get_rev_edges

    val new_sig_nodes = ref []
    val new_fields = ref (new TaintNodeCollections.set_t)
    val new_call_nodes = ref (new TaintNodeCollections.set_t)
    val new_calls = ref (new TaintNodeCollections.set_t)
    val new_var_nodes = ref (new TaintNodeCollections.set_t)
    val new_edges = ref (new TaintNodeCollections.table_t)
    val new_rev_edges = ref (new TaintNodeCollections.table_t)

    method private add_table_edge table n1 n2 =
      match table#get n1 with
      |	Some set -> set#add n2
      |	None ->
	  let set = TaintNodeCollections.set_of_list [n2] in
	  table#set n1 set

    method add_edge rn wn =
      begin
        self#add_table_edge !new_edges rn wn;
        self#add_table_edge !new_rev_edges wn rn
      end

    method transform =
      new_sig_nodes := sig_nodes

    method make_tgraph =
      self#transform;

      (if !dbg then
         pr__debug [STR "make_tgraph new_edges: "; NL;
                    !new_edges#toPretty; NL;
                    STR "make_tgraph new_rev_edges: "; NL;
                    !new_rev_edges#toPretty; NL]);

      new taint_graph_t
          ~proc_name
	  ~sig_nodes:!new_sig_nodes
          ~fields:!new_fields
          ~call_nodes:!new_call_nodes
          ~calls:!new_calls
          ~var_nodes:!new_var_nodes
	  ~edges:!new_edges
          ~rev_edges:!new_rev_edges
          ~sources:tgraph#get_sources

  end

(* Removes nodes that are not tainted and are not sig_nodes or fields
 * Removes nodes that have no edges
 * Removes unk_fields - the taint was already propagated and the fields
 * cannot get any more taint *)
class stub_transformer_t (tgraph:taint_graph_t) =
  object (self: 'a)
    inherit tgraph_transformer_t tgraph as super

    val not_unk_fields = new TaintNodeCollections.set_t
    val field_edges = ref []
    method get_field_edges = !field_edges

    method private add_tedges =
      let remove n =
	let r = not (List.mem n sig_nodes || n#is_field) in

	(if !dbg then
           pr__debug [STR "remove "; n#toPretty; STR " res: "; pp_bool r; NL]);

	r in
      let add_te (n1: taint_node_int) (n2: taint_node_int) =

	(if !dbg then
           pr__debug [STR "add_te "; n1#toPretty; STR " "; n2#toPretty; NL]);

	match (remove n1, remove n2) with
	| (false, false) ->

	   (if !dbg then
              pr__debug [STR "add_te do not remove"; NL]);

	   if n1#is_field && n2#is_field then
             field_edges := (n1, n2) :: !field_edges
	   else
             super#add_edge n1 n2
	| _ -> () in
      let add_tes n set = set#iter (add_te n) in
      edges#iter add_tes

    method !transform =
      begin
        self#add_tedges;
        new_sig_nodes := sig_nodes;
        new_fields := not_unk_fields;
        new_call_nodes := call_nodes;
        new_calls := calls
      end

  end

(* Uses the library stubs to remove the call nodes
 * for which there is a stub or remove all library calls
 * If unknown calls are removed than variables are connected to T
 * It also adds edegs to the call tgraph *)
class call_remover_t
    (tgraph:  taint_graph_t)
    (tgraphs: (int, JCHTGraph.taint_graph_t) H.t)
    (calls_tgraphs: (int, JCHTGraph.taint_graph_t) H.t)
    (stub_tgraphs: (int, JCHTGraph.taint_graph_t) H.t)
    (procs_with_calls: SymbolCollections.set_t) =
  object (self: 'a)
    inherit tgraph_transformer_t tgraph

    val removed = new TaintNodeCollections.set_t
    val has_calls = ref false
    val changed_calls = new SymbolCollections.set_t

    method has_calls = !has_calls

    method private remove_unknown_call tinfo snodes_opt str caller pc =

      (if !dbg then
         pr__debug [STR "remove_unknown_call "; NL]);

      match snodes_opt with
      | Some snodes ->
	 begin

	   (if !dbg then
              pr__debug [STR "snodes = "; snodes#toPretty; NL]);

	    let add_unknown n =
	      match n#get_node_type with
	      | TN_VAR (_,v, _) ->
		  if not (v = JCHGlobals.exception_var) then
		    let origs =
                      mk_taint_origin_set
                        [mk_call_origin tinfo str caller pc] in
		    let _ = n#add_untrusted_origins origs in
		    ()
	      | _ -> () in
	    snodes#iter add_unknown;
	  end
      | None -> ()

    method private record_call cproc_name iproc_name args =

      (if !dbg then
         pr__debug [STR "record_call "; cproc_name#toPretty; NL;
                    iproc_name#toPretty; STR " "; pp_list args; NL]);

      let calls_tgraph =
	try
	  H.find calls_tgraphs iproc_name#getSeqNumber
	with
	| Not_found ->
	   raise
             (JCH_failure
                (LBLOCK [
                     STR "calls taint graph for "; iproc_name#toPretty;
		     STR " not found in JCHTGraphTransformer.record_call"])) in

      (if !dbg then
         pr__debug [STR "calls_tgraph#get_arg_nodes = ";
                    pp_list (calls_tgraph#get_arg_nodes); NL]);

      let pairs =  List.combine args calls_tgraph#get_arg_nodes in
      let add_arg_edge (arg, iarg_node) =
	let arg_node = mk_var_node cproc_name arg in
	calls_tgraph#add_edge arg_node iarg_node in
      List.iter add_arg_edge pairs

    method private remove_known_call
                     tnode
                     is_stub
                     (cname: symbol_t)
                     (iname: string)
                     (call_vars: variable_t list)
                     (igraph: taint_graph_t)
                     pc =

      (if !dbg then
         pr__debug [STR "remove_known_call "; cname#toPretty; STR " ";
                    STR iname; STR " "; pp_list call_vars; NL;
                    igraph#toPretty; NL]);

      let mk_node v = mk_var_node cname v in
      let call_nodes = List.map mk_node call_vars in

      (if !dbg then
         pr__debug [STR "call_nodes = "; pp_list call_nodes; NL]);

      let inodes = igraph#get_ret_and_arg_nodes in

      (if !dbg then
         pr__debug [STR "inodes = "; pp_list inodes; NL]);

      let iedges = igraph#get_edges in
      let pairs =
	try
	  List.combine inodes call_nodes
	with _ ->
	  begin
	    pr_debug [STR "Call does not match signature. "; NL;
		      STR "remove_known_call has lists of different sizes ";
                      cname#toPretty; STR " "; pp_list call_vars; NL;
                      igraph#toPretty; NL;
		      STR "inodes "; pp_list inodes; NL; STR " call_nodes ";
                      pp_list call_nodes; NL];
	    ch_error_log#add "invocation argument mismatch" cname#toPretty;
	    raise (JCH_failure (STR "Call does not match signature."))
	  end in
      let getCNode inode =
	let is_return =
	  match inode#get_node_type with
	  | TN_VAR (_, v, _) -> v#getName#getBaseName = "return"
	  | _ -> false in
	if List.mem_assoc inode pairs then
	  (is_return, List.assq inode pairs)
	else
          (is_return, inode) in
      let add_edge in1 set =
	let (_, cn1) = getCNode in1 in
	let add_e in2 =

	  (if !dbg then
             pr__debug [STR "add_edge "; in1#toPretty; STR " "; in2#toPretty; NL]);

	  let (is_ret, cn2) = getCNode in2 in
	  if not is_ret && cn2#is_immutable && iname <> "<init>" then
	    begin
	      if !dbg then
                pr__debug [STR "cn2 = "; cn2#toPretty;
                           STR " is_arg and is immutable and is not init"; NL]
	    end
	  else self#add_edge cn1 cn2 in
	set#iter add_e  in
      iedges#iter add_edge;

      let add_taint_origins (inode, call_node) =
	let _ = call_node#add_untrusted_origins (inode#get_untrusted_origins) in
	if is_stub then
	  match JCHTNode.set_stub_origins cname pc tnode inode call_node with
	  | Some stub_node -> self#add_edge stub_node call_node
	  | _ -> () in
      List.iter add_taint_origins pairs

    method private record_unknown_call_edges
                     (cproc_name: symbol_t)
                     (call_vars: variable_t list)
                     (iproc_name: symbol_t) =

      (if !dbg then
         pr__debug [STR "record_unknown_call_edges ";
                    cproc_name#toPretty; STR " "; iproc_name#toPretty; NL]);

      (if !dbg then
         pr__debug [STR "call_vars: "; pp_list call_vars; NL]);

      has_calls := true;
      let jproc_info = JCHSystem.jsystem#get_jproc_info cproc_name in
      let mk_node v = mk_var_node cproc_name v in
      let call_nodes = List.map mk_node call_vars in
      let igraph =
	try
	  H.find tgraphs iproc_name#getSeqNumber
	with
	| Not_found ->
	   raise
             (JCH_failure
                (LBLOCK [
                     STR "graph not found for "; iproc_name#toPretty;
		     STR " in JCHTGraphTransformer.record_unknown_call_edges"])) in

      (if !dbg then
         pr__debug [STR "igraph: = "; NL; igraph#toPretty; NL]);

      let inodes = igraph#get_ret_and_arg_nodes in
      let pairs = List.combine inodes call_nodes in
      let get_var inode =
	match inode#get_node_type with
	| TN_VAR (_, v, _) -> v
	| _ ->
           raise
             (JCH_failure
                (STR "record_unknown_call_edges expected variable node ")) in
      let is_return inode =
	let iv = get_var inode in
	iv#getName#getBaseName = "return"in
      let add_edge (inode, call_node) =

	(if !dbg then
           pr__debug [STR "add_edge "; inode#toPretty; STR " ";
                      call_node#toPretty; NL]);

	if is_return inode then self#add_edge inode call_node
	else
	  begin
	    self#add_edge call_node inode;

	    (if !dbg then
               pr__debug [STR "after self#add_edge "; NL]);

	    let is_immutable =

	      (if !dbg then
                 pr__debug [STR "before get_var "; NL]);

	      let cv = get_var call_node in

	      (if !dbg then
                 pr__debug [STR "after get_var "; cv#toPretty; NL]);

	      let vtypes = (jproc_info#get_jvar_info cv)#get_types in

	      (if !dbg then
                 pr__debug [STR "after vtypes "; NL]);

	      JCHTypeUtils.is_immutable_type vtypes in
	    if not is_immutable then
              self#add_edge inode call_node
	  end in
      List.iter add_edge pairs

    method private remove_proc_call tnode cinfo iinfo args pc =

      (if !dbg then
         pr__debug [NL; STR "remove_proc_call "; tnode#toPretty; NL;
                    cinfo#toPretty; NL; iinfo#toPretty; NL;
                    pp_list args; NL]);

      let cproc_name = cinfo#get_procname in
      let iproc_name = iinfo#get_procname in
      if JCHSystem.jsystem#not_analyzed iproc_name#getSeqNumber then

	(if !dbg then
           pr__debug [
               STR "iinfo failed in analysis || does not need to be analyzed ";
               NL])

      else
        self#record_call cproc_name iproc_name args;
      try
	begin
	  let igraph =
	    try
	      H.find stub_tgraphs iproc_name#getSeqNumber
	    with
	    | Not_found ->
	       raise
                 (JCH_failure
                    (LBLOCK [
                         STR "graph for "; iproc_name#toPretty;
			 STR " not found in JCHTGraphTransformer.remove_proc_call"])) in
	  if procs_with_calls#has iproc_name then
	    begin
	      (if !dbg then
                pr__debug [STR "the called graph has calls cproc_name: ";
                           cproc_name#toPretty; STR " iproc_name: ";
                           iproc_name#toPretty; NL;
                           igraph#toPretty; NL]);

	      self#record_unknown_call_edges
                cproc_name tnode#get_call_vars iproc_name
	    end
	  else
	    begin

	      (if !dbg then
                 pr__debug [STR "called method has stub: ";
                            igraph#toPretty; NL]);
	      !new_fields#addSet igraph#get_fields;
	      let iname = (iinfo#get_class_method_signature)#name in
	      try
		self#remove_known_call
                  tnode false cproc_name iname tnode#get_call_vars igraph pc;
		removed#add tnode
	      with _ ->
		self#remove_unknown_call
                  iinfo (edges#get tnode)
                  "method not analyzed"
                  cproc_name
                  pc (* in case that method was not analyzed *)
	    end
	end
      with _ ->
	begin

	  (if !dbg then
             pr__debug [STR "no stub for the called method"; NL]);

	  if JCHSystem.jsystem#not_analyzed iproc_name#getSeqNumber then
	    begin
	      self#remove_unknown_call
                iinfo (edges#get tnode) "missing stub" cproc_name pc
	    end
	  else
	    self#record_unknown_call_edges
              cproc_name tnode#get_call_vars iproc_name
	end

    method private remove_stub_call tnode cinfo iinfo args pc =

      (if !dbg then
         pr__debug [STR "remove_stub_call "; tnode#toPretty; NL;
		    STR "    "; pp_list args; NL;
		    STR "cinfo = "; cinfo#toPretty; NL;
		    STR "iinfo = "; iinfo#toPretty; NL]);

      let cproc_name = cinfo#get_procname in
      let iproc_name = iinfo#get_procname in
      let icmsig = iinfo#get_class_method_signature in
      let iname = icmsig#name in

      (if !dbg then
         pr__debug [STR "before get_lib_stub "; NL]);

      let lgraph = JCHTGraphStubs.get_lib_stub iproc_name icmsig in

      (if !dbg then
         pr__debug [STR "lgraph = "; NL; lgraph#toPretty; NL]);

      try
	self#remove_known_call
          tnode true cproc_name iname tnode#get_call_vars lgraph pc;
	removed#add tnode;
      with _ ->
	self#remove_unknown_call
          iinfo (edges#get tnode) "remove known call failed" cproc_name pc

    method private remove_call tnode =
      match tnode#get_node_type with
      |	TN_CALL (_,pc, callerix, tgtix, _, args) ->
         let tinfo = app#get_method (retrieve_cms tgtix) in
         let cinfo = app#get_method (retrieve_cms callerix) in
	  begin
	    match tinfo#get_implementation with
	    | ConcreteMethod m ->

	       (if !dbg then
                  pr__debug [implementation_to_pretty m#get_implementation]);

	       self#remove_proc_call tnode cinfo tinfo args pc;

	       (if !dbg then
                  pr__debug [STR "finished remove_proc_call"; NL;
                             !new_edges#toPretty; NL])

	    | JCHPreAPI.Stub _ ->
	       self#remove_stub_call tnode cinfo tinfo args pc;

	       (if !dbg then
                  pr__debug [STR "finished remove_stub_call"; NL;
                             !new_edges#toPretty; NL])

	    | _ ->
               raise
                 (JCH_failure (STR "encountered method neither concrete nor stub "))
	  end

      |	TN_UNKNOWN_CALL (_, _pc, _cinfo, _, _args) ->
	  begin
	    match (edges#get tnode, rev_edges#get tnode) with
	    | (Some succs, Some preds) ->
		List.iter2 self#add_edge preds#toList succs#toList
	    | _ -> ()
	  end
      |	_ ->
	  ()

    method add_some_edges n set =

      (if !dbg then
         pr__debug [STR "add_some_edges "; n#toPretty; STR " "; set#toPretty; NL]);

      if removed#has n then
        ()
      else
	let not_removed m = not (removed#has m) in
	let nodes = List.filter not_removed set#toList in
	List.iter (self#add_edge n) nodes

    method !transform =
      new_sig_nodes := sig_nodes;
      !new_fields#addSet fields;
      calls#iter self#remove_call;

      (if !dbg then
         pr__debug [STR "after remove_call"; NL; !new_edges#toPretty; NL]);

      edges#iter self#add_some_edges;

      (if !dbg then
         pr__debug [STR "after add_some_edges"; NL; !new_edges#toPretty; NL]);
  end

class prune_var_transformer_t (tgraph: taint_graph_t) =
object (self: 'a)
  inherit tgraph_transformer_t tgraph

(* collects reachable nodes but stops at call vars and fields
 * it is not clear what type of dependency it is until
 * the summary of the call is available *)
  method private get_reachables
                   forward (node: taint_node_int) : TaintNodeCollections.set_t =
    let reachable = new TaintNodeCollections.set_t in
    let rec work start ns  =
      match ns with
      | n :: rest_ns ->

	 (if !dbg then
            pr__debug [STR "prune_var_transformer get_reachable work ";
                       n#toPretty; NL]);

	 if reachable#has n then
	   work false rest_ns
	 else
	   begin
	     reachable#add n;
	     if not start && (call_nodes#has n) then
	       work false rest_ns
	     else
	       let table = if forward then edges else rev_edges in
	       match table#get n with
	       | Some set ->
		  work false (List.rev_append (rest_ns) (set#toList))
	       | None ->
		  work false rest_ns
	   end
      | [] ->
	 () in
    begin
      work true [node];
      reachable#remove node;
      reachable
    end

(* Prunes vars that are discovered to be not tainted
 * and vars that are intermediary
 * Does not prune vars in a call, fields, calls and vars from other methods
 * Prunes vars that are not reachable from any of the above *)
  method !transform =

    (if !dbg then
       pr__debug [STR "prune_vars "; NL]);

    let add_es forward n =
      let reach = self#get_reachables forward n in
      let keep m =
	match m#get_node_type with
	| TN_FIELD _ | TN_CALL _ -> true
	| TN_VAR (cmsix, _v, _) ->
           cmsix = proc_name#getIndex || (List.mem m sig_nodes) || call_nodes#has m
	| _ -> false in
      let kreach = List.filter keep reach#toList in
      let add n m = if forward then self#add_edge n m else self#add_edge m n in
      List.iter (add n) kreach in
    List.iter (add_es true) (sig_nodes @ fields#toList);
    begin
      match return_node_opt with
      | Some return -> add_es false return
      | None -> ()
    end;
    new_sig_nodes := sig_nodes;
    fields#iter (add_es true);
    call_nodes#iter (add_es true);
    calls#iter (add_es true);
    new_fields := fields;
    new_call_nodes := call_nodes;
    new_calls := calls

end


class graph_env_maker_t tgraph env_graph =
  object (self: 'a)
    inherit tgraph_transformer_t tgraph as super

    val name = tgraph#get_proc_name

    method private  add_rev_env_edge (wn: taint_node_int) (env_n: taint_node_int) =
      super#add_edge env_n wn;
      let _ = wn#add_untrusted_origins (env_n#get_untrusted_origins) in
      ()

    method private add_env_edges n =
      match env_graph#get_rev_edges#get n with
      |	Some set ->
	  set#iter (self#add_rev_env_edge n)
      |	None ->
	  ()

    method !transform =
      let add_edges n set =
	set#iter (super#add_edge n) in
      begin
        new_sig_nodes := sig_nodes;
        !new_fields#addSet tgraph#get_fields;
        !new_call_nodes#addSet tgraph#get_call_nodes;
        !new_calls#addSet tgraph#get_calls;
        edges#iter add_edges;
        List.iter self#add_env_edges arg_nodes;
      end
  end


(* Propagates taint on the given local tgraph *)
class taint_propagator_t (tgraph:  taint_graph_t) =
  object (self: 'a)

    val edges = tgraph#get_edges
    val rev_edges = tgraph#get_rev_edges

     (* propagates the taint of one node *)
    method private propagate_taint (node : taint_node_int) =

      let _ =
        if !dbg then
          pr__debug [STR "propagate_taint "; STR " "; node#toPretty; NL] in

      let get_next_nodes n =
	if n#is_loop_counter_var || n#is_conditional then
          []
	else
	  begin
	    match edges#get n with
	    | Some set ->
		let ns = ref [] in
		let add_node n' =
		  if n#propagate_taint n' then ns := n' :: !ns in
                begin
		  set#iter add_node;
		  !ns
                end
	    | _ -> []
	  end in

      let rec work ns  =
	match ns with
	| n :: rest_ns ->

           (if !dbg then
              pr__debug [
                  STR "taint_propagator get_reachable work "; n#toPretty; NL]);

	    let new_nodes = get_next_nodes n in
	    work (List.rev_append (rest_ns) new_nodes)
	| [] -> () in
      work [node]

    method transform =
      let nodes = edges#listOfKeys in
      List.iter self#propagate_taint nodes;
      (* values are tainted first so we can taint the bounds of the
       * loop counter before the taint on bounds is propagated *)

  end


(* Makes a skeleton call graph.
 * In case the method could be invoked by library methods,
 * the inputs might be tainted in these calls, so tainted nodes are
 * added as inputs here *)
let init_calls_graph tgraph =
  let new_tgraph = (new tgraph_transformer_t tgraph)#make_tgraph in
  new_tgraph

let make_stub tgraph =
  let transformer = (new stub_transformer_t tgraph) in
  let tgraph = transformer#make_tgraph in
  let field_edges = transformer#get_field_edges in
  (tgraph, field_edges)

let remove_calls
      tgraph tgraphs calls_tgraphs stub_tgraphs procs_with_calls =
  let transformer =
    new call_remover_t
        tgraph tgraphs calls_tgraphs stub_tgraphs procs_with_calls in
  let tgraph = transformer#make_tgraph in
  let has_calls = transformer#has_calls in
  (tgraph, has_calls)

let prune_vars tgraph =
  let p =
    (new prune_var_transformer_t tgraph)#make_tgraph in

  (if !dbg then
     pr__debug [STR "p = "; NL; p#toPretty; NL]);
  p

let make_env tgraph env_graph =
  (new graph_env_maker_t tgraph env_graph)#make_tgraph

let propagate_taint tgraph =
  (new taint_propagator_t tgraph)#transform

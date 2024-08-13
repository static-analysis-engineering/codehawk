(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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
open CHUtils
open CHLanguage
open CHOnlineCodeSet

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes

(* jchpre *)
open JCHPreAPI

module LF = LanguageFactory


let symbol_to_pretty s   = STR s#getBaseName

let initboundlabel s = new symbol_t (s#getBaseName ^ "_initbound")

let exitguardlabel s = new symbol_t (s#getBaseName ^ "_exitguard")

let intraguardlabel s = new symbol_t (s#getBaseName ^ "_intraguard")

let loopexitlabel s = new symbol_t (s#getBaseName ^ "_loopexit")

let sinknodelabel p n = new symbol_t (p#getBaseName ^ "_sink_" ^ n#getBaseName)


class cmd_list_t (l: (code_int, cfg_int) command_t list):cmd_list_int =
object

  val mutable cmds = l

  method cmd_list = cmds
  method reverse_cmds = cmds <- List.rev cmds

  method toPretty = pretty_print_list cmds (command_to_pretty 0) "{" ":" "}"
end


class code_graph_t:code_graph_int =
object (self)

  val nodes = new SymbolCollections.table_t
  val out_n = new SymbolCollections.table_t
  val in_n  = new SymbolCollections.table_t

  val predreplacements = new SymbolCollections.table_t

  method private probe (s:symbol_t) =
    if nodes#has s then () else
      begin
	nodes#set s (new cmd_list_t []);
	out_n#set s (new SymbolCollections.set_t);
	in_n#set s (new SymbolCollections.set_t)
      end

  method add_node (s:symbol_t) (c:cmd_t list) =
    begin self#probe s; self#set_cmd s c end

  method private add_predreplacement (s1:symbol_t) (s2:symbol_t) =
    predreplacements#set s1 s2

  method private get_predreplacement (s:symbol_t) =
    match predreplacements#get s with
    | Some p -> p
    | _ -> s

  method add_edge (src:symbol_t) (tgt:symbol_t) =
    begin
      self#probe src;
      self#probe tgt;
      (self#get_out_edges src)#add tgt;
      (self#get_in_edges tgt)#add src
    end

  method get_cmds (s:symbol_t) =
    match nodes#get s with
    | Some c -> c
    | _ ->
      begin
	ch_error_log#add "invocation error"
	  (LBLOCK [STR "code_graph#get_cmds: "; symbol_to_pretty s]);
	raise (JCH_failure (LBLOCK [STR "code_graph#get_cmds"]))
      end

  method private get_out_edges (s:symbol_t) =
    match out_n#get s with
    | Some s -> s
    | _ ->
      begin
	ch_error_log#add "invocation error"
	  (LBLOCK [STR "code_graph#get_out_edges: "; symbol_to_pretty s]);
	raise (JCH_failure (LBLOCK [STR "code_graph#get_out_edges"]))
      end

  method private get_in_edges (s:symbol_t) =
    match in_n#get s with
    | Some s -> s
    | _ ->
      begin
	ch_error_log#add "invocation error"
	  (LBLOCK [STR "code_graph#get_in_edges: "; symbol_to_pretty s]);
	raise (JCH_failure (LBLOCK [STR "code_graph#get_in_edges"]))
      end

  method set_cmd (s:symbol_t) (c:cmd_t list) =
    begin
      self#probe s;
      match nodes#get s with
      | Some _ -> nodes#set s (new cmd_list_t c)
      | _ ->
	begin
	  ch_error_log#add "internal error"
	    (LBLOCK [STR "code_graph#set_cmd"]);
	  raise (JCH_failure (LBLOCK [STR  "code_graph#set_cmd"]))
	end
    end

  method remove_edge (src:symbol_t) (tgt:symbol_t) =
    match (in_n#get tgt, out_n#get src) with
    | (Some i, Some o) -> begin i#remove src; o#remove tgt end
    | _ -> ()

  method loopbound_transform
    ~(node:symbol_t)
    ~(nodecmds:cmd_t list)
    ~(initsrcs:symbol_t list)
    ~(intratgts:symbol_t list)
    ~(exittgts:symbol_t list)
    ~(initcmds:cmd_t list)
    ~(intracmds:cmd_t list)
    ~(exitcmds:cmd_t list) =
    if nodes#has node then
      let initbound = initboundlabel node in
      let exitguard = exitguardlabel node in
      let intraguard = intraguardlabel node in
      begin
	self#set_cmd node ((self#get_cmds node)#cmd_list @ nodecmds);
	self#add_node initbound initcmds;
	self#add_node exitguard exitcmds;
	self#add_node intraguard intracmds;
	List.iter (fun initsrc -> self#remove_edge initsrc node) initsrcs;
	List.iter (fun exittgt -> self#remove_edge node exittgt) exittgts;
	List.iter (fun intratgt -> self#remove_edge node intratgt) intratgts;
	List.iter (fun initsrc -> self#add_edge initsrc initbound) initsrcs;
	List.iter (fun exittgt -> self#add_edge exitguard exittgt) exittgts;
	List.iter (fun intratgt -> self#add_edge intraguard intratgt) intratgts;
	self#add_edge initbound node;
	self#add_edge node exitguard;
	self#add_edge node intraguard
      end

  method loopcut_transform
    ~(node:symbol_t)
    ~(xcmds:cmd_t list)
    ~(intrasrcs:symbol_t list)
    ~(exittgts:symbol_t list) =
    if nodes#has node then
      let loopexit = loopexitlabel node in
      begin
	self#add_node loopexit xcmds;
	self#add_predreplacement node loopexit;
	List.iter (fun intrasrc -> self#remove_edge intrasrc node) intrasrcs;
	List.iter (fun exittgt -> self#remove_edge node exittgt) exittgts;
	List.iter (fun intrasrc -> self#add_edge intrasrc loopexit) intrasrcs;
	List.iter (fun exittgt -> self#add_edge loopexit exittgt) exittgts
      end

  method sink_transform
    ~(node:symbol_t)
    ~(preds: (symbol_t * cmd_t list) list) =
    if nodes#has node then
      List.iter (fun (p,cmds) ->
	let p = self#get_predreplacement p in
	let sinknode = sinknodelabel p node in
	begin
	  self#add_node sinknode cmds;
	  self#remove_edge p node;
	  self#add_edge p sinknode;
	  self#add_edge sinknode node
	end) preds

  method to_cfg (entry:symbol_t) (exit:symbol_t):cfg_int =
    let states = new SymbolCollections.table_t in
    let _ = nodes#iter
      (fun label commands ->
	let in_edges = self#get_in_edges label in
	let out_edges = self#get_out_edges label in
	let state = LF.mkState label (LF.mkCode commands#cmd_list) in
	let _ = out_edges#iter (fun o -> state#addOutgoingEdge o) in
	let _ = in_edges#iter (fun i -> state#addIncomingEdge i) in
	states#set label state) in
    let (entryState, exitState) =
      match (states#get entry, states#get exit) with
      | (Some entryState, Some exitState) -> (entryState, exitState)
      | _ ->
	begin
	  ch_error_log#add "invalid argument"
	    (LBLOCK [STR "code_graph#to_cfg lacks an entry or exit node"]);
	  raise (Invalid_argument "code_graph#to_cfg")
	end in
    let cfg = LF.mkCFG entryState exitState in
    let _ = states#iter (fun _ s -> cfg#addState s) in
    cfg

end

let make_code_graph () = new code_graph_t

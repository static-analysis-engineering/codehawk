(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Arnaud Venet and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

module LF = LanguageFactory

class cmd_list_t (l: (code_int, cfg_int) command_t list):cmd_list_int =
object (self: _)

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

  method private probe (s:symbol_t) =
    if nodes#has s then () else
      begin
	nodes#set s (new cmd_list_t []) ;
	out_n#set s (new SymbolCollections.set_t) ;
	in_n#set  s (new SymbolCollections.set_t)
      end

  method add_node (s:symbol_t) (c:cmd_t list) =
    begin self#probe s ; self#set_cmd s c end

  method add_edge (src:symbol_t) (tgt:symbol_t) =
    begin
      self#probe src ;
      self#probe tgt ; 
      (self#get_out_edges src)#add tgt ;
      (self#get_in_edges tgt)#add src
    end

  method get_cmds (s:symbol_t) =
    match nodes#get s with
	Some c -> c
      | _ ->
	begin
	  ch_error_log#add
            "invocation error"
            (LBLOCK [ STR "code_graph#get_cmds: " ; symbol_to_pretty s ]) ;
	  raise (Invocation_error "code_graph#get_cmds")
	end

  method private get_out_edges (s:symbol_t) =
    match out_n#get s with
	Some s -> s
      | _ ->
	begin
	  ch_error_log#add
            "invocation error"
            (LBLOCK [ STR "code_graph#get_out_edges: " ; symbol_to_pretty s ]) ;
	  raise (Invocation_error "code_graph#get_out_edges")
	end

  method private get_in_edges (s:symbol_t) =
    match in_n#get s with
	Some s -> s
      | _ ->
	begin
	  ch_error_log#add
            "invocation error"
            (LBLOCK [ STR "code_graph#get_in_edges: " ; symbol_to_pretty s ]) ;
	  raise (Invocation_error "code_graph#get_in_edges")
	end

  method set_cmd (s:symbol_t) (c:cmd_t list) =
    begin
      self#probe s ;
      match nodes#get s with
	  Some _ -> nodes#set s (new cmd_list_t c)
	| _ ->
	  begin
	    ch_error_log#add
              "internal error" (LBLOCK [ STR "code_graph#set_cmd" ]) ;
	    raise (Internal_error "code_graph#set_cmd")
	  end
    end

  method remove_edge (src:symbol_t) (tgt:symbol_t) =
    match (in_n#get tgt, out_n#get src) with
	(Some i, Some o) -> begin i#remove src ; o#remove tgt end
      | _ -> ()
	
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
	  (Some entryState, Some exitState) -> (entryState, exitState)
	| _ ->
	  begin
	    ch_error_log#add "invalid argument" 
	      (LBLOCK [ STR "code_graph#to_cfg lacks an entry or exit node" ]) ;
	    raise (Invalid_argument "code_graph#to_cfg")
	  end in
    let cfg = LF.mkCFG entryState exitState in
    let _ = states#iter (fun _ s -> cfg#addState s) in
    cfg
      
end

let make_code_graph () = new code_graph_t

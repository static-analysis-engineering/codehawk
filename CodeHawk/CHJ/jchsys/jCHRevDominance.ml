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
open CHNumerical
open CHPretty
open CHSCC
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHIFSystem

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

module F = CHOnlineCodeSet.LanguageFactory

class rev_dominance_info_t
        (proc_name:symbol_t) (cfg:cfg_int) (wto:wto_t) = 
  object (self: _) 
      
    val state_to_rep = new SymbolCollections.table_t 
    val rev_cfg = F.mkCFG_s method_exit_sym method_entry_sym 
    val loops = new SymbolCollections.set_t
    val rev_dominance_info = ref None
    val cms = retrieve_cms proc_name#getSeqNumber

    method private mk_code (cmds:(code_int,cfg_int) command_t  list) =
      chif_system#make_code cms cmds

    method private mk_rep (state_name:symbol_t) = 
      let rep_state = F.mkState state_name 
	  (self#mk_code []) in
      rev_cfg#addState rep_state ;
      rep_state

    method private get_rep (state_name: symbol_t) =
	(Option.get (state_to_rep#get state_name))#getLabel 

    (* sets of the state of all the states to rep *)
    method private set_state_to_rep (wto:wto_t) (rep:state_int) =
      match wto with 
      |	(CHSCC.VERTEX s) :: rest_wto -> 
	  state_to_rep#set s rep ;
	  self#set_state_to_rep rest_wto rep 
      |	(CHSCC.SCC inner_wto) :: rest_wto -> 
	  self#set_state_to_rep inner_wto rep ;
	  self#set_state_to_rep rest_wto rep 
      |	[] -> ()

    method private find_state_reps (wto:wto_t) = 
      match wto with 
      |	(CHSCC.VERTEX s) :: rest_wto -> 
	  state_to_rep#set s (self#mk_rep s) ;
	  self#find_state_reps rest_wto 
      |	(CHSCC.SCC inner_wto) :: rest_wto -> 
	  let rep = 
	    match inner_wto with 
	    | CHSCC.VERTEX st :: _ -> 
		loops#add st ;
		self#mk_rep st
	    | _ -> 
		raise (JCH_failure (STR "expected head of SCC.")) in
	  self#set_state_to_rep inner_wto rep ;
	  self#find_state_reps rest_wto 
      |	[] -> ()

    method private find_other_state_reps (cfg: cfg_int) =  
      let mk_other_rep s = 
	match state_to_rep#get s with 
	| Some s -> ()
	| None -> 
	    if s#getBaseName.[0] = 'l' then (* loop_counter_init *)
	      let state = cfg#getState s in
	      let next = List.hd state#getOutgoingEdges in
	      state_to_rep#set s (rev_cfg#getState (self#get_rep next))
	    else (* method-entry *)
	      state_to_rep#set s (self#mk_rep s) in
      List.iter mk_other_rep cfg#getStates 

    method private add_edges = 
      let addStateEdges (state_name:symbol_t) = 
	let state = cfg#getState state_name in 
	let incoming = state#getIncomingEdges in 
	let rep = 
	  if state_name#getBaseName = "exceptional-exit" then
            (* We skip over the exceptional exit, as it is dealt with 
             * differently in jCHDominance and we do not need it anyway *)            
	    self#get_rep method_exit_sym   
	  else 
	    self#get_rep state_name in
	let incoming_reps = 
	  List.rev_map self#get_rep incoming in
	let add_edge (r:symbol_t) = 
	  if r = rep then
            ()
	  else 
	    rev_cfg#addEdge rep r in
	List.iter add_edge incoming_reps in 
      List.iter addStateEdges cfg#getStates 

    method private add_terminal_edges = 
      let reps = rev_cfg#getStates in
      let add_terminal_edge rep = 
	if rep = method_exit_sym then
          ()
	else 
	  let rep_state = rev_cfg#getState rep in
	  if rep_state#getIncomingEdges = [] then 
	    rev_cfg#addEdge method_exit_sym rep 
	  else 
	    () in
      List.iter add_terminal_edge reps

    initializer
      self#find_state_reps wto ;
      self#find_other_state_reps cfg ;
      self#add_edges ;
      self#add_terminal_edges ;
      let rev_dom = new JCHDominance.dominance_info_t rev_cfg in
      let _ = rev_dom#find_dominator_tree in
      rev_dominance_info := Some rev_dom ;

    method find_rev_common_dominator (states:symbol_t list) = 
      let dom_info = Option.get !rev_dominance_info in
      let rec find_rev_cd sts = 
	let st_reps = List.rev_map self#get_rep sts in
	let reps = dom_info#find_common_dominator st_reps in
	let find_dom_states rep = 
	  let rep_state = rev_cfg#getState rep in
	  if loops#has rep then 
	    find_rev_cd rep_state#getIncomingEdges 
	  else 
	    [rep] in
	List.flatten (List.rev_map find_dom_states reps) in
      find_rev_cd states 
      
  end
	     
      
      

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

(* chutil *)
open CHUtils
open CHPrettyUtil

module H = Hashtbl
module LF = CHOnlineCodeSet.LanguageFactory

let make_label pc = new symbol_t (string_of_int pc)

let loophead_to_incoming = ref (new IntCollections.table_t)

let remove_loops
      (cost_chif:procedure_int)
      (loopstructure: CHLoopStructure.loop_structure_int):procedure_int =
  loophead_to_incoming := new IntCollections.table_t ;
  let cfg =
    match cost_chif#getBody#getCmdAt 0 with
    | CFG (_, cfg) -> cfg
    | _ -> raise (JCHBasicTypes.JCH_failure (STR "expected CFG")) in

  let transform_state (state_name:  symbol_t) : state_int =
    let state = cfg#getState state_name in
    let get_loophead =
      try
	let pc = int_of_string state_name#getBaseName in
	if loopstructure#is_loophead pc then Some pc
	else None
      with _ -> None in
    match get_loophead with
    | Some hpc ->
	let new_state = LF.mkState state_name state#getCode in
	let loop_edges = ref [] in
	let is_not_inloop s =
	  try
	    let pc = int_of_string s#getBaseName in
	    if loopstructure#is_inloop_with_loophead pc hpc then
	      begin
		loop_edges := s :: !loop_edges ;
		false
	      end
	    else true
	  with _ -> true in
	let new_incoming_edges =
          List.filter is_not_inloop state#getIncomingEdges in
	
	!loophead_to_incoming#set hpc (SymbolCollections.set_of_list !loop_edges);      
	List.iter new_state#addIncomingEdge new_incoming_edges ;
	new_state
    | _ ->
	let new_state = LF.mkState state_name state#getCode in
	List.iter new_state#addIncomingEdge state#getIncomingEdges ;
	new_state in
	
  let states = List.map transform_state cfg#getStates in
  let add_out (state: state_int) (state'_name: symbol_t) =
    let state' : state_int =
      List.find (fun s -> s#getLabel#equal state'_name) states in
    state'#addOutgoingEdge state#getLabel in
  List.iter (fun state ->
      List.iter (add_out state) state#getIncomingEdges) states ;
  
  let new_cfg = LF.mkCFG cfg#getEntry cfg#getExit in
  new_cfg#addStates states ;
  
  let new_body = LF.mkCode [CFG (cost_chif#getName, new_cfg)] in
  LF.mkProcedure
    cost_chif#getName
    ~signature:[]
    ~bindings:[]
    ~scope:cost_chif#getScope
    ~body:new_body

    
let reduce_to_loop
      (cost_chif: procedure_int)
      (cvar: variable_t)
      (bvar: variable_t)
      (hpc: int)
      (pcs: int list) : procedure_int =
  let cfg =
    match cost_chif#getBody#getCmdAt 0 with
    | CFG (_, cfg) -> cfg
    | _ -> raise (JCHBasicTypes.JCH_failure (STR "expected CFG")) in
  let loop_scope = cost_chif#getScope in

  let entry_name = new symbol_t "entry" in
  let exit_name = new symbol_t "exit" in
  let loop_state_name = make_label hpc in
    
  let initassign =
    OPERATION ({op_name = new symbol_t ~atts:["0"] "set_to_0" ;
		 op_args = [("dst", cvar, WRITE)] }) in
    
  let invop =
    OPERATION ( { op_name = new symbol_t ~atts:["methodexit"] "invariant" ; 
		  op_args = [("cvar", cvar, READ_WRITE)] }) in

    let entry_state = LF.mkState entry_name (LF.mkCode [initassign]) in
    let exit_state = LF.mkState exit_name (LF.mkCode [invop]) in

    let loop_cfg = LF.mkCFG entry_state exit_state in
    
    let is_in_pcs s =
      let pc = int_of_string s#getBaseName in
      List.mem pc pcs in

    let rec work first state_names new_state_names =
      match new_state_names with
      | new_state_name :: rest_new_state_names ->
	  if List.mem new_state_name#getBaseName state_names then
	    begin
	      work false state_names rest_new_state_names
	    end
	  else
	    begin
	      let state = cfg#getState new_state_name in
	      let new_state = LF.mkState new_state_name state#getCode in
	      loop_cfg#addState new_state ;

	      let new_ins =
		if first then
		  match !loophead_to_incoming#get hpc with
		  | Some set -> set#toList
		  | _ -> [] 
		else
		  begin
		    List.filter is_in_pcs state#getIncomingEdges 
		  end in
	      
	      if first then
		begin
		  List.iter (fun s -> exit_state#addIncomingEdge s) new_ins ;
		  new_state#addIncomingEdge entry_name
		end
	      else
		List.iter (fun s -> new_state#addIncomingEdge s) new_ins;
	      
	      work false (new_state_name#getBaseName :: state_names)
		(List.rev_append rest_new_state_names new_ins) ;
	    end
      | [] -> () in
    work
      true [entry_name#getBaseName; exit_name#getBaseName] [loop_state_name] ;

    let add_out_edges new_state_name =
      let new_state = loop_cfg#getState new_state_name in
      let add_out_edge s =
	let new_s = loop_cfg#getState s in
	new_s#addOutgoingEdge new_state_name in
      List.iter add_out_edge new_state#getIncomingEdges in
    List.iter add_out_edges loop_cfg#getStates;
    
    let loop_procname =
      new symbol_t (cost_chif#getName#getBaseName^"_loop_"^(string_of_int hpc)) in
    let loop_body = LF.mkCode [CFG (loop_procname, loop_cfg)] in
    LF.mkProcedure
      loop_procname
      ~signature:[]
      ~bindings:[]
      ~scope:loop_scope
      ~body:loop_body
    

let remove_dead_end_states
      (cost_chif: procedure_int)
      (loopstructure: CHLoopStructure.loop_structure_int) = 
  let not_in_loop state_name =
    try
      let pc = int_of_string state_name#getBaseName in
	
      not (loopstructure#is_inloop pc)
      || (loopstructure#is_loophead pc) && (loopstructure#get_nesting_level pc = 1)
    with _ -> true in

  let cfg =
    match cost_chif#getBody#getCmdAt 0 with
    | CFG (_, cfg) -> cfg
    | _ -> raise (JCHBasicTypes.JCH_failure (STR "expected CFG")) in
  let states_not_in_loops = List.filter not_in_loop cfg#getStates in

  let new_states = ref [] in
  let new_state_names = ref [] in

  let rec work state_names =
    match state_names with
    | state_name :: rest_state_names ->
	let state_name_str = state_name#getBaseName in
	if List.mem state_name_str !new_state_names then work rest_state_names
	else
	  begin
	    let state = cfg#getState state_name in
	    let new_state = LF.mkState state_name state#getCode in
	    new_states := new_state :: !new_states ;
	    new_state_names := state_name_str :: !new_state_names ;
	    let ins = state#getIncomingEdges in
	    List.iter (fun s -> new_state#addIncomingEdge s) ins;
	    work (List.rev_append rest_state_names ins)
	  end
    | _ -> () in
  work states_not_in_loops ;

  
  let add_out (state: state_int) (state'_name: symbol_t) =
    let state':state_int =
      List.find (fun s -> s#getLabel#equal state'_name) !new_states in
    state'#addOutgoingEdge state#getLabel in
  List.iter
    (fun state -> List.iter (add_out state) state#getIncomingEdges) !new_states ;
  
  let new_cfg = LF.mkCFG cfg#getEntry cfg#getExit in
  new_cfg#addStates !new_states ;
  
  let new_body = LF.mkCode [CFG (cost_chif#getName, new_cfg)] in
  LF.mkProcedure
    cost_chif#getName
    ~signature:[]
    ~bindings:[]
    ~scope:cost_chif#getScope
    ~body:new_body

	

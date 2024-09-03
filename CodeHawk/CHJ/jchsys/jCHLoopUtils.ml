(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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
open CHSCC
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHIFSystem
open JCHPreAPI

(* jchsys *)
open JCHPrintUtils

module H = Hashtbl

let dbg = ref false
let wto_index = ref (-1)


(* Information about wtos that is collected from the original CFG
 * the exit info could get lost when simplifying the CHIF *)
class wto_info_t
    ~(is_proc_wto: bool)
    ~(name: symbol_t)
    ~(wto: wto_component_t)
    (* conditional states in the wto that can lead to a loop exit *)
    ~(conds: symbol_t list)
    (* states outside the wto that are loop exits *)
    ~(exit_conds: symbol_t list)
    ~(proc: procedure_int)
    ~(cfg: cfg_int)
    ~(proc_wto: wto_component_t list) =
  object (self: 'a)

    val proc_name = proc#getName
    val method_info = app#get_method (retrieve_cms proc#getName#getSeqNumber)
    val inner_loops : 'a list ref = ref []
    (* list of outer loops from the inner one to the outer one *)
    val outer_loops : 'a list ref = ref []
    val index =
      incr wto_index ;
      !wto_index
    val var_name = new symbol_t ~seqnr: !wto_index "lc"
    val var =
      let name = new symbol_t ~seqnr: !wto_index "lc" in
      new variable_t name NUM_VAR_TYPE
    val entry_pc = ref (-1)
    val first_pc = ref (-1)
    val last_pc = ref (-1)

    (* pcs in the loop from where there is a jump, etc. to the entry_pc *)
    val entry_incoming_pcs = ref []
    val last_in_entry_state = ref (-1)
    val instr_count = ref 0
    val call_pcs = ref []
    val cond_pcs =
      List.map JCHSystemUtils.sym_to_pc conds

    val max_iterations : jterm_t list ref = ref []
    val unreachable = ref false

    (* all catch blocks in the method *)
    val all_catch_blocks:handler_block_int list ref = ref []

    (* starts of catch blocks that include the loop *)
    val catch_block_starts : int list ref = ref []

    method private find_catch_blocks_that_contain pc =
      let includes_pc pc handler_block =
	pc >= handler_block#get_start_pc && pc <= handler_block#get_end_pc in
      List.map (fun cb ->
          cb#get_start_pc) (List.filter (includes_pc pc) !all_catch_blocks)

    initializer
      if is_proc_wto then
        ()
      else
	begin
	  let (epc, fpc, lpc, pcs, lpc') = self#get_entry_first_last in
	  entry_pc := epc ;
	  first_pc := fpc ;
	  last_pc := lpc ;
	  entry_incoming_pcs := pcs ;
	  last_in_entry_state := lpc';
	  self#set_inloop_calls();
	  let method_info =
            app#get_method (retrieve_cms proc#getName#getSeqNumber) in
	  let exception_handlers = method_info#get_exception_handlers in
	  all_catch_blocks := exception_handlers#get_handler_blocks ;
	  catch_block_starts := self#find_catch_blocks_that_contain  !first_pc
	end

    method set_max_iterations (jterms:jterm_t list) =
      max_iterations := jterms

    method set_unreachable = unreachable := true

    method get_name = name
    method get_wto = wto
    method get_inner_loops = !inner_loops
    method get_conds = conds
    method get_cond_pcs = cond_pcs
    method get_exit_conds = exit_conds
    method get_outer_loops = !outer_loops
    method get_index = index
    method get_var_name = var_name
    method get_var = var
    method get_proc_wto = proc_wto
    method get_entry_pc = !entry_pc
    method get_first_pc = !first_pc
    method get_last_pc = !last_pc
    method get_entry_incoming_pcs = !entry_incoming_pcs
    method get_last_in_entry_state = !last_in_entry_state
    method get_max_iterations = !max_iterations
    method is_unreachable = !unreachable
    method is_top = !outer_loops = []

    method add_inner_loop (inner_loop: 'a) =
      inner_loops := inner_loop :: !inner_loops

    method set_outer_loops (outer_wtos : 'a list) =
      outer_loops := outer_wtos

    (* Checks wether s is a state in the wto *)
    method has_state (s:symbol_t) =
      let rec hasLp ws =
	match ws with
	| (SCC inner_ws) :: rest_ws ->
	    ((hasLp inner_ws) || (hasLp rest_ws))
	| (VERTEX st) :: rest_ws ->
	    if st#equal s then
	      true
	    else
	      hasLp rest_ws
	| [] -> false in
      hasLp [wto]

    (* Returns the entry, first and last pc in a loop *)
    method private get_entry_first_last =
      let entry = ref true in
      let entry_pc = ref (-1) in
      let entry_incoming_sts = ref [] in
      let is_entry_incoming_st state_name =
	List.exists state_name#equal !entry_incoming_sts in
      let entry_incoming_pcs = ref [] in
      let rec get_pcs_rec (first_opt, last) ws =
	match ws with
	| (SCC inner_ws) :: rest_ws ->
	    get_pcs_rec (get_pcs_rec (first_opt, last) inner_ws) rest_ws
	| (VERTEX st_name) :: rest_ws ->
	    let state = cfg#getState st_name in
	    let (st_first_opt, st_last) =
              JCHSystemUtils.get_first_and_last_in_state method_info state in
	    let new_first =
	      match (first_opt, st_first_opt) with
	      |	(Some first, Some st_first) ->
              (* In the case of wto = (... (... pc=5-then) pc=5-else) it will get pc=5-else *)
		 if st_first < first then
                   Some st_first
		 else
                   Some first
	      |	(Some first, None) ->
		  Some first
	      |	(None, Some st_first) -> Some st_first
	      |	_ -> None in
	    let new_last =
	      if st_last >= last then st_last
	      else last in
	    if !entry then
	      begin
		entry_pc := Option.get st_first_opt ;
		entry := false ;
		entry_incoming_sts := state#getIncomingEdges ;
		last_in_entry_state := st_last
	      end ;
	    if is_entry_incoming_st st_name then
	      entry_incoming_pcs := st_last :: !entry_incoming_pcs ;
	    get_pcs_rec (new_first, new_last) rest_ws
	| [] -> (first_opt, last) in
      let (first_opt, last) = get_pcs_rec (None, -1) [wto] in
      (!entry_pc,
       Option.get first_opt,
       last,
       !entry_incoming_pcs,
       !last_in_entry_state)

    method private is_handler (state_name:symbol_t) =
      let str = state_name#getBaseName in
      try
	let _ = Str.search_forward (Str.regexp "handler") str 0 in
	true
      with _ -> false

    method private pp_state_pc_list (pairs:(state_int * int) list) =
      let pp_state_int (state, pc) =
        LBLOCK [STR "("; state#getLabel#toPretty; STR ", "; INT pc; STR ")"] in
      pretty_print_list pairs pp_state_int "{" ", " "}"


    (* Returns the list of states in the wto *)
    method get_states =
      let rec add_st ss ws =
	match ws with
	| (SCC inner_ws) :: rest_ws ->
	    add_st (add_st ss inner_ws) rest_ws
	| (VERTEX st) :: rest_ws ->
	    add_st (st :: ss) rest_ws
	| [] -> ss in
      add_st [] [wto]

    (* Returns 1 if the instr at pc has a jump to the offset
     * Returns 2 if the instr at pc is a table/lookupswitch with a
     * jump to offset *)
    method private is_jump (pc:int) (offset:int) =
      let opcodes =
        (Option.get (JCHSystemUtils.get_bytecode proc_name))#get_code in
      match opcodes#at pc with
      | OpIfEq n
      | OpIfNe n
      | OpIfLt n
      | OpIfGe n
      | OpIfGt n
      | OpIfLe n
      | OpIfNull n
      | OpIfNonNull n
      | OpIfCmpEq n
      | OpIfCmpNe n
      | OpIfCmpLt n
      | OpIfCmpGe n
      | OpIfCmpGt n
      | OpIfCmpLe n
      | OpIfCmpAEq n
      | OpIfCmpANe n
      | OpGoto n ->
	  if n = offset then 1 else 0
      |	OpTableSwitch (_,_,_,table) ->
	begin
	  let found = ref false in
	  for i = 0 to pred (Array.length table) do
	    if table.(i) = offset then
	      found := true
	  done ;
	  if !found then 2 else 0
	end
      |	OpLookupSwitch (_, pairs) ->
	 if List.exists (fun (_,n) -> offset = n) pairs then
           2
	 else
           0
      | _ -> 0

    method private set_inloop_calls () =
      let in_loop pc = !first_pc <= pc && pc < !last_pc in
      let opcodes:opcodes_int =
        (Option.get (JCHSystemUtils.get_bytecode proc_name))#get_code in
      let loop_pcs = ref [] in
      let check (pc: int) (opc:opcode_t) =
	if in_loop pc then
	  begin
	    loop_pcs := (pc,opc) :: !loop_pcs ;
	    match opc with
	    | OpInvokeStatic (cn,ms)
	    | OpInvokeVirtual (TClass cn,ms)
	    | OpInvokeSpecial (cn,ms)
	    | OpInvokeInterface (cn,ms) ->
               call_pcs := (cn#index,ms#index,pc) :: !call_pcs
	    | _ -> ()
	  end in
      opcodes#iteri check ;
      instr_count := List.length !loop_pcs

    method get_loop_info () =
      let get_pc_range w = (w#get_first_pc, w#get_last_pc) in
      { li_first_pc = !first_pc ;
	li_entry_pc = !entry_pc ;
	li_last_pc = !last_pc ;
	li_instr_count = !instr_count ;
	li_cond_pcs = cond_pcs ;
	li_inner_loops = List.map get_pc_range !inner_loops ;
	li_outer_loops = List.map get_pc_range !outer_loops ;
	li_max_iterations = !max_iterations ;
	li_pc_invariants = [] ;
	li_calls = !call_pcs;
      }

    method toPretty =
      let pp_w =
	LBLOCK [STR " wto: "; pretty_print_wto [wto]] in
      let pp_c conds =
	LBLOCK [STR "conditions that loop exits are under: "; NL;
		 INDENT (5, (LBLOCK [pp_list conds; NL]))] in
      let pp_ec =
	LBLOCK [STR "states to which the loop exits: "; NL;
		 INDENT (5, (LBLOCK [pp_list exit_conds; NL]))] in
      let pp_p =
	match !outer_loops with
	| wto_info :: _ -> LBLOCK [STR "in wto "; wto_info#get_name#toPretty]
	| _ -> STR "is top wto" in
      let pp_ch =
	if !inner_loops = [] then
	  STR ""
	else
	  LBLOCK [STR " includes ";
                  pp_list (List.map (fun wi -> wi#get_name) !inner_loops)] in
      let pp_cb =
	if !catch_block_starts = [] then STR ""
	else
	  LBLOCK [STR " included in catch blocks that start at offsets: ";
                  pp_list_int !catch_block_starts] in
      LBLOCK [STR "wto "; name#toPretty; STR " from "; proc#getName#toPretty; NL;
		 INDENT (5, LBLOCK [STR " index: "; INT index; NL;
				     pp_p; pp_ch; NL;
				     pp_w; NL;
				     pp_cb ; NL;
				     INDENT (5, LBLOCK [pp_c conds; pp_ec]); NL])]

  end

let get_wto_name (wto:wto_component_t) =
  match wto with
  | (SCC ((VERTEX s) :: _)) -> s
  |  _ -> raise (JCH_failure (STR "getSCCHead expected SCC ((VERTEX _)::_)"))

(* Returns true if s is the name of a conditional statement
 * Are these the only statements that determine the exit from a loop?
 * Hopefully *)
let is_conditional (s: symbol_t) =
  let name = s#getBaseName in
  if String.length name > 5 then
    let end4 = String.sub name (String.length name - 4) 4 in
    end4 = "else" || end4 = "then"
  else
    false

(* Returns the states in wto that are loop exits,
 * as (state in wto, the successor state out of wto or the
 * conditional pair that is out of the wto) *)
let get_first_states_out (cfg:cfg_int) (wto: wto_t)  =
  let states =
    let rec addSt ss ws =
	match ws with
	| (SCC inner_ws) :: rest_ws ->
	    addSt (addSt ss inner_ws) rest_ws
	| (VERTEX st) :: rest_ws ->
	    addSt (st :: ss) rest_ws
	| [] -> ss in
    addSt [] wto in
  let is_in_wto (s:symbol_t) =
    List.exists (fun st -> st#getBaseName = s#getBaseName) states in
  let is_ex_exit (s:symbol_t) = s#getBaseName = "exceptional-exit" in
  let is_of_interest (s:symbol_t) =
    not ((is_in_wto s) || (is_ex_exit s)) in
  let get_opp_cond (cond:symbol_t) =
    let opp_name =
      let name = cond#getBaseName in
      let opp_name = Bytes.of_string name in
      let suff =
	match String.sub name ((String.length name) - 4) 4 with
	| "else" -> "then"
	| _ -> "else" in
      Bytes.blit
        (Bytes.of_string suff) 0 opp_name ((Bytes.length opp_name) - 4) 4;
      Bytes.to_string opp_name in
    let has_opp_name (state:symbol_t) =
      state#getBaseName = opp_name in
    try
      List.find has_opp_name cfg#getStates
    with
    | Not_found ->
	pr__debug [STR "state "; STR opp_name; STR " not found in JCHLoopUtils" ] ;
	raise
          (JCH_failure
             (LBLOCK [ STR "state " ; STR opp_name ;
                       STR " not found in JCHLoopUtils" ])) in
  let get_succ_out (s:symbol_t) =
    let state = cfg#getState s in
    let succs = state#getOutgoingEdges in
    List.filter is_of_interest succs in
  let addConds (conds: (symbol_t * symbol_t) list) (s:symbol_t) =
    let get_next_state (next:symbol_t) =
      if is_conditional next then
        (get_opp_cond next, next)
      else
        (s, next) in
    (List.map get_next_state (get_succ_out s)) @ conds in
    List.fold_left addConds [] states

(* finds all the states that are previous to the states in the scc
 * and are not in the scc *)
let find_scc_prev_states
      (cfg:cfg_int) (states:SymbolCollections.set_t):symbol_t list =
  let all_other_states:symbol_t list ref = ref [] in
  let add (s:symbol_t) =
    let prev_states:symbol_t list = (cfg#getState s)#getIncomingEdges in
    let add_prev (p:symbol_t) =
      if not (states#has p) then
        all_other_states := p :: !all_other_states in
    List.iter add_prev prev_states in
  states#iter add ;
  !all_other_states

(* Finds other conditions the exit is under *)
let find_prev_conds
      (cfg:cfg_int)
      (states:symbol_t list)
      (wtoHead:symbol_t)
      (state_to_scc_states:(symbol_t,SymbolCollections.set_t) H.t):symbol_t list =
  let wtoHead_name = wtoHead#getBaseName in
  let all_conds =
    SymbolCollections.set_of_list (List.filter is_conditional states) in
  let covered_states =
    StringCollections.set_of_list (List.map (fun s -> s#getBaseName) states) in
  let work_states =
    ref (List.filter (fun s -> s#getBaseName != wtoHead_name) states) in
  let rec find_prev_states () =
    match !work_states with
    | s :: rest_states ->
	begin
	  work_states := rest_states ;
	  let add_previous in_scc p =
	    let p_name = p#getBaseName in
	    (if p_name = wtoHead_name then
               ()
	     else if covered_states#has p_name then
               ()
	    else
	      begin
		covered_states#add p_name;
		if is_conditional p then
                  all_conds#add p ;
		if in_scc then
                  ()
		else
                  work_states := p :: !work_states
	      end ) in
	  let ps =
	    match H.find_opt state_to_scc_states s with
	    | Some scc_states ->
                let prevs = find_scc_prev_states cfg scc_states in
		scc_states#iter (add_previous true) ;
		prevs
	    | _ -> [] in
          List.iter (add_previous false) ps ;
	  find_prev_states ();
	end
    | [] -> () in
  find_prev_states () ;
  all_conds#toList

let add_all_wto_states (ws: wto_component_t list) =
  let states = new SymbolCollections.set_t in
  let rec add ws =
    match ws with
    | (VERTEX s) :: rest_ws ->
	states#add s;
	add rest_ws
    | (SCC ws') :: rest_ws ->
	add ws' ;
	add rest_ws
    | _ -> () in
  add ws ;
  states

let make_state_to_scc_states (wto: wto_component_t) =
  let table = Hashtbl.create 3 in
  let process w =
    match w with
    | (VERTEX s) ->
	Hashtbl.add table s (SymbolCollections.set_of_list [s])
    | (SCC ws') ->
	let all_ss = add_all_wto_states ws' in
	all_ss#iter (fun s -> Hashtbl.add table s all_ss) in
  (match wto with
  | SCC ws -> List.iter process ws
  | _ -> ());
  table

let make_wto_info
      ~(_proc_name:symbol_t)
      ~(cfg:cfg_int)
      ~(wto:wto_component_t)
      ~(outer_loops:'a list)
      ~(proc:procedure_int)
      ~(proc_wto:wto_component_t list) =
  let name = get_wto_name wto in
  let cond_pairs = get_first_states_out cfg [wto] in
  let state_to_scc_states = make_state_to_scc_states wto in
  let (states, exit_conds) = List.split cond_pairs in
  let all_conds = find_prev_conds cfg states name state_to_scc_states in
  let exit_conds =  (* to remove duplicates *)
    (SymbolCollections.set_of_list exit_conds)#toList in
  let wto_info =
    new wto_info_t
        ~is_proc_wto:false
        ~name
        ~wto
        ~conds:all_conds
        ~exit_conds
        ~proc
        ~cfg
        ~proc_wto in
  wto_info#set_outer_loops outer_loops ;
  wto_info


let get_sccs_proc procedure (proc_name: symbol_t) =
  let cfg = JCHSystemUtils.get_CFG procedure in
  let engine = new wto_engine_t (new CHIterator.fwd_graph_t cfg) in
  let wto = engine#computeWTO in
  let wto_infos = ref [] in
  let max_depth = ref 0 in
  let rec addSCCs (ws:wto_t) (loops: wto_info_t list) (depth:int) =
    match ws with
    | (SCC inner_ws as scc) :: rest_ws ->
       let wto_info =
         make_wto_info
           ~_proc_name:proc_name
           ~cfg
           ~wto:scc
           ~outer_loops:loops
           ~proc:procedure
           ~proc_wto:wto in
	let _ =
	  match loops with
	  | loop :: _rest_loops -> loop#add_inner_loop wto_info
	  | _ -> () in
	wto_infos := wto_info :: !wto_infos ;
	let new_depth = succ depth in
	(if new_depth > !max_depth then
          max_depth := new_depth
        else
          ()) ;
	addSCCs inner_ws (wto_info :: loops) new_depth ;
	addSCCs rest_ws loops depth
    | (VERTEX _) :: rest_ws ->
	addSCCs rest_ws loops depth
    | [] ->  () in
  addSCCs wto [] 0 ;
  (List.rev !wto_infos, wto, !max_depth)


let get_loop_infos (mInfo:method_info_int) =
  if mInfo#has_bytecode then
    try
      let proc = get_chif mInfo#get_class_method_signature in
      let (wto_infos, _, _) = get_sccs_proc proc proc#getName in
      List.map (fun wto_info -> wto_info#get_loop_info ()) wto_infos
    with
    | JCH_failure p ->
	begin
	  pr_debug [ STR "Failure in translating " ;
		     mInfo#get_class_method_signature#toPretty ;
		     STR ": " ; p ; NL ] ;
	  [ { li_first_pc = (-1) ;
	      li_entry_pc = (-1) ;
	      li_last_pc = (-1) ;
	      li_instr_count = (-1) ;
	      li_cond_pcs = [] ;
	      li_inner_loops = [] ;
	      li_outer_loops = [] ;
	      li_max_iterations = [] ;
	      li_pc_invariants = [] ;
	      li_calls = []
	    } ]
	end
  else
    []

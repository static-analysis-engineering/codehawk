(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
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
open CHLanguage
open CHPretty
open CHUtils
open CHSCC

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHIFSystem
open JCHPreAPI
open JCHSystemSettings


let wto_index = ref (-1)

let is_sym_conditional (s:symbol_t) =
  let name = s#getBaseName in
  try
    let _ = Str.search_forward (Str.regexp ("then\\|else")) name 0 in
    true
  with _ -> false

let get_pc_from_sym (s:symbol_t) =
  let get_num_str str =
    let first = Str.search_forward (Str.regexp "[0-9]") str 0 in
    let last =
      try
	Str.search_forward (Str.regexp "[a-zA-Z_.-]") str first
      with
      | _ -> String.length str in
    String.sub str first (last-first) in
  let num_str = get_num_str s#getBaseName in
  try
    int_of_string num_str
  with
  | _ ->
    raise
      (JCH_failure
         (LBLOCK [STR "Error in extracting pc from symbol: "; s#toPretty]))


let get_unique_syms (l:symbol_t list) =  (SymbolCollections.set_of_list l)#toList


(* Information about wtos that is collected from the original CFG
 * the exit info could get lost when simplifying the CHIF *)
class wto_info_t
  (is_proc_wto: bool)
  (name: symbol_t)
  (wto: wto_component_t)
  (conds: symbol_t list list)
      (* states that have conditions for loop exits. Each list corresponds
         to a complete list of branches that lead to an exit *)
  (exit_conds: symbol_t list)
      (* states outside the wto that are loop exits *)
  (proc: procedure_int)
  (cfg: cfg_int)
  (proc_wto: wto_t) =
object (self: 'a)

  val proc_name = proc#getName
  val mInfo = app#get_method (retrieve_cms proc#getName#getSeqNumber)
  val mutable inner_loops = []
  val mutable outer_loops = []  (* from the inner one to the outer one *)
  val index = begin incr wto_index; !wto_index end
  val var_name = new symbol_t ~seqnr: !wto_index "lc"

  val var =
    let name = new symbol_t ~seqnr: !wto_index "lc" in
    new variable_t name NUM_VAR_TYPE

  val mutable entry_pc = (-1)
  val mutable first_pc = (-1)
  val mutable last_pc = (-1)

  val cond_pcs =
    let all_conds =
      List.filter is_sym_conditional (get_unique_syms (List.flatten conds)) in
    List.map get_pc_from_sym all_conds

  val mutable has_monitor_enter = false
  val mutable has_monitor_exit = false
  val mutable max_iterations:jterm_t list = []

  (* all catch blocks in the method *)
  val mutable all_catch_blocks:handler_block_int list = []

  (* starts of catch blocks that include the loop *)
  val mutable catch_block_starts:int list = []

  method private find_catch_blocks_that_contain pc =
    let includes_pc pc handler_block =
      pc >= handler_block#get_start_pc && pc <= handler_block#get_end_pc in
    List.map (fun cb ->
        cb#get_start_pc) (List.filter (includes_pc pc) all_catch_blocks)

  initializer
    if is_proc_wto then ()
    else
      begin
	let (epc, fpc, lpc) = self#get_entry_first_last in
	begin
	  entry_pc <- epc;
	  first_pc <- fpc;
	  last_pc <- lpc;
	end;

	let exception_handlers = mInfo#get_exception_handlers in
	begin
	  all_catch_blocks <- exception_handlers#get_handler_blocks;
	  catch_block_starts <- (self#find_catch_blocks_that_contain first_pc)
	end
      end

  method get_name = name
  method get_wto = wto

  method get_inner_loops = inner_loops
  method get_outer_loops = outer_loops

  method get_conds = conds
  method get_cond_pcs = cond_pcs
  method get_exit_conds = exit_conds

  method get_index = index

  method get_var_name = var_name
  method get_var = var

  method get_proc_wto = proc_wto

  method get_entry_pc = entry_pc
  method get_first_pc = first_pc
  method get_last_pc = last_pc

  method get_max_iterations = max_iterations

  method is_outer_most = outer_loops = []

  method add_inner_loop (inner_loop: 'a) =
    inner_loops <- inner_loop :: inner_loops

  method set_outer_loops (outer_wtos : 'a list) = outer_loops <- outer_wtos

  (* Checks wether s is a state in the wto *)
  method has_state s =
    let rec hasLp ws =
      match ws with
      | (SCC inner_ws) :: rest_ws -> ((hasLp inner_ws) || (hasLp rest_ws))
      | (VERTEX st) :: rest_ws -> (st#equal s) || (hasLp rest_ws)
      | [] -> false in
    hasLp [wto]

  method private get_first_and_last_in_state (state: state_int) =
    let last_seen = ref (-1) in
    let lowest = ref None in
    let rec walkCode code : unit =
      for i = 0 to code#length - 1 do walkCmd (code#getCmdAt i) done
    and walkCmd cmd : unit =
      match cmd with
      | CODE (s, code) ->
	if s#getBaseName = "enter_state" then ()
	else walkCode code
      | OPERATION op ->
	begin
	  match op.op_name#getBaseName with
	  | "i"
	  | "ii"
	  | "v" ->
	    begin
	      let bcloc = get_bytecode_location_in_proc proc_name op.op_name in
	      let iInfo = app#get_instruction bcloc in
	      let record () =
		let pc = iInfo#get_location#get_pc in
		begin
		  last_seen := pc;
		  (match !lowest with
		  | Some low_pc -> if pc < low_pc then lowest := Some pc
		  | None -> lowest := Some pc )
		end in
	      match iInfo#get_opcode with
	      | OpMonitorEnter ->
                 begin
                   has_monitor_enter <- true;
                   record ()
                 end
	      | OpMonitorExit ->
                 begin
                   has_monitor_exit <- true;
                   record ()
                 end
	      | OpIfEq _
	      | OpIfNe _
	      | OpIfLt _
	      | OpIfGe _
	      | OpIfGt _
	      | OpIfLe _
	      | OpIfNull _
	      | OpIfNonNull _
	      | OpIfCmpEq _
	      | OpIfCmpNe _
	      | OpIfCmpLt _
	      | OpIfCmpGe _
	      | OpIfCmpGt _
	      | OpIfCmpLe _
	      | OpIfCmpAEq _
	      | OpIfCmpANe _
	      | OpCmpL -> last_seen := iInfo#get_location#get_pc
	      | _ -> record ()
	    end
	  | _ -> ()
	end
      | _ -> ()
    in
    begin
      walkCode state#getCode;
      (!lowest, !last_seen)
    end

  (* Returns the entry, first and last pc in a loop *)
  method private get_entry_first_last =
    let entry = ref true in
    let entry_pc = ref (-1) in
    let rec get_pcs_rec (first_opt, last) ws =
      match ws with
      | (SCC inner_ws) :: rest_ws ->
	get_pcs_rec (get_pcs_rec (first_opt, last) inner_ws) rest_ws
      | (VERTEX st_name) :: rest_ws ->
	let state = cfg#getState st_name in
	let (st_first_opt, st_last) = self#get_first_and_last_in_state state in
	let new_first =
	  match (first_opt, st_first_opt) with
	  | (Some first, Some st_first) ->
	    (* In the case of wto = (... (... pc=5-then) pc=5-else)
               it will get pc=5-else *)
	    if st_first < first then Some st_first else Some first
	  | (Some first, None) -> Some first
	  | (None, Some st_first) -> Some st_first
	  | _ -> None in
	let new_last = if st_last >= last then st_last else last in
	begin
	  (if !entry then
	    begin
	      entry_pc := Option.get st_first_opt;
	      entry := false
	    end
	   else ());
	  get_pcs_rec (new_first, new_last) rest_ws
	end
      | [] -> (first_opt, last) in
    let (first_opt, last) = get_pcs_rec (None, -1) [wto] in
    (!entry_pc, Option.get first_opt, last)

  method private is_handler state_name =
    let str = state_name#getBaseName in
    try
      let _ = Str.search_forward (Str.regexp "handler") str 0 in
      true
    with _ -> false

  method private pp_state_pc_list pairs =
    let pp_state_int (state, pc) =
      LBLOCK [STR "("; state#getLabel#toPretty; STR ", "; INT pc; STR ")"] in
    pretty_print_list pairs pp_state_int "{" ", " "}"

  (* True if this is the loop in a finally block that waits for this loop
     to finish *)
  method is_monitor_loop =
    (* I am not sure how to detect this loop exactly *)
    if inner_loops = [] && last_pc - first_pc <= 4 then
      let last_loc = get_bytecode_location proc_name#getSeqNumber last_pc in
      let iInfo = app#get_instruction last_loc in
      match iInfo#get_opcode with OpMonitorExit -> true | _ -> false
    else false

  (* Returns the list of states in the wto *)
  method get_states =
    let rec add_st (ss:symbol_t list) (ws:wto_t) =
      match ws with
      | (SCC inner_ws) :: rest_ws -> add_st (add_st ss inner_ws) rest_ws
      | (VERTEX st) :: rest_ws -> add_st (st :: ss) rest_ws
      | [] -> ss in
    add_st [] [wto]

  (* ---------------------------------------------------------------------------
     Returns 1 if the instr at pc has a jump to the offset
     Returns 2 if the instr at pc is a table/lookupswitch with a jump to offset
     --------------------------------------------------------------------------- *)
  method private is_jump pc offset =
    match mInfo#get_opcode pc with
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
    | OpGoto n -> if n = offset then 1 else 0

    | OpTableSwitch (_,_,_,table) ->
      begin
	let found = ref false in
	for i = 0 to pred (Array.length table) do
	  if table.(i) = offset then
	    found := true
	done;
	if !found then 2 else 0
      end

    | OpLookupSwitch (_, pairs) ->
      if List.exists (fun (_,n) -> offset = n) pairs then 2 else 0
    | _ -> 0

  method toPretty =
    let pp_w = LBLOCK [STR " wto: "; pretty_print_wto [wto]] in
    let pp_c cond  = LBLOCK [pp_list cond; NL] in
    let pp_c conds =
      LBLOCK [STR "exit-condition states: "; NL;
	      INDENT (5, LBLOCK (List.map pp_c conds))] in
    let pp_ec =
      LBLOCK [STR "states to which the loop exits: "; NL;
	      INDENT (5, (LBLOCK [pp_list exit_conds; NL]))] in
    let pp_p =
      match outer_loops with
      | wto_info :: _ -> LBLOCK [STR "in wto "; wto_info#get_name#toPretty]
      | _ -> STR "is outermost wto" in
    let pp_ch =
      match inner_loops with
      | [] -> STR ""
      | _ -> LBLOCK [STR " includes ";
		     pp_list (List.map (fun wi -> wi#get_name) inner_loops)] in
    let pp_cb =
      match catch_block_starts with
      | [] -> STR ""
      | _ ->
         LBLOCK [
             STR " included in catch blocks that start at offsets: ";
	     pp_list_int catch_block_starts] in
    LBLOCK [
        STR "wto ";
        name#toPretty;
        STR " from ";
        proc#getName#toPretty; NL;
	INDENT (5, LBLOCK [
                       STR " index: ";
                       INT index;
                       NL;
		       pp_p;
                       pp_ch;
                       NL;
		       pp_w; NL;
		       pp_cb; NL;
		       INDENT (5, LBLOCK [pp_c conds; pp_ec]); NL])]
end


let get_wto_name wto =
  match wto with
  | (SCC ((VERTEX s) :: _)) -> s
  |  _ -> raise (JCH_failure (STR "getSCCHead expected SCC ((VERTEX _)::_)"))


(* -----------------------------------------------------------------------------
   Returns true if s is the name of a conditional statement
   (Are these the only statements that determine the exit from a loop? Hopefully)
   ----------------------------------------------------------------------------- *)
let is_conditional (s: symbol_t) =
  let name = s#getBaseName in
  if String.length name > 5 then
    let end4 = String.sub name (String.length name - 4) 4 in
    end4 = "else" || end4 = "then"
  else
    false


(* ----------------------------------------------------------------------------
   Returns the states in wto that are loop exits, as
   (state in wto, the successor state out of wto or the conditional pair that
   is out of the wto)
   ---------------------------------------------------------------------------- *)
let get_first_states_out (cfg:cfg_int) (wto: wto_t)  =
  try
    let states =
      let rec addSt (ss:symbol_t list) (ws:wto_t) =
	match ws with
	| (SCC inner_ws) :: rest_ws -> addSt (addSt ss inner_ws) rest_ws
	| (VERTEX st) :: rest_ws -> addSt (st :: ss) rest_ws
	| [] -> ss in
      addSt [] wto in
    let is_in_wto s =
      List.exists (fun st -> st#getBaseName = s#getBaseName) states in
    let is_ex_exit s = s#getBaseName = "exceptional-exit" in
    let is_of_interest s = not ((is_in_wto s) || (is_ex_exit s)) in
    let get_opp_cond (cond:symbol_t) =
      let opp_name =
        let name = cond#getBaseName in
        let opp_name = Bytes.copy (Bytes.of_string name) in
        let suff =
	  match String.sub name ((String.length name) - 4) 4 with
	  | "else" -> "then"
	  | _ -> "else" in
        begin
          Bytes.blit
            (Bytes.of_string suff) 0 opp_name ((Bytes.length opp_name) - 4) 4;
          Bytes.to_string opp_name
        end in
      let has_opp_name state = state#getBaseName = opp_name in
      try
        List.find has_opp_name cfg#getStates
      with
      | Not_found ->
	 raise
           (JCH_failure
              (LBLOCK [
                   STR "State ";
                   STR opp_name;
                   STR " not found in ";
		   STR " JCHLoopUtils.get_first_states_out"])) in
    let get_succ_out (s:symbol_t) =
      let state = cfg#getState s in
      let succs = state#getOutgoingEdges in
      List.filter is_of_interest succs in
    let addConds (conds: (symbol_t * symbol_t) list) s =
      let get_next_state next =
        if is_conditional next then
	  (get_opp_cond next, next)
        else
	  (s, next) in
      (List.map get_next_state (get_succ_out s)) @ conds in
    List.fold_left addConds [] states
  with
  | Invalid_argument s ->
     raise (JCH_failure (LBLOCK [STR "Error in get_first_states_out: "; STR s]))


(* -----------------------------------------------------------------------------
   Returns the states in wto that have a name of the form pc = _.then or pc = _.else
   and that have a corresponding pair that is not in the wto.
   ----------------------------------------------------------------------------- *)
let get_cond_scc (wto: wto_t) : symbol_t list =
  try
    let rec addCondSCC (wto: wto_t) (ops: symbol_t list) : symbol_t list =
      (* paired: true if the two symbols have the same beginning. The intention here
         is to ret urn true for name.then and name.else *)
      let paired (s1:symbol_t) (s2: symbol_t) =
        let name1 = s1#getBaseName and
	    name2 = s2#getBaseName in
        String.sub name1 0 ((String.length name1) - 5) =
          String.sub name2 0 ((String.length name2) - 5) in

      (* addOrRemove: Removes its pair from ls1 if it finds or else it adds
         i tself to ls2 *)
      let rec addOrRemove s ls1 ls2 =
        match ls1 with
        | (s'::rest_ls1) ->
	   if (paired s s')
	   then
	     List.rev_append rest_ls1 ls2
	   else
	     addOrRemove s rest_ls1 (s'::ls2)
        | [] -> (s::ls2) in
      begin
        match wto with
        | (SCC w)::ws -> addCondSCC ws (addCondSCC w ops)
        | (VERTEX s)::ws ->
	   let ops = if is_conditional s then addOrRemove s ops [] else ops in
	   addCondSCC ws ops
        | [] -> ops
      end in
    addCondSCC wto []
  with
  | Invalid_argument s ->
     raise (JCH_failure (LBLOCK [STR "Error in get_cond_scc: "; STR s]))


(* Collect conditions that are under the same exit *)
let find_prev_conds (cfg:cfg_int) (s:symbol_t) (wtoHead:symbol_t) =
  let rec find_prev_states (ss:symbol_t list) (preds:wto_t) =
    match ss with
    | s :: rest_ss ->
      let state = cfg#getState s in
      let ps = state#getIncomingEdges in
      let addPred (sts, prs) p =
	if List.exists (fun q ->
	  match q with VERTEX v -> v#equal p | _ -> false) preds then
          (sts, prs)
	else if p#equal wtoHead then
          (sts, prs)
	else
          (p :: sts, (VERTEX p) :: prs) in
      let (new_ss, new_preds) =
	List.fold_left addPred (rest_ss, preds) ps in
      find_prev_states new_ss new_preds
    | [] -> preds in
  let prev_states = find_prev_states [s] [] in
  get_cond_scc prev_states


let make_wto_info
    (proc:procedure_int)
    (cfg:cfg_int)
    (wto:wto_component_t)
    (outer_loops:wto_info_t list)
    (proc_wto:wto_t) =
  let name = get_wto_name wto in
  let conds = get_first_states_out cfg [wto] in
  let addPrevConds cond =
    if cond#equal name then
      [cond]
    else
      (* collect all conditions that are under this exit *)
      cond :: (find_prev_conds cfg cond name) in
  let all_conds = List.map (fun (c, ec) -> (addPrevConds c, ec)) conds in
  let (conds, exit_conds) = List.split all_conds in
  let exit_conds = get_unique_syms exit_conds in
  let wto_info = new wto_info_t false name wto conds exit_conds proc cfg proc_wto in
  begin
    wto_info#set_outer_loops outer_loops;
    wto_info
  end


let get_sccs_proc proc =
  let cfg =
    let rec get_CFG_code code =
      match code#getCmdAt 0 with
      | RELATION cd -> get_CFG_code cd
      | CFG (_, cfg) -> cfg
      | cmd ->
	let _ = pr_debug [STR "getCFG "; command_to_pretty 0 cmd; NL] in
	raise
          (JCHBasicTypes.JCH_failure
             (STR "getCFG expected CODE [CFG cfg; ...] ")) in
    get_CFG_code proc#getBody in
  let engine = new wto_engine_t (new CHIterator.fwd_graph_t cfg) in
  let wto = engine#computeWTO in
  let wto_infos = ref [] in
  let rec addSCCs ws (loops: wto_info_t list) depth =
    match ws with
    | (SCC inner_ws as scc) :: rest_ws ->
      let wto_info = make_wto_info proc cfg scc loops wto in
      let _ = List.map (fun l -> l#add_inner_loop wto_info) loops in
      begin
	wto_infos := wto_info :: !wto_infos;
	addSCCs inner_ws (wto_info :: loops) (depth + 1);
	addSCCs rest_ws loops depth
      end
    | (VERTEX _) :: rest_ws -> addSCCs rest_ws loops depth
    | [] ->  () in
  begin
    addSCCs wto [] 0;
    List.rev !wto_infos
  end


let get_inloop_calls (mInfo:method_info_int) (first_pc:int) (last_pc:int) =
  let in_loop pc = first_pc <= pc && pc < last_pc in
  let loopPcs = ref [] in
  let callPcs = ref [] in
  let _ = mInfo#bytecode_iteri (fun pc opc ->
    if in_loop pc then
      begin
	loopPcs := (pc,opc) :: !loopPcs;
	match opc with
	| OpInvokeStatic (cn,ms)
	| OpInvokeVirtual (TClass cn, ms)
	| OpInvokeSpecial (cn,ms)
	| OpInvokeInterface (cn, ms) ->
           callPcs := (cn#index, ms#index, pc) :: !callPcs
	| _ -> ()
      end) in
  (List.length !loopPcs, !callPcs)


let get_loop_infos (mInfo:method_info_int) =
  if mInfo#has_bytecode then
    try
      let proc = get_chif mInfo#get_class_method_signature in
      let wtoInfos = get_sccs_proc proc in
      let get_pc_range w = (w#get_first_pc, w#get_last_pc) in
      List.map (fun wtoInfo ->
	let firstPc = wtoInfo#get_first_pc in
	let lastPc = wtoInfo#get_last_pc in
	let (instrCount,calls) = get_inloop_calls mInfo firstPc lastPc in
	{ li_first_pc = firstPc;
	  li_entry_pc = wtoInfo#get_entry_pc;
	  li_last_pc = lastPc;
	  li_instr_count = instrCount;
	  li_cond_pcs = wtoInfo#get_cond_pcs;
	  li_inner_loops = List.map get_pc_range wtoInfo#get_inner_loops;
	  li_outer_loops = List.map get_pc_range wtoInfo#get_outer_loops;
	  li_max_iterations = wtoInfo#get_max_iterations;
	  li_pc_invariants = [];
	  li_calls = calls
	}) wtoInfos
    with
      JCH_failure p ->
	begin
	  system_settings#log_error p;
	  (pr_debug [
               STR "No loop features for ";
               mInfo#get_class_method_signature#toPretty;
	       STR ": ";
               p;
               NL]);
	   [{ li_first_pc = (-1);
	       li_entry_pc = (-1);
	       li_last_pc = (-1);
	       li_instr_count = (-1);
	       li_cond_pcs = [];
	       li_inner_loops = [];
	       li_outer_loops = [];
	       li_max_iterations = [];
	       li_pc_invariants = [];
	       li_calls = []
	     }]
	   end
  else
    []

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
open CHPretty
open CHLanguage
open CHUtils
open CHSCC


class taint_loop_manager_t =
  object (self: _)

    (* for each variable, the list of loops where they are created in *)
    val var_to_loops_table : IntCollections.set_t VariableCollections.table_t =
      new VariableCollections.table_t

    (* Stores the loops that a variable is a bound for *)
    val bound_to_loops_table : IntCollections.set_t VariableCollections.table_t =
      new VariableCollections.table_t

    method get_var_to_loops = var_to_loops_table
    method get_bound_to_loops = bound_to_loops_table

    (* Given a WTO, it returns a list of variables that could get tainted,
     * that is, any write variable other than assignments to constants *)
    method private set_var_to_loops
                     (proc_name:symbol_t)
                     (wto_info:JCHLoopUtils.wto_info_t)
                     (cfg:cfg_int)  =
      let loop_index = wto_info#get_index in
      let addStateVars vert vs : variable_t list =
	let code = (cfg#getState vert)#getCode in
	let state_vars = JCHCollectors.collect_loop_vars proc_name code in
	List.rev_append state_vars vs in
      let rec addWTOVars (ws: wto_component_t list) (vs: variable_t list) =
	match ws with
	| (SCC w) :: rest_ws ->
	    addWTOVars (List.rev_append w rest_ws) vs
	| (VERTEX vert) :: rest_ws ->
	    addWTOVars rest_ws (addStateVars vert vs)
	| [] ->
	   vs in
      let write_vars =
	addWTOVars [wto_info#get_wto] [] in
      let addVarToLoops v =
	match var_to_loops_table#get v with
	| Some set ->
	    set#add loop_index
	| None ->
	    var_to_loops_table#set v (IntCollections.set_of_list [loop_index]) in
      List.iter addVarToLoops write_vars

    method private set_bound_to_loops
                     (proc_name:symbol_t)
                     (wto_info:JCHLoopUtils.wto_info_t)
                     (cfg:cfg_int) =
      let loop_index = wto_info#get_index in
      let all_conds = wto_info#get_conds in
      let add_cond_assert_vars (vars: variable_t list) state_name =
	let state = cfg#getState state_name in
	let state_vars = JCHCollectors.collect_bound_vars proc_name state#getCode in
	vars @ state_vars in (* Why not change the order here there is no need for List.rev later on ? *)

      (* reverse because I need the mainCond processed first in case it is unreachable *)
      let assert_vars = List.rev (List.fold_left add_cond_assert_vars [] all_conds) in

      let add_assert_vars vs =
	let add_var v =
	  (match bound_to_loops_table#get v with
	  | Some set ->
	      set#add loop_index
	  | None ->
	      bound_to_loops_table#set v (IntCollections.set_of_list [loop_index])) in
	List.iter add_var vs in
      add_assert_vars assert_vars

    method initialize_tables (proc_info: JCHProcInfo.jproc_info_t) =
      let cfg = proc_info#get_cfg in
      let proc_name = proc_info#get_name in
      let initialize_tables_wto wto_info =
	if not wto_info#is_unreachable then
	  begin
	    self#set_var_to_loops proc_name wto_info cfg ;
	    self#set_bound_to_loops proc_name wto_info cfg
	  end in
      let wto_infos = proc_info#get_wto_infos in
      List.iter initialize_tables_wto wto_infos

    method toPretty =
      LBLOCK [STR "taint_loop_manager"; NL;
	      INDENT (5, LBLOCK [STR "var_to_loops_table: "; NL;
                                 var_to_loops_table#toPretty; NL;
				 STR "bound_to_loops_table: "; NL;
                                 bound_to_loops_table#toPretty; NL ])]

  end

let get_taint_loop_info (proc_info: JCHProcInfo.jproc_info_t) =
  let loop_manager = new taint_loop_manager_t in
  let _ = loop_manager#initialize_tables proc_info in
  (loop_manager#get_var_to_loops, loop_manager#get_bound_to_loops)


let get_pc_to_loop_vars (jproc_info: JCHProcInfo.jproc_info_t) =
  let state_to_pcs = JCHCollectors.collect_state_pcs jproc_info in
  let state_to_loop_vars = new SymbolCollections.table_t in
  let add_wto (wto_info: JCHLoopUtils.wto_info_t)  =
    let loop_var = wto_info#get_var in
    let states = wto_info#get_states in
    let add_state state =
      match state_to_loop_vars#get state with
      | Some set -> set#add loop_var
      | _ ->
         state_to_loop_vars#set
           state (VariableCollections.set_of_list [loop_var]) in
    List.iter add_state states in
  List.iter add_wto jproc_info#get_wto_infos ;
  let pc_to_loop_vars = new IntCollections.table_t in
  let add_state state loop_vars =
    match state_to_pcs#get state with
    | Some pcs -> pcs#iter (fun pc -> pc_to_loop_vars#set pc loop_vars)
    | _ -> () in
  state_to_loop_vars#iter add_state ;
  pc_to_loop_vars

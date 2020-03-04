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
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

module F = CHOnlineCodeSet.LanguageFactory

let dbg = ref false 

(* Transforms the CHIF by adding phi operations wherever needed *)
class ssa_phi_t 
    ~(procedure: procedure_int) 
    ~(cfg: cfg_int) 
    ~(dominance: JCHDominance.dominance_info_t) 
    ~(nr_states: int) = 
  object (self: _)

    val proc_name = procedure#getName 
    val arg_inds = 
      List.filter (fun v_ind -> v_ind <> exception_var_index) 
	(List.map (fun (_,v) -> v#getIndex) procedure#getBindings) 
    val cms = retrieve_cms procedure#getName#getSeqNumber 
    val states = cfg#getStates
    val writeVars_array = JCHSplitArray.make nr_states (new VariableCollections.set_t)
    val readVars_array = JCHSplitArray.make nr_states (new VariableCollections.set_t)
    val readWriteVars_array = JCHSplitArray.make nr_states (new VariableCollections.set_t)

    val work_array = JCHSplitArray.make nr_states 0 
    val hasAlready_array = JCHSplitArray.make nr_states 0
    val iter_count = ref 0
    val phiNeeded_array = JCHSplitArray.make nr_states (new VariableCollections.set_t)
    val current_state = ref state_name_sym

    method initialize_array () = 
      for i = 0 to nr_states - 1 do
	phiNeeded_array#set i new VariableCollections.set_t
      done

    method initialize = 
      let _ = self#initialize_array () in
      let initialize_state state = 
        if dominance#is_reachable state then
          let state_index = dominance#get_index state in
          let code = (cfg#getState state)#getCode in
	  let (rvars, wvars, rwvars) = 
	    JCHTransformUtils.get_vars_in_code proc_name code in
	  writeVars_array#set state_index wvars ;
	  readVars_array#set state_index rvars ;
	  readWriteVars_array#set state_index rwvars 
        else 
          () in
      List.iter initialize_state states ;

    (* Used to determine if the phi variable is needed 
     * However this does eliminate all the unnecessary ohi variables *)
    method isWriteBeforeRead (var:variable_t) (st_index:int) = 
      let state = cfg#getState (dominance#get_state st_index) in
      let code = state#getCode in
      let res = ref 0 in (* 1 is write first, 2 is read first *)
      let rec findVar cd = 
	for i = 0 to cd#length - 1 do
	  match cd#getCmdAt i  with 
	  | CODE (_, code) -> findVar code 
	  | RELATION code -> 
	      findVar code 
	  | TRANSACTION (_, code, post_code_opt) -> 
	      begin
		findVar code ;
		match post_code_opt with 
		| None -> ()
		| Some post_code -> 
		    findVar post_code 
	      end
	  | cmd -> let (rvars, wvars, rwvars) = 
	      JCHTransformUtils.get_vars_in_cmd proc_name cmd in
	    if (rvars#has var) || (rwvars#has var) then 
	      let _ = res := 2 in
	      raise Exit
	    else if wvars#has var then 
	      let _ = res := 1 in
	      raise Exit 
	done in
      try 
	findVar code ;
	false ;
      with
      |	Exit -> 
	  !res = 1

    method get_states_that_write var = 
      let write_list = ref [] in
      let read_list = ref [] in
      let read_write_list = ref [] in 
      for i = 0 to nr_states - 1 do 
	if (writeVars_array#get i)#has var then
	  write_list := i :: !write_list
	else () ;
	if (readVars_array#get i)#has var then
	  read_list := i :: !read_list
	else () ;
	if (readWriteVars_array#get i)#has var then 
	  read_write_list := i :: !read_write_list
	else () 
      done ;
      match (List.length !write_list,
             List.length !read_write_list,
             List.length !read_list) with 
      |	(1, 0, _)  (* The writes have to come before the reads unless it is a parameter *)
      |	(0, 1, _) -> 
	 if List.mem var#getIndex arg_inds then
           !write_list @ !read_write_list
	  else []
      |	(1, 1, 0) -> 
	  let w_st = List.hd !write_list in
	  let rw_st = List.hd !read_write_list in
	  if List.mem var#getIndex arg_inds then
            !write_list @ !read_write_list
	  else if (w_st = rw_st) && (self#isWriteBeforeRead var w_st) then
            []
	  else
            !write_list @ !read_write_list
      |	_ ->
         !write_list @ !read_write_list

    method find_phi_var (var:variable_t) = 
      let _ = iter_count := !iter_count + 1 in
      let write_list = self#get_states_that_write var in
      let init_work i = work_array#set i !iter_count in
      let workList = ref write_list in
      List.iter init_work write_list ;
      while !workList != [] do 
	let (state_index, rest_list) = (List.hd !workList, List.tl !workList) in
	workList := rest_list ;
	let set = dominance#get_dom_frontier state_index in
	let addState y = 
	  let y_index = dominance#get_index y in 
	  if (hasAlready_array#get y_index) < !iter_count
	  then 
	    begin
	      (phiNeeded_array#get y_index)#add var ;
	      hasAlready_array#set y_index !iter_count ;
	      if (work_array#get y_index) < !iter_count then 
		begin
		  work_array#set y_index !iter_count ;
		  workList := y_index :: !workList
		end
	      else ()
	    end
	  else () 
	in
	set#iter addState
      done

    method find_phi = 
      let variables = 
	let allVars = procedure#getScope#getVariables in
	let is_phi_var (v:variable_t) = 
	  not (v#isTmp
               || JCHSystemUtils.is_exception v
               || JCHSystemUtils.is_constant v) in
	List.filter is_phi_var allVars in
      self#initialize ;
      List.iter self#find_phi_var variables 

    method private mk_code cmds = JCHIFSystem.chif_system#make_code cms cmds

    method mkPhis_state (state_name:symbol_t) (state:state_int) = 
      let _ = current_state := state_name in
      let enter_code_cmds =
	let mkPhiArg var s_name = 
	  (s_name#getBaseName, var, READ) in
	let (phi_s, enter_s) = 
	  if state_name#getIndex = normal_exit_sym#getIndex then 
	    (final_phi_sym , enter_final_state_sym) 
	  else 
	    (phi_sym, enter_state_sym) in
	let mkArgs var = 
	  ("phi", var, WRITE) :: 
	  (List.map (mkPhiArg var) state#getIncomingEdges) in
	let mkPhi var = 
	  OPERATION { op_name = phi_s; op_args = mkArgs var }  in
	let enter_cmds = 
	  if state_name#getBaseName = exceptional_exit_sym#getBaseName
	     || state_name#getBaseName = method_exit_sym#getBaseName then 
	    []
	  else if dominance#is_reachable state_name then 
            let n = dominance#get_index state_name in
	    List.map mkPhi (phiNeeded_array#get n)#toList
          else
            [] in
	[CODE (enter_s, self#mk_code enter_cmds)] 
      in
      let exit_code_cmds = [CODE (exit_state_sym, self#mk_code [])]  in 
      JCHTransformUtils.mk_state
        state 
	(JCHSystemUtils.add_cmds
           ~cms
           ~init_cmds:enter_code_cmds
           ~final_cmds:exit_code_cmds
           ~code:state#getCode)
      
    method mkPhi_cfg = 
      let _  = self#find_phi in
      let change_state state_name = 
	self#mkPhis_state state_name (cfg#getState state_name) in
      let new_states = 
	List.rev_map change_state cfg#getStates in
      let new_cfg = F.mkCFG cfg#getEntry cfg#getExit in
      new_cfg#addStates new_states ;
      new_cfg

  end

(* Transforms the CHIF by introducing a new version of a variable 
 * at every new write on that variable. 
 * It also creates alias sets to be used by the alias_transformer
 * It also transforms the variable in the tables that keep track of char vars *)
class ssa_transformer_t 
    ~(proc_name: symbol_t)
    ~(phi_cfg: cfg_int) 
    ~(dominance: JCHDominance.dominance_info_t) = 
  object (self: _)

    inherit JCHCodeTransformers.variable_transformer_t as super

    val cms = retrieve_cms proc_name#getSeqNumber
    val stacks = new JCHTransformUtils.vv_stacks_t
    val alias_sets = new JCHTransformUtils.alias_sets_t
    val ssa_vars = new JCHTransformUtils.ssa_variable_t 
    val current_pc = ref 0 
    val rvar_to_pc_to_versions = new VariableCollections.table_t 
    val pc_to_instruction = 
      let method_info = app#get_method (retrieve_cms proc_name#getSeqNumber) in
      let stack_layouts =
        method_info#get_method_stack_layout#get_pc_stack_layouts in
      let table = new IntCollections.table_t in 
      let _ = List.iter (fun (pc,s) -> table#set pc s) stack_layouts in
      table

    method get_rvar_to_pc_to_versions = rvar_to_pc_to_versions

    method get_alias_sets = alias_sets 

    method replace_in_phi (cfg: cfg_int) (state: symbol_t) (succ: symbol_t) = 
      let replace_in_phi_arg arg = 
	match arg with
	| (_,_,WRITE) -> arg
	| (str, var, mode) -> 
	    if str = state#getBaseName
	    then 
	      match stacks#get var with
	      | Some stack -> 
		  begin
		    try 
		      let v = stack#top in
		      (str, v, mode)
		    with
		    | _ -> arg
		  end
	      | None -> arg
	    else arg in

      let replace_in_phi_cmd cmd = 
	match cmd with
	| OPERATION { op_name = name ; op_args = args } -> 
	    let new_args = List.map replace_in_phi_arg args in
	    OPERATION { op_name = name ; op_args = new_args }
	| _ -> cmd in

      (* first command in state is CODE enter_state with *)
      match (cfg#getState succ)#getCode#getCmdAt 0 with           
      |	CODE (_, enter_code) ->         
	  for i = 0 to enter_code#length - 1 do
	    let new_cmd = replace_in_phi_cmd (enter_code#getCmdAt i) in
	    enter_code#setCmdAt i new_cmd 
	  done
      | _ -> () 


    method private mk_code cmds = JCHIFSystem.chif_system#make_code cms cmds

    val init_cmd = ref SKIP
    val final_cmd = ref SKIP
    val new_states = ref ([]: state_int list) 
    val write_params = ref ([]: variable_t list)
    val transformed_normal_exit = ref false 

    method set_var = 
      match pc_to_instruction#get !current_pc with 
      |	Some stack_layout -> 
	  let set_tr_var_slot (slot: logical_stack_slot_int) = 
	    let orig_var = slot#get_variable in
	    let var = 
	      try (Option.get (stacks#get orig_var))#top 
	      with _ -> orig_var in
              (* var is not the final variable; 
               * (aliases#get_representative var) will be set later *)
	    slot#set_transformed_variable var in
	  List.iter set_tr_var_slot stack_layout#get_slots 
      |	_ -> () 


    method transformState (cfg:cfg_int) (state_name:symbol_t) = 
     let state = cfg#getState state_name in
      let code = state#getCode in
      let new_enter_cmd = 
	match code#getCmdAt 0 with (* This is the enter code *)
	| CODE (s, enter_code) -> 
            let new_enter_code = 
	      if state#getLabel = method_entry_sym then 
		JCHSystemUtils.add_cmds
                  ~cms
                  ~init_cmds:[!init_cmd]
                  ~final_cmds:[]
                  ~code:enter_code 
	      else if state#getLabel#getIndex = normal_exit_sym#getIndex then 
		let _ = transformed_normal_exit := true in
		JCHSystemUtils.add_cmds
                  ~cms
                  ~init_cmds:[]
                  ~final_cmds:[!final_cmd]
                  ~code:enter_code 
	      else 
		enter_code in
            CODE (s, new_enter_code) 
       | _ -> raise (JCH_failure (STR "CODE enter state expected")) in
      code#setCmdAt 0 new_enter_cmd ;
      new_states := state :: !new_states ;
     (try 
       current_pc := JCHSystemUtils.sym_to_pc state_name ;
       self#set_var ;
     with _ -> ()) ;
      let succs = state#getOutgoingEdges in 
      stacks#reset_num_assignments ;
      self#transformCode code ;
      let num_assignments = stacks#num_assignments in
      List.iter (self#replace_in_phi cfg state_name) succs ;
      begin
        if dominance#is_reachable state_name then 
	  let children = dominance#get_immediate_dominated_children state_name in
	  children#iter (self#transformState cfg)
        else 
          ()
      end ;
      stacks#pop num_assignments 

    method makeAssign isPre (v, t) = 
      match v#getType with
      | NUM_LOOP_COUNTER_TYPE
      | NUM_TMP_VAR_TYPE
      | NUM_VAR_TYPE -> 
	  if isPre then
            ASSIGN_NUM (t, NUM_VAR (self#transformVar v))
	  else
            ASSIGN_NUM (self#make_new_variable v,  NUM_VAR t) 
      | SYM_TMP_VAR_TYPE
      | SYM_VAR_TYPE -> 
	  if isPre then
            ASSIGN_SYM (t, SYM_VAR (self#transformVar v))
	  else
            ASSIGN_SYM (self#make_new_variable v, SYM_VAR t) 
      | STRUCT_TYPE _ -> 
	  if isPre then
            ASSIGN_STRUCT (t, self#transformVar v)
	  else
            ASSIGN_STRUCT (self#make_new_variable v, t) 
      | _ -> raise (JCH_failure (STR "SSA: var types not covered")) 

    method transformOtherOperation op = 
      let transformArg (s,v,m) =
	match m with 
	| READ -> 
	    (s, self#transformVar v, m)
	|  _ -> 
	    (s, self#make_new_variable v, m) in
      let new_args = List.map transformArg op.op_args in
      OPERATION { op_name = op.op_name; op_args = new_args } 

    method transformOperation op =
      let addReadAssigns assigns (s,v,m) =
	match m with
	| READ -> 
	    (self#makeAssign false (v, v)) :: assigns
	| _ -> 
	    assigns in

      let addWriteAssigns assigns (s,v,m) =
	if v#getIndex = exception_var_index 
	then 
	  assigns
	else
	  match m with
	  | WRITE -> 
	      (self#makeAssign true (v, v)) :: assigns
	  | _ -> assigns in      
      
      match op.op_name#getBaseName with
      |	"initialize" -> 
	  let read_assigns = List.fold_left addReadAssigns [] op.op_args in
	  CODE (initial_assigns_sym, self#mk_code read_assigns)
      |	"finalize" -> 
	  begin
	    try 
	      let write_assigns =
                List.fold_left addWriteAssigns [] op.op_args in
	      CODE (final_assigns_sym, self#mk_code write_assigns)
	    with
	    | _ ->
               (* The return variable was never assigned as in the case when 
                * the method just throws an exception *)               
	       ASSERT FALSE  
	  end
      |	"phi" -> 
	  let changeArg (s,v,m) = (s, self#make_new_variable v, m) in
	  let new_args =
            (changeArg (List.hd op.op_args)) :: (List.tl op.op_args) in
	  OPERATION { op_name = op.op_name ; op_args = new_args }
      |	"final_phi" -> 
	  let (_,v0,_) = List.hd op.op_args in
	  if (List.mem v0 !write_params) 
	  then 
	    let changeArg (s,v,m) = (s, self#make_new_variable v, m) in
	    let new_args =
              (changeArg (List.hd op.op_args)) :: (List.tl op.op_args) in
	    OPERATION { op_name = phi_sym ; op_args = new_args }
	  else SKIP
      |	"enter_final_state" -> OPERATION op 
      |	"dead_vars" -> SKIP
      |	"v" -> 
	  current_pc := op.op_name#getSeqNumber;
	  self#set_var ;
	  self#transformOtherOperation op 
      |	_ -> self#transformOtherOperation op 

    method set_write_vars cmd = 
      let addWriteVar vars (s,v,m) =
	match m with
	| WRITE -> v::vars
	| _ -> vars in
      match cmd with
      |	OPERATION op -> 
	  let write_vars = List.fold_left addWriteVar [] op.op_args in
	  write_params := write_vars 
      |	_ -> ()
 
    method transformVar var = 
      let index = var#getIndex in
      if index = exception_var_index
         || index = num_return_var_index
         || index = sym_return_var_index
         || var#getName#getBaseName.[0] = 'c' then
        var
      else 
	try 
	  let new_var = stacks#get_top var in
	  let table = 
	    match rvar_to_pc_to_versions#get var with 
	    | Some table -> table
	    | _ -> 
		let table = new IntCollections.table_t in
		rvar_to_pc_to_versions#set var table ;
		table in
	  (match table#get !current_pc with 
	  | Some set -> 
	      set#add new_var 
	  | _ -> table#set
                   !current_pc (VariableCollections.set_of_list [new_var])) ;
	  new_var
	with _ -> 
	  pr_debug [proc_name_pp proc_name; STR " "; proc_name#toPretty; 
		    STR " variable read before write ";
                    var#toPretty; STR " at pc = "; INT !current_pc; NL] ;
	  raise (JCH_failure (STR "failure in transformVar"))

    method make_new_variable var = 
      let index = var#getIndex in
      if index = exception_var_index
         || index = num_return_var_index
         || index = sym_return_var_index then
        var 
      else
        ssa_vars#make_new_variable var 

    method add_to_alias_sets v w = 
      let index = v#getIndex in
      if index = num_return_var_index || index = sym_return_var_index then
        ()
      else
        alias_sets#add v w

  val in_branch = ref 10
  val in_branch_var = ref (make_variable "branch_dummy" NUM_VAR_TYPE)

  method transformCmd cmd = 
    match cmd with
    | CFG (name, cfg) -> 
	let _ = self#transformState phi_cfg method_entry_sym in
        let _ = 
	  try 
	    let _ = phi_cfg#getState exceptional_exit_sym in
            (* taken out by the dominance functions *)            
	    self#transformState phi_cfg exceptional_exit_sym 
	  with _ -> () in 
	let _ = 
	  if !transformed_normal_exit then 
	    ()
	  else     (* The method never terminates *)      
	    let _ = self#transformState phi_cfg normal_exit_sym in 
	    let _ = self#transformState phi_cfg method_exit_sym in
	    () in
	let newCFG = F.mkCFG_s method_entry_sym method_exit_sym in
	let addState state = 
	  let is_reachable s =
            List.exists (fun st ->
                st#getLabel#getBaseName = s#getBaseName) !new_states in
	  let new_edges = List.filter is_reachable state#getIncomingEdges in
	  let new_state = F.mkState state#getLabel state#getCode in
	  let _ = 
	      List.iter new_state#addIncomingEdge new_edges in
	  let _  = 
	    List.iter new_state#addOutgoingEdge state#getOutgoingEdges in
	  newCFG#addState new_state in
	List.iter addState !new_states ;
	CFG (name, newCFG) 
    | CODE (str, code) -> 
	if str#getBaseName = "enter_final_state" && code#length > 0 
	then (
	  self#set_write_vars (code#getCmdAt (code#length - 1)) ;
	  self#transformCode code ;
	  CODE (enter_state_sym, code))
	else 
	  super#transformCmd cmd
    | TRANSACTION (str, code, copde_opt) -> 
	if str#getBaseName = "OpNewArray" then 
	  match code#getCmdAt 0 with 
	  | ASSIGN_NUM (length, _) -> 
	      let elements_field = new symbol_t "elements" in
	      let elements_path =
                List.rev (elements_field :: (List.tl (List.rev length#getPath))) in
	      let array_elements = 
		new variable_t
		  length#getName
		  ~suffix: length#getSuffix
		  ~path: elements_path
		  NUM_ARRAY_TYPE in
	      let _ = self#make_new_variable array_elements in
	      super#transformCmd cmd		
	  | _ -> 
	      super#transformCmd cmd
	else if code#length = 0 then
          super#transformCmd cmd
	else
	  begin
	    match code#getCmdAt 0 with
            (* this is taken as one source of information so one variable *)              
	    | BRANCH [c1; c0; c_1] ->  
		in_branch := 1 ;
		super#transformCode c1 ;
		in_branch := 0 ;
		super#transformCode c0 ;
		super#transformCode c_1 ;
		in_branch := 10 ;
		TRANSACTION (str, F.mkCode [BRANCH [c1; c0; c_1]], None)
	    | _ -> 
		super#transformCmd cmd
	  end
    | ABSTRACT_VARS l -> 
	ABSTRACT_VARS (List.map self#make_new_variable l)
    | ASSIGN_NUM (v, NUM_VAR v') -> 
	let new_v' = self#transformVar v' in
	let new_v = self#make_new_variable v in
	self#add_to_alias_sets new_v new_v';
	ASSIGN_NUM (new_v, NUM_VAR new_v')
    | ASSIGN_NUM (v, NUM c) -> 
	let new_v = 
	  if !in_branch = 1 then 
	    let v0 = self#make_new_variable v in
	    in_branch_var := v0 ;
	    v0
	  else if !in_branch = 0 then 
	    !in_branch_var
	  else (
	    let v0 = self#make_new_variable v in
	    alias_sets#add_const v0 c ;
	    v0) in
	ASSIGN_NUM (new_v, NUM c)
    | ASSIGN_NUM (v,e) -> 
	ASSIGN_NUM (self#make_new_variable v, self#transformNumExp e)
    | INCREMENT (v, num) -> 
	let new_temp = ssa_vars#make_new_temp v in 
	alias_sets#add_const new_temp num ;
	let newCode =
          [ASSIGN_NUM (new_temp, NUM num) ;
	   ASSIGN_NUM (self#make_new_variable v,
                       PLUS (self#transformVar v, new_temp))] in
	TRANSACTION (new symbol_t "increment", self#mk_code newCode, None)
    | ASSIGN_SYM (v,SYM_VAR v') -> 
	let new_v' = self#transformVar v' in
	let new_v = self#make_new_variable v in
	self#add_to_alias_sets new_v new_v';
	ASSIGN_SYM (new_v, SYM_VAR new_v')
    | ASSIGN_SYM (v,e) -> 
	let new_e = self#transformSymExp e in
	let new_v = self#make_new_variable v in
	ASSIGN_SYM (new_v, new_e)
    | ASSIGN_ARRAY (v, v') -> 
	let new_v' = self#transformVar v' in
	let new_v = self#make_new_variable v in
	self#add_to_alias_sets new_v new_v' ;
	ASSIGN_ARRAY (new_v, new_v')
    | ASSIGN_STRUCT (v,v') -> 
	let new_v' = self#transformVar v' in
	let new_v = self#make_new_variable v in
	self#add_to_alias_sets new_v new_v';
	ASSIGN_STRUCT (new_v, new_v') 
    | READ_NUM_ELT (x, a, i) -> 
	let new_a = self#transformVar a in
	let new_i = self#transformVar i in
	let new_x = self#make_new_variable x in
	READ_NUM_ELT (new_x, new_a, new_i)
    | READ_SYM_ELT (x, a, i) -> 
	let new_a = self#transformVar a in
	let new_i = self#transformVar i in
	let new_x = self#make_new_variable x in
	READ_SYM_ELT (new_x, new_a, new_i)
    | OPERATION op -> self#transformOperation op
    | _ -> super#transformCmd cmd 

    method transformProcedure (procedure: procedure_int) = 
      let bindings = procedure#getBindings in
      let signature = procedure#getSignature in
      let scope = procedure#getScope in
      let _ = ssa_vars#set_stacks stacks in
      let _ = ssa_vars#set_scope scope in
      let mkOpArg (sym,v) = 
	try
	  let (_,_,m) =
            List.find (fun (s,_,_) ->
                sym#getBaseName = s#getBaseName) signature in
	  (sym#getBaseName, v, m) 
	with
	| Not_found ->
	   raise
             (JCH_failure
                (LBLOCK [ STR "op arg " ; sym#toPretty ; STR " not found in " ;
			  STR "JCHSSA.transformProcedure" ])) in
      let op_args = List.map mkOpArg bindings in
      let _ =
        init_cmd := OPERATION {op_name = initialize_sym; op_args = op_args } in
      let _ =
        final_cmd := OPERATION {op_name = finalize_sym; op_args = op_args } in
      let body = procedure#getBody#clone () in 
      let _ = self#transformCode body in
      F.mkProcedure 
	procedure#getName 
	~signature: signature 
	~bindings: bindings
	~scope: scope
	~body: body 
      
end

let make_ssa procedure cfg dominance_info = 
  let proc_name = procedure#getName in
  let phi_cfg =
    (new ssa_phi_t
         ~procedure
         ~cfg
         ~dominance:dominance_info
         ~nr_states:dominance_info#get_nr_states)#mkPhi_cfg in
  let ssa_transformer =
    new ssa_transformer_t
        ~proc_name
        ~phi_cfg
        ~dominance:dominance_info in
  let new_proc = ssa_transformer#transformProcedure procedure in
  let alias_sets = ssa_transformer#get_alias_sets in
  let rvar_to_pc_to_versions = ssa_transformer#get_rvar_to_pc_to_versions in
  (new_proc, alias_sets, rvar_to_pc_to_versions) 
  

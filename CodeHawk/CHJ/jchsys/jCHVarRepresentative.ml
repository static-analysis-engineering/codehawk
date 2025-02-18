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
open CHPretty
open CHUtils

(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHIFSystem

(* jchsys *)
open JCHGlobals

module F = CHOnlineCodeSet.LanguageFactory


class bad_phi_collector_t system procedure =
  object (self: _)
    inherit code_walker_t as super

    val proc_name = procedure#getName
    val states =
      List.map (fun s ->
          s#getBaseName) (JCHSystemUtils.get_CFG procedure)#getStates
    val bad_vars = new VariableCollections.set_t
    val var_to_phis = new VariableCollections.table_t
    val phi_to_vars = new VariableCollections.table_t
    val vars_read = new VariableCollections.set_t
    (* The following catches the phi assignments as well:
     * read_vars_in_code procedure#getBody system *)

    method get_vars = bad_vars

    method private add_all_phis (bad_var:variable_t) =
      if bad_vars#has bad_var then ()
      else
	begin
	  bad_vars#add bad_var;
	  match var_to_phis#get bad_var with
	  | Some set -> set#iter self#add_all_phis
	  | None -> ()
	end

    method add_phi_info (phi_var:variable_t) (var:variable_t) =
      (match var_to_phis#get var with
      |	Some set -> set#add phi_var
      |	None ->
         var_to_phis#set var (VariableCollections.set_of_list [phi_var]));
      match phi_to_vars#get phi_var with
      |	Some set -> set#add var
      |	None ->
         phi_to_vars#set phi_var (VariableCollections.set_of_list [var]);

    method private check_phi (phi_var:variable_t) (vars:variable_t list) =
      let bad_var v =
	JCHSystemUtils.is_exception v
        || v#getName#getSeqNumber = -1
        || bad_vars#has v in
      if List.exists bad_var vars then
        self#add_all_phis phi_var
      else
        List.iter (self#add_phi_info phi_var) vars

    method !walkCmd (cmd:(code_int, cfg_int) command_t) =
      match cmd with
      |	CFG (_, cfg) ->
         List.iter (fun s ->
             self#walkCode (cfg#getState s)#getCode) cfg#getStates
      |	CODE (_, code) -> super#walkCode code
      |	OPERATION op ->
	  begin match op.op_name#getBaseName with
	  | "phi" ->
	     let phi_var =
               List.hd (JCHSystemUtils.get_write_vars op.op_args) in
	      let args_in_cfg =
                List.filter (fun (s,_,_) -> List.mem s states) op.op_args in
	      let vars = JCHSystemUtils.get_read_vars args_in_cfg in
	      self#check_phi phi_var vars
	  | _ ->
	      let read_vars = JCHSystemUtils.get_read_vars op.op_args in
	      vars_read#addList read_vars;
	      super#walkCmd cmd
	  end
      |	_ ->
	  let collector = new read_vars_collector_t system in
	  collector#walkCmd cmd;
	  let read_vars = collector#getVars in
	  vars_read#addList read_vars;
	  super#walkCmd cmd

    method get_unread =
      let last_phis =
        VariableCollections.set_of_list phi_to_vars#listOfKeys in
      last_phis#removeList var_to_phis#listOfKeys;
      let done_vars = new VariableCollections.set_t in
      let rec work vars =
	match vars with
	| var :: rest_vars ->
	    if done_vars#has var then work rest_vars
	    else if JCHSystemUtils.is_return var || vars_read#has var then
	      begin
		done_vars#add var;
		work rest_vars
	      end
	    else
	      begin
		done_vars#add var;
		let vars =
		  match phi_to_vars#get var with
		  | Some vars -> vars#toList
		  | None -> [] in
		if vars = [] then work rest_vars
		else
		  begin
		    bad_vars#add var;
		    let phis =
		      match var_to_phis#get var with
		      | Some set -> set#toList
		      | _ -> [] in
		    if phis = [] then
		      let remove_phi res v =
			let set = Option.get (var_to_phis#get v) in
			set#remove var;
			if set#isEmpty then v :: res
			else res in
		      let new_last_vars = List.fold_left remove_phi [] vars in
		      work (new_last_vars @ rest_vars)
		    else work rest_vars
		  end
	      end
	| _ -> () in
      work last_phis#toList
    method walkProcedure (proc: procedure_int) =
      self#walkCode proc#getBody;
      self#get_unread;

  end

(* Substitutes the variables by a representative of the class of aliases.
 * Eliminates the assignment between aliased variables
 * Eliminates the phi operations that are not completely determined,
 * that is have variables that are not assigned on some path.
 * (Java does not have unassigned variables)
 * It creates subst_tables for the parameters to be used by the
 * cleanup transformer *)
class rep_transformer_t
        (system:system_int) (aliases:JCHTransformUtils.alias_sets_t) =
  object (self: _)

    inherit JCHCodeTransformers.variable_transformer_t as super

    val states = ref ([]: string list)
    val new_states = ref ([]: state_int list)

    val init_cmd = ref SKIP

    val variables = new VariableCollections.set_t

    val subst_table = ref (new VariableCollections.table_t)

    val returnVar = ref None

    val cms_opt = ref None

    (* phi variable to vars it depends on before aliasing *)
    val orig_phi_vars = new VariableCollections.table_t

    method get_subst_table = !subst_table
    method get_return_var = !returnVar
    method get_orig_phi_vars = orig_phi_vars

    method !transformVar (var:variable_t) =
      if JCHSystemUtils.is_exception var then
	begin
	  variables#add exception_var;
	  exception_var
	end
      else if JCHSystemUtils.is_return var then
	begin
	  variables#add var;
	  var
	end
      else
	let new_v =
	  match aliases#get_representative var with
	  | Some v -> v
	  | None -> var in
	variables#add new_v;
	new_v

    method private has_no_rep (var:variable_t) =
      if JCHSystemUtils.is_exception var || JCHSystemUtils.is_return var then
        true
      else
	match aliases#get_representative var with
	| Some _ -> false
	| None -> true

    val phi_vars_to_remove = ref (new VariableCollections.set_t)

    method transformOperation (op:operation_t) =
      match op.op_name#getBaseName with
      | "phi" ->
	  let (_,phi_var,_) = List.hd op.op_args in
	  if !phi_vars_to_remove#has phi_var then
	    SKIP
	  else
	    let changeArg (s,v,m) = (s, self#transformVar v, m) in
	    let reach_args =
              List.filter (fun (s,_,m) ->
                  m = WRITE || List.mem s !states) op.op_args in
	    orig_phi_vars#set
              phi_var
              (VariableCollections.set_of_list
                 (List.map (fun (_,v,_) -> v) reach_args));
	    let new_args = List.map changeArg reach_args in
	    OPERATION {op_name = op.op_name; op_args = new_args }
      |	_ ->
	  let changeArg (s,v,m) = (s,self#transformVar v, m) in
	  let new_args = List.map changeArg op.op_args in
	  OPERATION {op_name = op.op_name; op_args = new_args }

    val visitedStates = new SymbolCollections.set_t

    method transformState (cfg:cfg_int) (state_name:symbol_t) =
      if visitedStates#has state_name then
	()
      else
	begin
	  let state = cfg#getState state_name in
	  self#transformCode state#getCode;
	  let succs = state#getOutgoingEdges in
	  visitedStates#add state_name;
	  List.iter (self#transformState cfg) succs
	end

    method private add_subst_table ~(is_initial:bool) ~(code:code_int) =
      let add_subst_table_cmd cmd =
	match cmd with
	| ASSIGN_NUM (v1, NUM_VAR v2)
	| ASSIGN_SYM (v1, SYM_VAR v2)
	| ASSIGN_ARRAY (v1, v2)
	| ASSIGN_STRUCT (v1, v2) ->
	    if is_initial then
	      !subst_table#set v1 v2
	    else
	      !subst_table#set v2 v1
	| _ -> () in
	for i = 0 to code#length - 1 do
	  add_subst_table_cmd (code#getCmdAt i)
	done

    method private mk_code (cmds:(code_int,cfg_int) command_t list) =
      chif_system#make_code (Option.get !cms_opt) cmds

    method !transformCmd cmd =
      match cmd with
      |	CODE (sym, code) ->
	  self#transformCode code;
	  if sym = initial_assigns_sym then
	    begin
	      self#add_subst_table ~is_initial:true ~code;
	      cmd
	    end
	  else if sym = final_assigns_sym then
	    begin
	      self#add_subst_table ~is_initial:false ~code;
	      cmd
	    end
	  else
	    cmd
      | CFG (_s, cfg) ->
	  states := List.map (fun s -> s#getBaseName) cfg#getStates;
	  self#transformState cfg cfg#getEntry#getLabel;
	  cmd
      | ASSIGN_NUM (v, NUM_VAR v') ->
	  if (self#has_no_rep v) || (self#has_no_rep v')
	  then
	    ASSIGN_NUM (self#transformVar v ,
			NUM_VAR (self#transformVar v'))
	  else SKIP
      |	ASSIGN_NUM (v, NUM c) ->
	  let rep_v = self#transformVar v in
	  if rep_v#getName#getBaseName.[0] = 'c' then
	    SKIP
	  else
	    ASSIGN_NUM (rep_v, NUM c)
      | ASSIGN_SYM (v,SYM_VAR v') ->
	  if (self#has_no_rep v) || (self#has_no_rep v')
	  then
	    ASSIGN_SYM (self#transformVar v,
			SYM_VAR (self#transformVar v'))
	  else SKIP
      | ASSIGN_STRUCT (v,v') ->
	  if (self#has_no_rep v) || (self#has_no_rep v')
	  then
	    ASSIGN_STRUCT (self#transformVar v,
			   self#transformVar v')
	  else SKIP
      | OPERATION op ->
	    self#transformOperation op
      | _ -> super#transformCmd cmd

    method !transformProcedure (procedure: procedure_int) =
      subst_table := new VariableCollections.table_t;
      cms_opt := Some (retrieve_cms procedure#getName#getSeqNumber);
      let scope = F.mkScope () in
      let collector = (new bad_phi_collector_t system procedure) in
      collector#walkProcedure procedure;
      phi_vars_to_remove := collector#get_vars;
      let body = procedure#getBody in
      self#transformCode body;
      scope#addVariables variables#toList;
      returnVar := None;
      let changeBind (s, v) =
	if s#getBaseName = "return" then
	  returnVar := Some v;
	(s, self#transformVar v) in
      let bindings = List.map changeBind procedure#getBindings in
      let signature = procedure#getSignature in
      F.mkProcedure
	procedure#getName
	~signature: signature
	~bindings: bindings
	~scope: scope
	~body: body

end

(* Transforms the SSA CHIF back to regular CHIF by subtituting phi
 * operations with one ASSIGN for each of the previous states
 * Also adds unnecessary phi_vars to subst_table *)
class phi_remover_t (subst_table:variable_t VariableCollections.table_t) =
    object (self: _)

      (* Symbol and not Symbol because of get, see below *)
      val assign_table = new SymbolCollections.table_t

      val cms_opt = ref None
      val rev_subst_table = new VariableCollections.table_t
      val var_to_phi_vars = new VariableCollections.table_t
      val phi_var_to_vars = new VariableCollections.table_t

      method private mk_code (cmds:(code_int,cfg_int) command_t list) =
        chif_system#make_code (Option.get !cms_opt) cmds

      method private get_rep (v:variable_t) =
	match subst_table#get v with
	| Some w -> w
	| None -> v

      method private add_redundant_phi (phiv:variable_t) (v:variable_t) =
	let check_other_phi (_v': variable_t) (phiv': variable_t) =
	  match phi_var_to_vars#get phiv' with
	  | Some set ->
	      let reps =
		let vars = new VariableCollections.set_t in
		let add_rep v = vars#add (self#get_rep v) in
		set#iter add_rep;
		vars in
	      let rep_list = reps#toList in
	      if List.length rep_list = 1 then
		begin
		  phi_var_to_vars#remove phiv';
		  self#add_redundant_phi phiv' (List.hd rep_list)
		end
	      else ()
	  | None -> () in
	let rec add_to_tables (v1:variable_t) (v2:variable_t) =
	  let change_subst (v1:variable_t) (v2:variable_t) =
	    subst_table#set v1 v2;
	    (match rev_subst_table#get v2 with
	    | Some set -> set#add v1
	    | None ->
               rev_subst_table#set v2 (VariableCollections.set_of_list [v1]) );
	    match rev_subst_table#get v1 with
	    | Some set ->
		rev_subst_table#remove v1;
		set#iter (fun w -> add_to_tables w v2)
	    | None -> () in
	  match subst_table#get v1 with
	  | Some x ->
	      if x#equal v2 then ()
	      else change_subst v1 v2
	  | None -> change_subst v1 v2 in
	let rep =
	  match subst_table#get v with
	  | Some w -> w
	  | None -> v in
	add_to_tables phiv rep;
	(match rev_subst_table#get phiv with
	| Some set -> set#iter (fun s -> add_to_tables s rep)
	| None -> ());
	(match var_to_phi_vars#get phiv with
	  | Some set -> set#iter (check_other_phi phiv)
	  | None -> ())


      method private find_redundant_phis (cfg: cfg_int) =
	let find_redundant_phis_cmd (cmd:(code_int,cfg_int) command_t) =
	  match cmd with
	  | OPERATION op ->
	      if op.op_name#getBaseName = "phi" then
		let (_, phiv, _) = List.hd op.op_args in
		let read_var_reps =
		  let vars = new VariableCollections.set_t in
		  let add_arg (_s, v, _m) =
		    let rep_v = self#get_rep v in
		    vars#add rep_v in
		  List.iter add_arg (List.tl op.op_args);
		  vars in
		let read_var_rep_list = read_var_reps#toList in
		if List.length read_var_rep_list = 1 then
		  self#add_redundant_phi phiv (List.hd read_var_rep_list)
		else
		  let add_var v =
		    (match var_to_phi_vars#get v with
		    | Some set -> set#add phiv
		    | None ->
                       var_to_phi_vars#set
                         v (VariableCollections.set_of_list [phiv]));
		    phi_var_to_vars#set phiv read_var_reps in
		  List.iter add_var read_var_rep_list
	      else ()
	  | _ -> () in
	let find_redundant_phis_state (state_name:symbol_t) =
	  let state = cfg#getState state_name in
	  match state#getCode#getCmdAt 0 with
	  | CODE (_, enter_code) ->
	      for i = 0 to enter_code#length - 1 do
		find_redundant_phis_cmd (enter_code#getCmdAt i)
	      done
	  | _ -> raise (JCH_failure (STR "Code enter_state expected")) in
	List.iter find_redundant_phis_state cfg#getStates

      method private collect_assigns (cfg: cfg_int)  =
	let addTable s =
          assign_table#set s (new VariableCollections.table_t) in
	let _ = List.iter addTable (cfg#getStates) in
	let collect_assigns_cmd cmd =
	  match cmd with
	  | OPERATION op ->
	      if op.op_name#getBaseName = "phi" then
		let (_, phiv, _) = List.hd op.op_args in
		let read_var_reps =
		  let vars = new VariableCollections.set_t in
		  let add_arg (_s, v, _m) =
		    let rep_v = self#get_rep v in
		    vars#add rep_v in
		    List.iter add_arg (List.tl op.op_args);
		  vars#toList in
		if List.length read_var_reps = 1 then SKIP
		else
		  begin
		    let collect_assign_arg (prev, v, _) =
		      let prev_sym = new symbol_t prev in
		      match  assign_table#get prev_sym with
		      | Some table -> table#set phiv (self#get_rep v)
                      (* It's possible that the state is not reachable *)
		      | None -> () in
		    List.iter collect_assign_arg (List.tl op.op_args);
		    SKIP
		  end
	      else cmd
	  | _ -> cmd in
	let collect_assigns_state (state_name:symbol_t) =
	  let state = cfg#getState state_name in
	  match state#getCode#getCmdAt 0 with
	  | CODE (_, enter_code) ->
	      for i = 0 to enter_code#length - 1 do
		let new_cmd = collect_assigns_cmd (enter_code#getCmdAt i) in
		enter_code#setCmdAt i new_cmd
	      done
	  | _ -> raise (JCH_failure (STR "Code enter_state expected")) in
	List.iter collect_assigns_state cfg#getStates

    method private make_assign (phiv:variable_t) (v:variable_t) =
      match v#getType with
      | NUM_LOOP_COUNTER_TYPE
      | NUM_TMP_VAR_TYPE
      | NUM_VAR_TYPE ->
	  ASSIGN_NUM (phiv,  NUM_VAR v)
      | SYM_TMP_VAR_TYPE
      | SYM_VAR_TYPE ->
	  ASSIGN_SYM (phiv, SYM_VAR v)
      | STRUCT_TYPE _ ->
	  ASSIGN_STRUCT (phiv, v)
      | _ -> raise (JCH_failure (STR "phi removal: var types not covered"))

      method private put_assigns (cfg: cfg_int) =
	let exit_cmd = OPERATION ({op_name = exit_sym; op_args = []}) in
	let put_assigns_state state_name =
	  let state_table = Option.get (assign_table#get state_name) in
	  let state = cfg#getState state_name in
	  let state_code = state#getCode in
	  let new_cmds =
            ref (if state#getLabel#getBaseName = "normal-exit" then [
                     exit_cmd]
                 else
                   []) in
	  match state_code#getCmdAt (state_code#length - 1) with
	  | CODE (nm, exit_code) ->
	      let _ =
		for i = exit_code#length -1 downto 0 do
		  new_cmds := (exit_code#getCmdAt i) :: (!new_cmds)
		done  in
	      let put_assign_var (phiv:variable_t) =
		let v = Option.get (state_table#get phiv) in
		new_cmds := (self#make_assign phiv v) :: (!new_cmds) in
	      List.iter put_assign_var state_table#listOfKeys;
	      state_code#setCmdAt (state_code#length - 1)
		(CODE (nm, (self#mk_code !new_cmds)))
	  | _ -> raise (JCH_failure (STR "CODE exit_code expected"))
	in
	List.iter put_assigns_state cfg#getStates

      method transformProcedure (procedure: procedure_int) =
	let cfg = JCHSystemUtils.get_CFG procedure in
	cms_opt := Some (retrieve_cms procedure#getName#getSeqNumber);
	self#find_redundant_phis cfg;
	self#collect_assigns cfg;
	self#put_assigns cfg
    end

(* Substitutes variables for parameters wherever appropriate.
 * Eliminates SKIP commands, introduced OPERATIONS that are not
 * needed anymore and empty CODE that is not needed *)
class cleanup_transformer_t
        ~(transformed_system:system_int)
        ~(subst_table:variable_t VariableCollections.table_t)
        ~(returnVar:variable_t option) =
  object (self: _)

    inherit JCHCodeTransformers.variable_transformer_t as super

    val readVars = ref []
    val cms_opt = ref None

    method !transformVar (v:variable_t):variable_t =
      match subst_table#get v with
      |	Some v1 -> v1
      |	None ->
	  if v#getName#getBaseName = "return" then
	    let returnV = Option.get returnVar in
	    let _ = subst_table#set v returnV in
	    returnV
	  else
	    v

    method private mk_code (cmds:(code_int,cfg_int) command_t list) =
      chif_system#make_code (Option.get !cms_opt) cmds

    method transform_code (code:code_int) =
      let new_cmds = ref [] in
      for i = 0 to code#length - 1 do
	begin
	  let new_cmd = self#transformCmd (code#getCmdAt i) in
	  if new_cmd = SKIP
	  then ()
	  else new_cmds := new_cmd :: (!new_cmds)
	end
      done;
      self#mk_code (List.rev !new_cmds)

    method transformState (cfg:cfg_int) (state_name:symbol_t) =
      let state = cfg#getState state_name in
      let new_code = self#transform_code state#getCode in
      JCHTransformUtils.mk_state state new_code

    method transformOp
             (t:variable_t)
             (v1:variable_t)
             {op_name = opname; op_args = opargs} =
      let transformArg (s,v,m) =
	if v = t then (s,v1,m)
	else (s,self#transformVar v,m) in
      {op_name = opname; op_args = List.map transformArg opargs }

    method !transformCmd (cmd:(code_int,cfg_int) command_t) =
      match cmd with
      |	CODE (s, code) ->
	  begin
	    match s#getBaseName with
	    | "initial_assigns"
	    | "final_assigns" ->
		SKIP
	    | _ ->
		CODE (s, self#transform_code code)
	  end
      | CFG (s, cfg) ->
	  let new_states = List.map (self#transformState cfg) cfg#getStates in
	  let new_cfg = F.mkCFG cfg#getEntry cfg#getExit in
	  let _ = new_cfg#addStates new_states in
	  CFG (s, new_cfg)
      |	TRANSACTION (s, code, code_opt) ->
	  let new_code = self#transform_code code in
	  let new_code_opt =
	    match code_opt with
	    | Some c -> Some (self#transform_code c)
	    | None -> None in
	  if (Option.is_none new_code_opt) then
	    if new_code#length = 0 then
	      SKIP
	    else if new_code#length = 1 then
	      begin
		new_code#getCmdAt 0
	      end
	    else
	      TRANSACTION (s, new_code, None)
	  else
	    TRANSACTION (s, new_code, new_code_opt)
      |	RELATION code ->
	  RELATION (self#transform_code code)
      |	_ ->
	  let new_cmd = super#transformCmd cmd in
	  match new_cmd with
	  | ASSIGN_NUM (v1, NUM_VAR v2)
	  | ASSIGN_SYM (v1, SYM_VAR v2)
	  | ASSIGN_ARRAY (v1, v2)
	  | ASSIGN_STRUCT (v1, v2) ->
	      if v1#getIndex = v2#getIndex then
		SKIP
	      else
		new_cmd
	  | _ -> new_cmd

    method !transformProcedure (procedure: procedure_int) =
      let body = procedure#getBody in
      let scope = procedure#getScope in
      readVars := read_vars_in_code body transformed_system;
      cms_opt := Some (retrieve_cms procedure#getName#getSeqNumber);
      self#transformCode body;
      scope#removeVariables subst_table#listOfKeys;
      scope#addVariables subst_table#listOfValues;
      procedure

  end

let reduce_to_rep
      ~(system:system_int)
      ~(proc:procedure_int)
      ~(aliases: JCHTransformUtils.alias_sets_t) =
  let rep_transformer = new rep_transformer_t system aliases in
  let new_proc = rep_transformer#transformProcedure proc in
  let subst_table = rep_transformer#get_subst_table in
  let returnVar = rep_transformer#get_return_var in
  (new phi_remover_t subst_table)#transformProcedure new_proc;
  let _ =   (* cleanup also added returns to the subst table  *)
    (new cleanup_transformer_t
         ~transformed_system:system
         ~subst_table
         ~returnVar)#transformProcedure new_proc in
  aliases#change_representative subst_table;
  (aliases, rep_transformer#get_orig_phi_vars, new_proc)

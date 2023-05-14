(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny Sipma

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
open CHIterator
open CHLanguage
open CHNumerical
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

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

module F = CHOnlineCodeSet.LanguageFactory

(* File contains transformations of the initial system that are 
 * necessary for the taint analysis:
 *  - adding an operation at the beginning to set the parameters of the
 *       method as dependent upon themselves
 *  - adding operations after ASSERTs to check, in case this is a condition 
 *       for a loop,
 *    whether its variables are tainted and therefore to signal that the 
 *       variables assigned in the loop
 *    must be tainted
 *    Info on the loop is also collected (needed for the final report)
 *  - adding operations after newArray to collect info for result reporting. *)

let dbg = ref false 

(* Returns an OPERATION which is used to initialize the input values *)
let make_init_params_ops (proc: procedure_int)  = 
  let bindings = proc#getBindings in
  let signature = proc#getSignature in
  let input_vars = JCHIFUtil.get_input_vars bindings signature in
  let proc_name_var = new variable_t proc#getName SYM_VAR_TYPE in
  let input_args = List.map (fun v -> ("arg", v, WRITE)) input_vars in 
  let args = 
    match JCHSystemUtils.get_return_var proc with 
    | Some r ->
       ("proc_name", proc_name_var, READ) :: ("return", r, READ) :: input_args 
    | None -> ("proc_name", proc_name_var, READ) :: input_args in 
  [OPERATION ({ op_name = init_params_sym ; op_args = args }) ;
    OPERATION { op_name = save_interval_sym; op_args = [] }] 

(* Returns an OPERATION which is used to produce the return values *)
let make_exit_op (proc: procedure_int)  = 
  OPERATION ({ op_name = exit_sym ; op_args = []}) 

(* Adds code to the beginning of the procedure
 * to initialize the domain for the input variable and
 * adds code to the end of each procedure to produce the exit domain *)
let add_pre_post_ops (procedure:procedure_int) =
  let proc_name = procedure#getName in
  let cms = retrieve_cms proc_name#getSeqNumber in
  let cfg = JCHSystemUtils.get_CFG procedure in
  begin
    let entry_code = cfg#getEntry#getCode in
    (match entry_code#getCmdAt 0 with
    | CODE (s, initialize_code) -> 
       let init_cmds = 
	 make_init_params_ops procedure in
       let new_initialize_code = 
	 JCHSystemUtils.add_cmds
           ~cms
           ~init_cmds
           ~final_cmds:[]
           ~code:initialize_code in
       entry_code#setCmdAt 0 (CODE (s, new_initialize_code)) 
    | _ -> 
       begin
	 pr_debug [STR "add_pre_post_ops expected CODE initialize"; NL];
	 raise (JCH_failure (STR "add_pre_post_op: expected CODE initialize")) 	    
       end) ;
    (try
       let normal_exit_state = 
	 let exits = cfg#getExit#getIncomingEdges in
	 let normal_exits = 
	   List.filter (fun n -> n#getBaseName = "normal-exit") exits in
	 cfg#getState (List.hd normal_exits) in
       let code = normal_exit_state#getCode in
       match code#getCmdAt (code#length - 1) with
       | CODE (_, exit_code) -> 
	  exit_code#setCmdAt (exit_code#length - 1) (make_exit_op procedure)
       | _ -> 
	  begin
	    pr_debug [STR "add_pre_post_ops: expected OPERATION exit"; NL];
	    raise (JCH_failure (STR "add_pre_post_op: expected OPERATION exit")) 
	  end
     with _ -> ())
  end

(* Transforms the code by adding an
 *   - OPERATION "new_array" after each OpNewArray
 *   - loop counters, states to initialize them and counters to increment 
 *   - ASSERTS to connect cmpl / fcmpl / ... followed by IfGe / ... 
 *   - operation for lengths of arrays: initialize, and assert ops 
 * It also sets proc_to_string_const_to_opname to be used by dynamic analysis *)
class op_transformer_t (proc:procedure_int) wto_infos = 
object (self: _)

  inherit code_transformer_t as super
    
  val proc_name = proc#getName;
  val cms = retrieve_cms proc#getName#getSeqNumber;

  val new_entry = ref None
  val new_states = ref [] 
  val new_edges = ref []
  val wto_heads = ref [] 
  val cmpl_var_to_op = new VariableCollections.table_t
  val ifjmp_var_to_state = new VariableCollections.table_t
  val state_name = ref state_name_sym
  val cfg_opt = ref None 
  val dbg = ref false 
  val assert_var_to_states = new VariableCollections.table_t

  method get_assert_var_to_states = assert_var_to_states

  method private add_edges (states1:symbol_t list) (states2:symbol_t list) = 
    let add_edge (s1:symbol_t) (s2:symbol_t) = 
      new_edges := (s1, s2) :: !new_edges in
    List.iter (fun s1 -> List.iter (add_edge s1) states2) states1 

  method private add_loop_var
                   (scope:scope_int) (cfg:cfg_int) (wto:JCHLoopUtils.wto_info_t) = 
    let loop_var = wto#get_var in
    let _ = scope#addVariable loop_var in 
    let get_state (state_name:symbol_t) = 
      let state_index = state_name#getIndex in
      try
        List.find (fun s -> s#getLabel#getIndex = state_index) !new_states 
      with _ -> cfg#getState state_name in
    let wto_head_name = wto#get_name in 
    let wto_head = get_state wto_head_name in
    let _ = wto_heads := wto_head :: !wto_heads in
    let init_state_name = 
      new symbol_t ("loop_counter_init_" ^ wto_head_name#getBaseName) in
    let save_lp_int_op =
      OPERATION { op_name = save_interval_sym;
                  op_args = [("val", loop_var, READ)] } in
    let mkCode cmds = JCHIFSystem.chif_system#make_code cms cmds in
    let init_code = 
      mkCode
	[CODE (enter_state_sym, mkCode []); 
	  ASSIGN_NUM (loop_var, NUM numerical_zero);
	  save_lp_int_op ;
	  CODE (exit_state_sym, mkCode [])] in
    let init_state = F.mkState init_state_name init_code in
    let _ = 
      if wto_head_name#equal cfg#getEntry#getLabel then 
	new_entry := Some init_state
      else
        () in
    new_states := init_state :: !new_states ;
    let new_code = 
      let code = wto_head#getCode in
      match code#getCmdAt 0 with 
      | CODE (s, entry_code) -> 
	  let lcheck_opname = 
	    new symbol_t
                ~atts: ("check_loop" :: wto_head_name#getSymbol)
                "check_loop" in
	  let new_entry_code = 
	    JCHSystemUtils.add_cmds
              ~cms
              ~init_cmds:[] 
	      ~final_cmds:[ INCREMENT (loop_var, numerical_one);
                            save_lp_int_op ;
	                    OPERATION {op_name = lcheck_opname;
                                       op_args = []} ] 
	      ~code:entry_code in
	  let _ = code#setCmdAt 0 (CODE (s, new_entry_code)) in
	  code 
      | _ -> 
	  begin
	    pr_debug [STR "add_pre_post_op: expected CODE initialize"; NL] ;
	    raise (JCH_failure (STR "add_pre_post_op: expected CODE initialize")) 
	  end in
    let new_wto_head = F.mkState wto_head_name new_code in 
    let _ = new_states := new_wto_head :: !new_states in 
    let prev_states = wto_head#getIncomingEdges in
    let wto_states = wto#get_states in 
    let inWTO st = List.exists (fun s-> s#getBaseName = st#getBaseName) wto_states in 
    let (prev_in, prev_out) = List.partition inWTO prev_states in

    let change_prev (prev_state_name:symbol_t) = 
      let prev_state = get_state prev_state_name in
      let new_prev_state = F.mkState prev_state_name prev_state#getCode in
      let other_out =
        List.filter (fun s -> s <> wto_head_name) prev_state#getOutgoingEdges in
      begin
        new_states := new_prev_state :: !new_states ;
        self#add_edges [prev_state_name] [init_state_name] ;
        self#add_edges [prev_state_name] other_out ;
        List.iter new_prev_state#addIncomingEdge prev_state#getIncomingEdges
      end in

    List.iter change_prev prev_out ;
    self#add_edges prev_in [wto_head_name] ;
    self#add_edges [init_state_name] [wto_head_name] ;

    let add_loop_exit loop_exit = 
      let loop_exit_state = get_state loop_exit in 
      let code = loop_exit_state#getCode in
      match code#getCmdAt (code#length - 1) with 
      | CODE (s, entry_code) -> 
	  let exit_loop_op = 
	    OPERATION 
	       {op_name = exit_loop_sym; 
		 op_args = [("loop_counter", loop_var, READ)]} in
	  let new_entry_code =
            JCHSystemUtils.add_cmds
              ~cms ~init_cmds:[exit_loop_op] ~final_cmds:[] ~code:entry_code in
	  code#setCmdAt (code#length - 1) (CODE (s, new_entry_code))
      | _ -> 
	  begin
	    pr_debug [STR "add_pre_post_op: expected CODE initialize"; NL] ;
	    raise
              (JCH_failure (STR "add_pre_post_op: expected CODE initialize")) 
	  end in
    List.iter add_loop_exit wto#get_exit_conds 

  method private add_wto_head_outgoing (new_cfg:cfg_int) (wto_head:state_int) = 
    let out = wto_head#getOutgoingEdges in  
    let label = wto_head#getLabel in
    let index = label#getIndex in
    let new_wto_head = new_cfg#getState label in
    let add_out_edge state_name = 
      let state_index = state_name#getIndex in
      if List.exists
           (fun whead -> whead#getLabel#getIndex = state_index) !wto_heads  then 
	let wto_info = 
	  List.find (fun wto -> wto#get_name#getIndex = index) wto_infos in
	let states = wto_info#get_states in 
	if List.exists (fun s -> s#getIndex = state_index) states then
          ()  (* The edge from this wto head to the state that initializes 
               * the loop with head state *)
	else
          new_wto_head#addOutgoingEdge state_name 
      else
        new_wto_head#addOutgoingEdge state_name in
    List.iter add_out_edge out 

  method private add_loop_vars_cfg (cfg:cfg_int) = 
    let scope = proc#getScope in
    let _ = new_entry := Some cfg#getEntry in
    let _ = List.iter (self#add_loop_var scope cfg) wto_infos in
    let new_cfg = F.mkCFG (Option.get !new_entry) cfg#getExit in 
    let addCFGState (state_name:symbol_t) = 
      let state_index = state_name#getIndex in
      if List.exists
           (fun s -> s#getLabel#getIndex = state_index) !new_states then
        ()
      else
        new_cfg#addState (cfg#getState state_name) in
    let add_new_edge (s1, s2) = new_cfg#addEdge s1 s2 in
    begin
      new_cfg#addStates !new_states ;
      List.iter addCFGState cfg#getStates ;
      List.iter add_new_edge !new_edges ;
      List.iter (self#add_wto_head_outgoing new_cfg) !wto_heads;
      new_cfg
    end

  method private transformState (cfg:cfg_int) (name:symbol_t) =
    begin
      state_name := name ;
      let state = cfg#getState name in
      self#transformCode (state#getCode) 
    end
    
  method transformCmd cmd = 
    match cmd with
    | CFG (s, cfg) ->
       begin
	 cfg_opt := Some cfg ;
	 List.iter (self#transformState cfg) cfg#getStates ;
	 CFG (s, self#add_loop_vars_cfg cfg)
       end
    | TRANSACTION (s, _, _) -> 
       if s#getBaseName = "assumptions" then
         SKIP
       else
         cmd (* REMOVE if these are not added anymore *)
    | OPERATION op ->
	begin
	  match op.op_name#getBaseName with 
	  | "i" 
	  | "ii" -> 
	      begin
		let mInfo =
                  app#get_method (retrieve_cms proc_name#getSeqNumber) in
		let pc = op.op_name#getSeqNumber in
		match mInfo#get_opcode pc with 
		| OpCmpL 
		| OpCmpFL
		| OpCmpFG
		| OpCmpDL
		| OpCmpDG -> 
		    begin
		      let dst = JCHSystemUtils.get_arg_var "dst1" op.op_args in
		      cmpl_var_to_op#set dst (new pretty_op_t op) ;
		      match ifjmp_var_to_state#get dst with 
		      |	Some name_set -> 
			 let current_state_name = !state_name in
                         begin
			   name_set#iter
                             (self#transformState (Option.get !cfg_opt)) ;
			   state_name := current_state_name ;
			   cmd
                         end
		      |	None -> cmd
		    end
		| _ -> super#transformCmd cmd
	      end
	  | _ -> super#transformCmd cmd
	end
    | _ -> super#transformCmd cmd 

  (* adds src1 = src2 for cmpl followed by ifeq , etc. *)
  method private get_branch_asserts
                   (is_inverted:bool) (opcode:opcode_t) (arg:variable_t) = 
    let mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber) in
    let assert_cmd = 
      match cmpl_var_to_op#get arg with 
      |  Some pp_op -> 
	  begin
	    let op = pp_op#op in
	    let pc = op.op_name#getSeqNumber in
	    let opcode1 = mInfo#get_opcode pc in
	    match opcode1 with 
	    | OpCmpL 
	    | OpCmpFL
	    | OpCmpFG
	    | OpCmpDL
	    | OpCmpDG ->
		begin
		  let src1 = JCHSystemUtils.get_arg_var "src1" op.op_args in
		  let src2 = JCHSystemUtils.get_arg_var "src2" op.op_args in
		  match (opcode, is_inverted) with 
		  | (OpIfNe _, true)
		  | (OpIfEq _, false) -> Some (ASSERT (EQ (src1, src2)))
		  | (OpIfEq _, true)
		  | (OpIfNe _, false) -> Some (ASSERT (NEQ (src1, src2)))
                  | (OpIfGe _, true)
		  | (OpIfLt _, false) -> Some (ASSERT (LT (src1, src2)))
		  | (OpIfLt _, true)
		  | (OpIfGe _, false) -> Some (ASSERT (GEQ (src1, src2)))
		  | (OpIfLe _, true)
		  | (OpIfGt _, false) -> Some (ASSERT (GT (src1, src2)))
		  | (OpIfGt _, true)
		  | (OpIfLe _, false) -> Some (ASSERT (LEQ (src1, src2)))
		  | _ -> None
		end
	    | _ -> None
	  end
      |	_ -> 
	  begin
	    match ifjmp_var_to_state#get arg with
	    | Some set -> set#add !state_name 
	    | None ->
               ifjmp_var_to_state#set
                 arg (SymbolCollections.set_of_list [!state_name]) 
	  end ;
	  None in
    assert_cmd 
	  
  method transformCode (code:code_int) = 
    for i = 0 to code#length - 2 do 
      let cmd = code#getCmdAt i in 
      match (cmd, code#getCmdAt (succ i)) with 
      | (TRANSACTION (s, tcode, None), OPERATION op) -> 
	  begin
	    let opn = op.op_name#getBaseName in
	    match opn with 
	    | "i"
	    | "ii" -> 
		begin
		  let mInfo =
                    app#get_method (retrieve_cms proc_name#getSeqNumber) in
		  let pc = op.op_name#getSeqNumber in
		  let opcode = mInfo#get_opcode pc in 
		  match opcode with 
		  | OpIfEq _
		  | OpIfNe _
		  | OpIfLt _
		  | OpIfGe _
		  | OpIfGt _
		  | OpIfLe _ -> 
		     let arg = JCHSystemUtils.get_arg_var "src1" op.op_args in
                     begin
		       self#transformCode tcode ;
		       match self#get_branch_asserts (opn = "ii") opcode arg with 
		       | Some acmd-> 
			  let new_tcode =
                            JCHSystemUtils.add_cmds
                              ~cms ~init_cmds:[] ~final_cmds:[acmd] ~code:tcode in
			  code#setCmdAt i (TRANSACTION (s, new_tcode, None))
		       | None -> code#setCmdAt i (self#transformCmd cmd)
		     end
		  | _ -> code#setCmdAt i (self#transformCmd cmd)
		end
	    | _ -> code#setCmdAt i (self#transformCmd cmd)
	  end
      | (ASSERT _, OPERATION op) -> 
	 let opn = op.op_name#getBaseName in
         begin
	   match opn with 
	   | "i"
	   | "ii" -> 
	      let mInfo =
                app#get_method (retrieve_cms proc_name#getSeqNumber) in
	      let pc = op.op_name#getSeqNumber in
	      let opcode = mInfo#get_opcode pc in
              begin
		match opcode with 
		| OpIfEq _
		| OpIfNe _
		| OpIfLt _
		| OpIfGe _
		| OpIfGt _
		| OpIfLe _ -> 
		   begin
		     let arg = JCHSystemUtils.get_arg_var "src1" op.op_args in
		     match self#get_branch_asserts (opn = "ii") opcode arg with 
		     | Some acmd -> 
			let new_code =
                          JCHIFSystem.chif_system#make_code cms [cmd; acmd] in
			code#setCmdAt
                          i (CODE (new symbol_t "enhanced asserts", new_code)) ;
			let vars = vars_in_cmd acmd in
			let record_assert_var var = 
			  match assert_var_to_states#get var with 
			  | Some set -> set#add !state_name
			  | None ->
                             assert_var_to_states#set
                               var
                               (SymbolCollections.set_of_list[!state_name]) in
			   List.iter record_assert_var vars 
			| None -> code#setCmdAt i (self#transformCmd cmd)
		      end
		  | _ -> code#setCmdAt i (self#transformCmd cmd)
		end
	    | _ -> code#setCmdAt i (self#transformCmd cmd)
	  end
      | _ -> code#setCmdAt i (self#transformCmd cmd)
    done ;
    let last = code#length - 1 in
    if last >= 0 then 
      code#setCmdAt last (self#transformCmd (code#getCmdAt last))
    else
      () 

  method transformProcedure (proc:procedure_int) = 
    let body = proc#getBody in
    begin
      new_states := [] ;
      new_edges := [] ;
      wto_heads := [] ;
      self#transformCode body 
    end
end

let add_operations
      (procedure:procedure_int) (wto_infos:JCHLoopUtils.wto_info_t list) =
  begin
    add_pre_post_ops procedure ;
    let transformer = new op_transformer_t procedure wto_infos in
    transformer#transformProcedure procedure ;
    transformer#get_assert_var_to_states 
  end
  
let add_vars_op
      ~(proc:procedure_int)
      ~(cms:class_method_signature_int)
      ~(state:state_int)
      ~(add_vars:variable_t list)
      ~(remove_vars:variable_t list) = 
  let code = state#getCode in
  if remove_vars <> [] then 
    begin
      let remove_op = 
	let args =
          List.map (fun v -> (v#getName#getBaseName, v, READ)) remove_vars in
	DOMAIN_OPERATION ([lin_eqs_dom_name; int_dom_name; poly_dom_name],
                          {op_name = remove_vars_sym; op_args = args }) in
      let last_cmd = pred code#length in
      let exit_code = 
	match code#getCmdAt last_cmd with
	| CODE (s, c) -> 
	    if s = exit_state_sym then c
	    else 
	      begin
		pr_debug [STR "remove_vars_op "; state#getLabel#toPretty; NL;
                          proc#toPretty; NL] ;
		raise (JCH_failure (STR "exit_state code expected."))
	      end
	| _ -> 
	    begin
	      pr_debug [STR "remove_vars_op "; state#getLabel#toPretty; NL;
                        proc#toPretty; NL] ;
	      raise (JCH_failure (STR "exit_state code expected.")) 
	    end in
      let new_exit_code =
        JCHSystemUtils.add_cmds
          ~cms ~init_cmds:[] ~final_cmds:[remove_op] ~code:exit_code in
      code#setCmdAt last_cmd (CODE (exit_state_sym, new_exit_code))
    end


class length_transformer_t
        (proc:procedure_int)
        (jvar_infos:JCHVarInfo.jvar_info_t VariableCollections.table_t) = 
object (self: _)

  inherit code_transformer_t as super

  val proc_name = proc#getName;
  val cms = retrieve_cms proc#getName#getSeqNumber;
  val length_vars = new VariableCollections.set_t 

  method private make_length_from_var (var:variable_t) = 
    let length_var = JCHSystemUtils.make_length var in
    try 
      List.find length_var#equal length_vars#toList 
    with _ ->
      begin
        length_vars#add length_var;
        length_var
      end

  method private make_length_assign (array:variable_t) (var:variable_t) = 
    let length_var = self#make_length_from_var array in
    ASSIGN_NUM (length_var, NUM_VAR var)

  method private make_length_assign2 (var:variable_t) (array:variable_t) = 
    let length_var = self#make_length_from_var array in
    ASSIGN_NUM (var, NUM_VAR length_var)

  method private make_length_eq_assert (array:variable_t) (var:variable_t) = 
    let length_var = self#make_length_from_var array in
    ASSERT (EQ (length_var, var))

  method private make_length_geq_assert (array:variable_t) (var:variable_t) = 
    let length_var = self#make_length_from_var array in
    ASSERT (GEQ (length_var, var))

  method private make_length_of_array_top (array:variable_t) = 
    let length_var = self#make_length_from_var array in
    ABSTRACT_VARS [length_var]

  method private make_length_const (var:variable_t) (num:numerical_t) = 
    let length_var = self#make_length_from_var var in
    ASSIGN_NUM (length_var, NUM num)

  method transformCmd (cmd:(code_int, cfg_int) command_t) = 
    match cmd with
    | CFG (s, cfg) ->
       begin
         List.iter
           (fun name ->
             self#transformCode (cfg#getState name)#getCode) cfg#getStates ;
	 proc#getScope#addVariables length_vars#toList ; 
	 CFG (s, cfg)
       end
    | CODE (s, code) -> 
       if s#equal enter_state_sym then
         CODE (s, self#transform_init_params_code code) 
       else
         super#transformCmd cmd
    | ASSIGN_SYM (v, SYM_VAR w) -> 
       let mk_length_code () =
	 let w_length = JCHSystemUtils.make_length w in		  
	 let acmd = self#make_length_assign v w_length in
	 let new_code = chif_system#make_code cms [cmd; acmd] in
	 CODE (new symbol_t "assign_sym array", new_code) in
       begin
	  match jvar_infos#get w with
	  | Some jvar_info -> 
	     if jvar_info#has_length then
               mk_length_code () 
	     else
               cmd
	  | _ -> cmd
	end
    | OPERATION op ->
	begin
	  match op.op_name#getBaseName with 
	  | "i" 
	  | "ii" -> 
	      begin
		let mInfo =
                  app#get_method (retrieve_cms proc_name#getSeqNumber) in
		let pc = op.op_name#getSeqNumber in
		match mInfo#get_opcode pc with 
		| OpStringConst s -> 
		   let string = JCHSystemUtils.get_arg_var "ref" op.op_args in
		   let scmd =
                     self#make_length_const
                       string (mkNumerical (String.length s)) in
		   let new_code = chif_system#make_code cms [cmd; scmd] in
		   CODE (new symbol_t "string const", new_code) 
		| OpAMultiNewArray _ -> 
		   let array = JCHSystemUtils.get_arg_var "ref" op.op_args in
		   let length = JCHSystemUtils.get_arg_var "dim1" op.op_args in
		   let acmd = self#make_length_assign array length in
		   let new_code = chif_system#make_code cms [cmd; acmd] in
		   CODE (new symbol_t "new array", new_code) 
		| OpNewArray _ -> 
		   let array = JCHSystemUtils.get_arg_var "ref" op.op_args in
		   let length = JCHSystemUtils.get_arg_var "length" op.op_args in
		   let acmd = self#make_length_assign array length in
		   let new_code = chif_system#make_code cms [cmd; acmd] in
		   CODE (new symbol_t "new array", new_code) 
		| OpArrayLength -> 
		   let array = JCHSystemUtils.get_arg_var "ref" op.op_args in
		   let length = JCHSystemUtils.get_arg_var "val" op.op_args in
		   let acmd = self#make_length_assign2 length array in
		   let new_code = chif_system#make_code cms [cmd; acmd] in
		   CODE (new symbol_t "array length", new_code);
		| OpAConstNull -> 
		   let ref = JCHSystemUtils.get_arg_var "ref" op.op_args in
		   let jvar_info = Option.get (jvar_infos#get ref) in
		   if jvar_info#has_length then 
		     let acmd = self#make_length_of_array_top ref in 
		     let new_code = chif_system#make_code cms [cmd; acmd] in
		     CODE (new symbol_t "const null", new_code) 
		   else
                     super#transformCmd cmd
		| OpNew cn -> 
		   let ref = JCHSystemUtils.get_arg_var "ref" op.op_args in
		   let jvar_info = Option.get (jvar_infos#get ref) in
		   if jvar_info#has_length then 
		     begin
		       let string = JCHSystemUtils.get_arg_var "ref" op.op_args in
		       let scmd = self#make_length_const string numerical_zero in
		       let new_code = chif_system#make_code cms [cmd; scmd] in
		       CODE (new symbol_t "new string", new_code) 
		     end
		   else super#transformCmd cmd
		| OpArrayLoad _ -> 
		   let array = JCHSystemUtils.get_arg_var "array" op.op_args in
		   let index = JCHSystemUtils.get_arg_var "index" op.op_args in
		   let element = JCHSystemUtils.get_arg_var "val" op.op_args in
		   let acmd = self#make_length_geq_assert array index in
		   let jvar_info = Option.get (jvar_infos#get element) in
		   let new_code = 
		     if jvar_info#has_length then 
		       let ecmd = self#make_length_of_array_top element in
		       chif_system#make_code cms [ecmd; cmd; acmd] 
		     else
		       chif_system#make_code cms [cmd; acmd] in
		   CODE (new symbol_t "array load", new_code);
		| OpArrayStore _ -> 
		   let array = JCHSystemUtils.get_arg_var "array" op.op_args in
		   let index = JCHSystemUtils.get_arg_var "index" op.op_args in
		   let acmd = self#make_length_geq_assert array index in
		   let new_code = chif_system#make_code cms [cmd; acmd] in
		   CODE (new symbol_t "array store", new_code);
		| OpGetStatic (cn, fsig) 
		| OpGetField (cn, fsig) -> 
		    let var = JCHSystemUtils.get_arg_var "val" op.op_args in
		    let jvar_info = Option.get (jvar_infos#get var) in
		    if jvar_info#has_length then 
		      let acmd = self#make_length_of_array_top var in
		      let new_code = chif_system#make_code cms [acmd; cmd] in
		      CODE (new symbol_t "get field", new_code);
		    else
                      super#transformCmd cmd
		| OpCheckCast _ -> 
		   let ref_new_type = JCHSystemUtils.get_arg_var "dst1" op.op_args in
		   let jvar_info = Option.get (jvar_infos#get ref_new_type) in
		   if jvar_info#has_length then 
		     let acmd = self#make_length_of_array_top ref_new_type in 
		     let new_code = chif_system#make_code cms [cmd; acmd] in
		     CODE (new symbol_t "op check_cast", new_code) 
		   else
                     super#transformCmd cmd
		| OpInvokeStatic _
		| OpInvokeVirtual _ 
		| OpInvokeInterface _
		| OpInvokeSpecial _ -> 
		    begin
		      match (List.filter
                               JCHSystemUtils.is_not_exception
                               (JCHSystemUtils.get_write_vars op.op_args)) with
		      |	return :: _ -> 
			  let jvar_info = Option.get (jvar_infos#get return) in
			  if jvar_info#has_length then 
                            (* just to have a length ready for the invocation to set *)
			    let acmd = self#make_length_of_array_top return in
			    let new_code = chif_system#make_code cms [acmd; cmd] in
			    CODE (new symbol_t "op invoke", new_code) 
			  else
                            super#transformCmd cmd
		      |	_ -> super#transformCmd cmd
		    end		    
		| _ -> super#transformCmd cmd
	      end
	  | _ -> super#transformCmd cmd
	end
    | _ -> super#transformCmd cmd 

  method transform_init_params_code (code:code_int) = 
    let rev_cmds = ref [] in 
    for i = 0 to code#length - 1 do 
      let cmd = code#getCmdAt i in 
      match cmd with 
      | OPERATION op -> 
	  if op.op_name#equal init_params_sym then 
	    begin
	      let params = JCHSystemUtils.get_write_vars op.op_args in
	      let has_length (var:variable_t) = 
		match jvar_infos#get var with 
		| Some jvar_info -> jvar_info#has_length
		| _ -> false in
	      let arrays = List.filter has_length params in
	      if arrays <> [] then 
		begin
		  let length_args =
                    List.map
                      (fun v -> ("arg", self#make_length_from_var v, WRITE))
                      arrays in
		  rev_cmds :=
                    (OPERATION
                       {op_name = init_assumptions_sym ;
                        op_args = length_args }) :: !rev_cmds 
		end ;
	      rev_cmds := cmd :: !rev_cmds ;
	    end 
      |	_ -> rev_cmds := cmd :: !rev_cmds 
    done ;
    chif_system#make_code cms !rev_cmds

  method transformProcedure (proc: procedure_int) = 
    let body = proc#getBody in
    self#transformCode body
      
end

let add_array_length_operations
      (procedure:procedure_int)
      (var_infos:JCHVarInfo.jvar_info_t VariableCollections.table_t) = 
  let transformer = new length_transformer_t procedure var_infos in
  transformer#transformProcedure procedure

 

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
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

let dbg = ref false 

class pretty_op_t o =
  object
    method op = o
    method toPretty = operation_to_pretty o
  end 

module OperationCollections = CHCollections.Make
    (struct 
      type t = operation_t
      let compare op1 op2 = compare op1.op_name op2.op_name
      let toPretty op = operation_to_pretty op 
    end)

class var_info_collector_t proc meth = 
  object (self: _) 
    inherit var_collector_t as super 

    val proc_name = proc#getName
    val mInfo = app#get_method (retrieve_cms proc#getName#getSeqNumber)
    val origins = new VariableCollections.table_t
    val origin_states = new VariableCollections.table_t
    val var_to_states = new VariableCollections.table_t
    val var_to_read_states = new VariableCollections.table_t

    (* for the case v1 = v2 and we do not know the type of v2 *)                           
    val var_to_assigned_vars : VariableCollections.set_t VariableCollections.table_t =
      new VariableCollections.table_t

    (* var -> variables it depends on *)      
    val var_to_rvars = new VariableCollections.table_t

    (* return -> offset of instruction where it is set -> read var *)                      
    val return_pc_to_rvar = new IntCollections.table_t

    (* var -> ops of origin *)                          
    val var_to_origin_ops = new VariableCollections.table_t

    (* x -> y -> ASSERT (x = y) state . Used for transmition of taint *)                          
    val var_to_var_to_eqs = new VariableCollections.table_t

    (* x -> y -> ASSERT (x < y or x <= y) state . Used for transmition of taint *)                          
    val var_to_var_to_ineqs = new VariableCollections.table_t

    (* var to OpIfEq / OpIfNeq op *)                            
    val var_to_if_eq_op = new VariableCollections.table_t

    (* var to state of OpIfEq / OpIfNe op *)                        
    val var_to_if_eq_state = new VariableCollections.table_t

    (* var to OpIfEq / OpIfNeq op *)                           
    val var_to_if_ineq_op = new VariableCollections.table_t

    (* var to state of OpIfEq / OpIfNe op *)                          
    val var_to_if_ineq_state = new VariableCollections.table_t

    (* phi -> immediate var dependents *)                             
    val phi_to_vars = new VariableCollections.table_t

    (* var to constant value *)                    
    val var_to_const = new VariableCollections.table_t

    (* variables that are in var_to_const that are not constant *)                     
    val not_constant = new VariableCollections.set_t

    (* var to pcs whete it appears *)                     
    val var_to_pcs = new VariableCollections.table_t

    (* var to one pc where it is read, a load if there is one *)                   
    val var_to_read_pc = new VariableCollections.table_t

    (* local variable index to load, store and iinc pcs *)                       
    val local_var_index_to_pc_to_var = new IntCollections.table_t 

    method get_info = 
      let restr_var_to_const = new VariableCollections.table_t in
      let add (var: variable_t) (const:numerical_t) = 
	if not (not_constant#has var) then restr_var_to_const#set var const in
      var_to_const#iter add ;
      let get_const name = 
	let sub = Str.string_after name 2 in
	mkNumericalFromString sub in
      let add_cNs var = 
	let name = var#getName#getBaseName in
	if name.[0] = 'c' then 
	  restr_var_to_const#set var (get_const name) in
      List.iter add_cNs proc#getScope#getVariables ;
      let var_origin_ops = ref [] in
      let add_var_origin_ops var ops = 
	var_origin_ops := (var#getIndex, ops#toList) :: !var_origin_ops in
      var_to_origin_ops#iter add_var_origin_ops ;
      (origin_states,
       var_to_states,
       var_to_read_states,
       origins, phi_to_vars,
       var_to_rvars,
       return_pc_to_rvar,
       !var_origin_ops,
       var_to_var_to_eqs,
       var_to_var_to_ineqs,
       restr_var_to_const, 
       var_to_pcs,
       var_to_read_pc,
       local_var_index_to_pc_to_var)

    val var_set = ref (new VariableCollections.set_t)
    val read_var_set = ref (new VariableCollections.set_t)
    val cfg_opt = ref None 
    val current_pc = ref (-1) 
    val current_state = ref state_name_sym

    (* used to find the type of element from the type of the array *)                      
    val array_to_elements = new VariableCollections.table_t
                          
    (* used to find the type of collections from the type of its elements *)
    val element_to_arrays = new VariableCollections.table_t 

    method private set_origin_state (v:variable_t) =
      match origin_states#get v with 
      | Some set -> 
	  set#add !current_state
      | None -> 
	  origin_states#set v (SymbolCollections.set_of_list [!current_state])

    method private set_origin (v:variable_t) = 
      self#set_origin_state v ;
      if !current_pc = -1 then 
	current_pc := JCHSystemUtils.sym_to_pc !current_state  
      else () ;
      match origins#get v with 
      | Some set -> 
	  set#add !current_pc
      | None -> 
	  origins#set v (IntCollections.set_of_list [!current_pc])

    method private set_var_to_op (op:operation_t) (var:variable_t) = 
      match var_to_origin_ops#get var with 
      | Some set -> 
	  set#add op
      | None ->
         var_to_origin_ops#set var (OperationCollections.set_of_list [op]) 

     method private set_array_to_elements (array:variable_t) (element:variable_t) = 
      match array_to_elements#get array with 
      |	Some set -> set#add element
      |	None ->
         array_to_elements#set array (VariableCollections.set_of_list [element])

    method add_phi_info (phi:variable_t) (var:variable_t) = 
      (match phi_to_vars#get phi with 
       | Some vars -> vars#add var 
       | None -> phi_to_vars#set phi (VariableCollections.set_of_list [var])) 

    method private add_rvars (var:variable_t) (rvars:variable_t list) = 
      let index = var#getIndex in
      if index = num_return_var_index || index = sym_return_var_index then 
	return_pc_to_rvar#set !current_pc (List.hd rvars)
      else 
	let new_list =
	  match var_to_rvars#get var with 
	  | Some pretty_old_list -> 
	      let old_list = pretty_old_list#vars in
	      let red_rvars =
                List.filter (fun v -> not (List.mem v old_list)) rvars in
	      old_list @ red_rvars 
	  | None -> rvars in
	var_to_rvars#set var (new pretty_var_list_t new_list)

    method private add_var_to_pc (is_read:bool) (var:variable_t) = 
      (match var_to_pcs#get var with 
      |	Some pcs -> pcs#add !current_pc
      |	_ -> var_to_pcs#set var (IntCollections.set_of_list [!current_pc])) ;
      if is_read then 
	begin
	  match var_to_read_pc#get var with 
	  | Some _ -> () 
	  | _ ->
             var_to_read_pc#set var (IntCollections.set_of_list [!current_pc])
	end

    method private add_load_var (var:variable_t) = 
      var_to_read_pc#set var (IntCollections.set_of_list [!current_pc])

    method walkState (cfg:cfg_int) (state:symbol_t) = 
      let name = state#getBaseName in
      if not (name = "normal-exit"
              || name = "exceptional-exit"
              || name = "method-exit"
              || name = "loop_counter_init") then 
	begin
	  var_set := new VariableCollections.set_t ;
	  read_var_set := new VariableCollections.set_t ;
	  current_state := state ;
	  current_pc := 
	    if name = "method-initialization" then
              0 
	    else
              JCHSystemUtils.sym_to_pc state ;
	  super#walkCode (cfg#getState state)#getCode ;
	  let set_state (is_read:bool) (v:variable_t) = 
	    let table = if is_read then var_to_read_states else var_to_states in
	    match table#get v with 
	    | Some set -> 
		set#add state
	    | None -> 
		table#set v (SymbolCollections.set_of_list [state]) in
	  !var_set#iter (set_state false) ;
	  !read_var_set#iter (set_state true)
	end
	  
    method private add_to_eq_table
                     (v1:variable_t) (v2:variable_t) (state_name:symbol_t) = 
      match var_to_var_to_eqs#get v1 with 
      | Some table -> 
	  begin
	    match table#get v2 with 
	    | Some set -> set#add state_name
	    | None -> table#set v2 (SymbolCollections.set_of_list [state_name])
	  end
      | None -> 
	  begin
	    let table = new VariableCollections.table_t in
	    table#set v2 (SymbolCollections.set_of_list [state_name]) ;
	    var_to_var_to_eqs#set v1 table 
	  end 

    method private add_eq
                     (is_eq:bool)
                     (opname:symbol_t)
                     (args:(string * variable_t * arg_mode_t) list)
                     (state_name:symbol_t) =
      let opname_str = opname#getBaseName in
      if is_eq = (opname_str = "i") then 
	begin
	  let src1 = JCHSystemUtils.get_arg_var "src1" args in
	  let src2 = JCHSystemUtils.get_arg_var "src2" args in
	  self#add_to_eq_table src1 src2 state_name ;
	  self#add_to_eq_table src2 src1 state_name
	end
      else ()

    method private add_eq2
                     (is_eq:bool)
                     (op:operation_t)
                     (opname:symbol_t)
                     (args:(string * variable_t * arg_mode_t) list)
                     (state_name:symbol_t) = 
      let src = JCHSystemUtils.get_arg_var "src1" args in
      match var_to_origin_ops#get src with 
      | Some set -> 
	  let ops = set#toList in
	  if List.length ops = 1 then 
	    begin
	      let op = List.hd ops in
	      match mInfo#get_opcode op.op_name#getSeqNumber with
	      | OpCmpL 
	      | OpCmpFL
	      | OpCmpFG
	      | OpCmpDL
	      | OpCmpDG -> self#add_eq is_eq opname op.op_args state_name
	      | _ -> ()	    		      
	    end
	  else () 
      |	None -> 
	  begin
	    var_to_if_eq_op#set src (new pretty_op_t op) ;
            (* CHANGE: there could be more than one OpIfEq with the same source ? *)
	    var_to_if_eq_state#set src (state_name) 
	  end

    method private add_cmp (iop:operation_t) (var:variable_t) =
      (* Note: iop is not used *)
      (match var_to_if_eq_op#get var with
      |	Some pp_if_op -> 
	  let if_op = pp_if_op#op in
	  let if_opname = if_op.op_name in
	  let state_name = Option.get (var_to_if_eq_state#get var) in
	  begin
	    match mInfo#get_opcode if_opname#getSeqNumber with
	    | OpIfEq _ -> self#add_eq2 true if_op if_opname if_op.op_args state_name
	    | _ -> self#add_eq2 false if_op if_opname if_op.op_args state_name
	  end
      |	None -> ()) ;
      (match var_to_if_ineq_op#get var with 
      |	Some pp_if_op -> 
	  let if_op = pp_if_op#op in
	  let if_opname = if_op.op_name in
	  let state_name = Option.get (var_to_if_ineq_state#get var) in
	  begin
	    match mInfo#get_opcode if_opname#getSeqNumber with
	    | OpIfLt _ 
	    | OpIfLe _ -> self#add_ineq2 true if_op if_opname if_op.op_args state_name
	    | _ -> self#add_ineq2 false if_op if_opname if_op.op_args state_name
	  end
      |	None -> ()) 
	

    method add_switch () = 
      let cfg = Option.get (!cfg_opt) in
      let state = cfg#getState !current_state in
      let add_state state_name = 
	let state : state_int = cfg#getState state_name in
	let add_eq x y = 
	    self#add_to_eq_table x y state_name ;
	    self#add_to_eq_table y x state_name in
	let code = state#getCode in 
	let rec check_cmd code i = 
	  if i = code#length then false (* table with just default ? *) 
	  else 
	    begin 
	      match code#getCmdAt i with 
	      | ASSERT (EQ (x, y)) -> 
		  add_eq x y ;
		  true 
	      | ASSERT _ -> 
		  true
	      | TRANSACTION (_, tcode, None) -> 
		  let found = check_cmd tcode 0 in
		  if found then true
		  else check_cmd code (succ i) 
	      | _ -> check_cmd code (succ i) 
	    end in
	let _ = check_cmd code 0 in 
	() in
      List.iter add_state state#getOutgoingEdges

    method private add_to_ineq_table
                     (v1:variable_t) (v2:variable_t) (state_name:symbol_t) = 
      match var_to_var_to_eqs#get v1 with 
      |	Some table -> 
	  begin
	    match table#get v2 with 
	    | Some set -> set#add state_name
	    | None -> table#set v2 (SymbolCollections.set_of_list [state_name])
	  end
      | None -> 
	  begin
	    let table = new VariableCollections.table_t in
	    table#set v2 (SymbolCollections.set_of_list [state_name]) ;
	    var_to_var_to_ineqs#set v1 table 
	  end 

    method private add_ineq
                     (is_lt_or_le:bool)
                     (opname:symbol_t)
                     (args:(string * variable_t * arg_mode_t) list)
                     (state_name:symbol_t) =
      let opname_str = opname#getBaseName in
      if is_lt_or_le = (opname_str = "i") then 
	begin
	  let src1 = JCHSystemUtils.get_arg_var "src1" args in
	  let src2 = JCHSystemUtils.get_arg_var "src2" args in
	  self#add_to_ineq_table src1 src2 state_name ;
	  self#add_to_ineq_table src2 src1 state_name
	end
      else ()

    method private add_ineq2
                     (is_lt_or_le:bool)
                     (op:operation_t)
                     (opname:symbol_t)
                     (args:(string * variable_t * arg_mode_t) list)
                     (state_name:symbol_t) = 
      let src = JCHSystemUtils.get_arg_var "src1" args in
      match var_to_origin_ops#get src with 
      | Some set -> 
	  let ops = set#toList in
	  if List.length ops = 1 then 
	    begin
	      let op = List.hd ops in
	      match mInfo#get_opcode op.op_name#getSeqNumber with
	      | OpCmpL 
	      | OpCmpFL
	      | OpCmpFG
	      | OpCmpDL
	      | OpCmpDG -> self#add_ineq is_lt_or_le opname op.op_args state_name
	      | _ -> ()	    		      
	    end
	  else () 
      |	None -> 
	  begin
	    var_to_if_ineq_op#set src (new pretty_op_t op) ;
            (* CHANGE: there could be more than one OpIfEq with the same source ? *)
	    var_to_if_ineq_state#set src (state_name) 
	  end


    val increment = ref false 

    method walkCmd (cmd: (code_int, cfg_int) command_t) = 
      match cmd with
      | CFG (name, cfg) -> 
	  cfg_opt := Some cfg ;
	  List.iter (self#walkState cfg) cfg#getStates 
      |	TRANSACTION (s, _, _) -> 
	  if s#getBaseName = "increment" then increment := true ;
	  super#walkCmd cmd
      | ASSIGN_STRUCT (v, w) 
      | ASSIGN_ARRAY (v, w) 
      | ASSIGN_NUM (v, NUM_VAR w) -> 
	  !var_set#addList [v; w] ;
	  !read_var_set#add w;
	  if not (JCHSystemUtils.is_length v || JCHSystemUtils.is_length w) then
            self#set_origin v ;
	  self#add_rvars v [w] ;
	  self#add_var_to_pc false v ;
	  self#add_var_to_pc true w ;
	  if not (JCHSystemUtils.is_length v || JCHSystemUtils.is_length w) then
            self#add_phi_info v w
      | ASSIGN_SYM (v, SYM_VAR w) ->
	  !var_set#addList [v; w] ;
	  !read_var_set#add w;
	  if w#getIndex <> exception_var_index then
            self#set_origin v ;
	  self#add_rvars v [w] ;
	  self#add_var_to_pc false v ;
	  self#add_var_to_pc true w ;
	  if w#getIndex <> exception_var_index then
            self#add_phi_info v w
      |	ASSIGN_NUM (v, NUM c) -> 
	  begin
	    !var_set#addList [v] ;
	    self#set_origin v ; 
	    self#add_var_to_pc false v;
	    match var_to_const#get v with 
	    | Some c' -> 
	       if not (c#equal c') then
                 not_constant#add v  (* This could happen for a branching instruction *)
	    | _ -> var_to_const#set v c 
	  end
      |	ASSIGN_NUM (v, PLUS (x, y)) -> 
	  if !increment then 
	    begin
	      self#add_phi_info v x ;
	      increment := false 
	    end ;
	  !var_set#addList [v; x; y] ;
	  !read_var_set#addList [x; y];
	  self#set_origin v ;
	  self#add_rvars v [x; y] ;
	  self#add_var_to_pc false v;
	  List.iter (self#add_var_to_pc true) [x; y] ;
      | ASSIGN_NUM (v, _) 
      | ASSIGN_SYM (v, _) ->
	  let vars = vars_in_cmd cmd in
	  !var_set#addList vars ;
	  let read_vars = List.filter (fun v' -> not (v'#equal v)) vars in
	  !read_var_set#addList read_vars;
	  self#set_origin v ;
	  let rvars =
            List.filter (fun var -> var#getIndex <> v#getIndex) vars in
	  self#add_rvars v rvars ;
	  List.iter
            (self#add_var_to_pc true) (List.filter (fun v' -> v#equal v') vars) ;
	  self#add_var_to_pc false v;
      | INCREMENT (v, _) -> 
	  !var_set#add v ;
	  !read_var_set#add v ;
	  self#set_origin v ;
      | OPERATION op -> 
	  begin
	    let opname = op.op_name in
	    let args = op.op_args in
	    let base_name = opname#getBaseName in
	    match base_name with 
	    | "i" 
	    | "ii" -> 
		begin
		  let wvars = JCHSystemUtils.get_write_vars args in 
		  let rvars = JCHSystemUtils.get_read_vars args in
		  !var_set#addList wvars;
		  !var_set#addList rvars;
		  !read_var_set#addList rvars;
		  List.iter (self#add_var_to_pc false) wvars ;
		  List.iter (self#add_var_to_pc true) rvars ;
		  List.iter self#set_origin wvars ;
		  List.iter (self#set_var_to_op op) wvars ;
		  (if wvars = [] then () 
		  else 
		    List.iter (fun v -> self#add_rvars v rvars) wvars ) ;
		  match mInfo#get_opcode opname#getSeqNumber with
		  | OpIInc (n, _) -> 
		      begin 
			let var = JCHSystemUtils.get_arg_var "src_dst" args in
			self#set_var_to_op op var ;
		      end
		  | OpCmpL 
		  | OpCmpFL
		  | OpCmpFG
		  | OpCmpDL
		  | OpCmpDG -> 
		      let var = JCHSystemUtils.get_arg_var "dst1" args in
		      self#set_var_to_op op var ;
		      self#add_cmp op var 
		  | OpAdd _
		  | OpSub _
		  | OpMult _
		  | OpDiv _
		  | OpNeg _ -> 
		      let var = JCHSystemUtils.get_arg_var "dst1" args in
		      self#set_var_to_op op var 
		  | OpIfCmpEq _ -> self#add_eq true opname args !current_state
		  | OpIfCmpNe _ -> self#add_eq false opname args !current_state
		  | OpIfCmpLt _ 
		  | OpIfCmpLe _ -> self#add_ineq true opname args !current_state
		  | OpIfCmpGt _ 
		  | OpIfCmpGe _ -> self#add_ineq false opname args !current_state
		  | OpIfEq _ -> self#add_eq2 true op opname args !current_state
		  | OpIfNe _ -> self#add_eq2 false op opname args !current_state
		  | OpIfLt _ 
		    | OpIfLe _ ->
                     self#add_ineq2 true op opname args !current_state
		  | OpIfGt _ 
		    | OpIfGe _ ->
                     self#add_ineq2 false op opname args !current_state
		  | OpTableSwitch _ 
		  | OpLookupSwitch _ -> self#add_switch ()
		  | OpLoad (_,n)  -> 
		      let var = JCHSystemUtils.get_arg_var "src1" args in
		      self#add_load_var var 
		  | OpStore (_,n) -> 
		      begin
			let var = JCHSystemUtils.get_arg_var "dst1" args in
			let pc =  opname#getSeqNumber in
			match local_var_index_to_pc_to_var#get n with 
			| Some table -> table#set pc var 
			| _ -> 
			    let table = new IntCollections.table_t in
			    table#set pc var ;
			    local_var_index_to_pc_to_var#set n table
		      end
		  | _ -> () 
		end
	    | "v" -> current_pc := opname#getSeqNumber
	    | "init_params" -> 
		begin
		  let set_arg var = 
		    let name = var#getName#getBaseName in
		    let index = int_of_string (Str.string_after name 1) in
		    match local_var_index_to_pc_to_var#get index with 
		    | Some table -> table#set 0 var 
		    | _ -> 
			let table = new IntCollections.table_t in
			table#set 0 var ;
			local_var_index_to_pc_to_var#set index table in
		  List.iter set_arg  (JCHSystemUtils.get_write_vars args) ;
		end
	    | _ -> ()
	  end 
      | ASSERT _ -> 
	  !var_set#addList (vars_in_cmd cmd) ;
	  !read_var_set#addList (vars_in_cmd cmd) ;
      | _ -> 
	  super#walkCmd cmd 

    method walkProcedure (proc:procedure_int) = 
      self#walkCode proc#getBody
  end

let collect_var_info (proc:procedure_int) (meth:method_int) = 
  let collector = new var_info_collector_t proc meth in
  collector#walkProcedure proc ;
  collector#get_info 


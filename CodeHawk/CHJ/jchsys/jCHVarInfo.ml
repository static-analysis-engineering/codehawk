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
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

class jvar_info_t
    ~(variable: variable_t)
    ~(param_index: int)
    ~(is_phi: bool)
    ~(origins: int list)
    ~(pc_in_scope: int)
    ~(basic_num_vtype: value_type_t option)
    ~(vtypes: value_type_t list)
    ~(const: numerical_t option)
    ~(is_numeric: bool)
    ~(has_length: bool)
    ~(first_state: symbol_t)
    ~(last_states: symbol_t list)
    ~(read_states: symbol_t list)
    ~(read_vars: variable_t list)
    ~(return_pc_to_rvar : variable_t IntCollections.table_t option)
    ~(origin_operations : operation_t list)
    ~(local_indices : int list) =
  object (self: 'a)

    method get_variable = variable

    (* first state in which the variable appears *)
    method get_first_state = first_state

    (* states after which the variable is not used anymore, so it is safe to
       abstract *)
    method get_last_states = last_states

    (* states where the variable is read *)
    method get_read_states = read_states

    (* origin pcs sorted from large to small *)
    method get_origins = origins

    (* a pc where the variable is read *)
    method get_pc_in_scope = pc_in_scope

    (* the basic numeric type of arrays elements or collection elements *)
    method get_basic_num_type = basic_num_vtype

    (* list of all possible types *)
    method get_types = vtypes

    (* if this variable is a constant it returns that constant *)
    method get_constant = const

    (* vars the variable is directly dependent on *)
    method get_read_vars = read_vars

    (* if the variable is a return variable, the pcs of the return and the
     * rvars for that return. The return variable is only one *)
    method get_return_pc_to_rvar = Option.get (return_pc_to_rvar)

    method get_origin_operations = origin_operations

    method is_phi = is_phi

    (* the index of the program local variables that are represented by this
     * variable; a local variable can represent several local variables if
     * they are the same constant or they one local variable was assigned
     * another *)
    method get_local_indices = local_indices

    method is_numeric = is_numeric

    val has_length = ref has_length

    method set_has_length b = has_length := b

    method has_length = !has_length

    method is_parameter =
      param_index > -1

    method is_local_var =
      let name = variable#getName#getBaseName in
      name.[0] = 'r' && name.[1] <> 'e' && param_index = -1

    method get_param_index =
      if param_index > -1 then Some param_index
      else None

    method is_return = Option.is_some return_pc_to_rvar

    method is_length =
      variable#getName#getBaseName = "length"

    val corresp_var = ref None
    method set_corresp_var var =
      corresp_var := Some var

    method get_variable_from_length =
      if self#is_length then
	match !corresp_var with
	| Some var -> (Some var, true)
	| None ->
	    begin
	      let name = variable#getName in
	      match name#getAttributes with
	      | "v" :: var_name :: atts ->
		 let var_name_sym =
                   new symbol_t
                       ~atts:atts
                       ~seqnr:name#getSeqNumber
                       var_name in
		 let var =
                   new variable_t
                       var_name_sym
                       ~suffix:variable#getSuffix
                       ~register:variable#isRegister
                       ~path:variable#getPath
                       SYM_VAR_TYPE in
		  (Some var, false)
	      | _ -> (None, false)
	    end
      else (None, false)

    val corresp_length = ref None

    method set_corresp_length (length:variable_t) =
      corresp_length := Some length

    method get_length =
      if self#has_length then
	match !corresp_length with
	| Some len -> (Some len, true)
	| None ->
	    begin
	      let name = variable#getName in
	      let length_name =
                new symbol_t
                    ~atts:(["v"; name#getBaseName]  @ name#getAttributes)
                    ~seqnr:name#getSeqNumber
                    "length" in
	      let length =
                new variable_t
                    length_name
                    ~register:variable#isRegister
                    ~path:variable#getPath
                    NUM_VAR_TYPE in
	      (Some length, false)
	    end
      else (None, false)

    method toPretty =
      let flag_pps = ref [] in
      let add_local_index i =
	flag_pps := LBLOCK [STR ": local "; INT i] :: !flag_pps in
      List.iter add_local_index local_indices;
      let return_pp =
	match return_pc_to_rvar with
	| Some table ->
	    LBLOCK [STR "return offsets and the read var: "; NL; table#toPretty]
	| None ->
	    if param_index > -1 then
	      begin
		flag_pps := (STR ": parameter ") :: !flag_pps;
		STR ""
	      end
	    else if is_phi then
	      begin
		flag_pps := (STR ": phi variable ") :: !flag_pps;
		STR ""
	      end
	    else STR "" in
      let pp_basic_num_type =
	if JCHSystemUtils.is_loop_counter variable then
          STR "loop counter"
	else
	  match basic_num_vtype with
          | Some t -> value_type_to_pretty t
          | None -> STR "unknown" in
      let pp_types =
	pretty_print_list vtypes value_type_to_pretty "{" ", " "}" in
      let pp_ops =
	pretty_print_list origin_operations operation_to_pretty "" "  " "" in
      LBLOCK [NL;
	      INDENT
                (2, LBLOCK
                      [variable#toPretty;
                       STR "("; INT variable#getIndex; STR ")";
                       LBLOCK !flag_pps; NL;
		       STR "origins: "; pp_list_int origins; NL;
		       STR "pc_in_scope: "; INT pc_in_scope; NL;
		       STR "type: "; pp_types; NL;
		       STR "basic numeric type: "; pp_basic_num_type; NL;
		       STR "constant: ";
                       (match const with Some c -> c#toPretty | _ -> STR "no");
                       NL;
		       STR (if is_numeric then "numeric" else "not numeric");
                       NL;
		       STR "first state: "; first_state#toPretty; NL;
		       STR "last states: "; pp_list last_states; NL;
		       STR "vars on which it is dependent: ";
                       pp_list read_vars; NL;
		       STR "origin operations "; pp_ops; NL;
		       STR "has_length: "; pp_bool !has_length;
                       (if origin_operations == [] then NL else STR "");
		       return_pp; NL])]


  end

let add_states var_to_var_to_eqs (cfg:cfg_int) =
  let add_states_vars
        (_var1: variable_t) (_var2: variable_t) (states:SymbolCollections.set_t) =
    let reachables = new SymbolCollections.set_t in
    let rec add_to_reach (state_name:symbol_t) =
      if reachables#has state_name then
        ()
      else
	begin
	  reachables#add state_name;
	  let state = cfg#getState state_name in
	  let out = state#getOutgoingEdges in
	  List.iter add_to_reach out
	end in
    states#iter add_to_reach;
    let removed = new SymbolCollections.set_t in
    let rec add_to_remove (check:bool) (state_name:symbol_t) =
      let remove (state:state_int) =
	removed#add state_name;
	let out = state#getOutgoingEdges in
	List.iter (add_to_remove false) out in
      if removed#has state_name || states#has state_name then
        ()
      else
	let state = cfg#getState state_name in
	if check then
	  let incoming = state#getIncomingEdges in
	  if List.exists
               (fun s -> not (reachables#has s) || removed#has s) incoming then
	    remove state
	  else
            remove state in
    reachables#iter (add_to_remove true);
    removed#iter reachables#remove;
    states#addSet reachables in
  let add_states_var (var1:variable_t) table =
    table#iter (add_states_vars var1) in
  var_to_var_to_eqs#iter add_states_var;
  var_to_var_to_eqs

(* Finds all the information needed to make jvar_info_t
 * for all the variables of the transformed CHIF *)
let make_jvar_infos
      ~(meth:method_int)
      ~(proc:procedure_int)
      ~(cfg:cfg_int)
      ~(lc_to_pc:(variable_t * int) list)
      ~(wto:CHSCC.wto_component_t list)
      ~(dom_info:JCHDominance.dominance_info_t)
      ~(aliases:JCHTransformUtils.alias_sets_t)
      ~(extra_assert_vars: SymbolCollections.set_t  VariableCollections.table_t) =
  let proc_name = proc#getName in
  let all_vars = proc#getScope#getVariables in
  let (origin_states,
       var_to_states,
       var_to_read_states,
       var_to_origins,
       phi_to_vars,
       var_to_rvars,
       return_pc_to_rvar,
       var_ops,
       var_to_var_to_eqs,
       var_to_var_to_ineqs,
       var_to_const,
       _var_to_pcs,
       var_to_read_pc,
       local_var_index_to_pc_to_var) =
    JCHVarInfoCollectors.collect_var_info proc meth in
  let var_to_type_list =
    JCHTypeUtils.get_types_from_stack_info proc_name proc phi_to_vars in
  let rev_dominance_info =
    new JCHRevDominance.rev_dominance_info_t proc_name cfg wto in
  let var_to_first = new VariableCollections.table_t in
  let set_first v =
    let f =
      if JCHSystemUtils.is_constant v then
	method_entry_sym
      else
	match origin_states#get v with
	| Some states_set ->
	    begin
	      let states = states_set#toList in
	      match dom_info#find_common_dominator states with
	      | [state] ->
		  if state#getBaseName = "pc=0" then
		    method_entry_sym
		  else
		    state
	      | _ ->
		  method_entry_sym end
	| None ->
	    method_entry_sym in
    var_to_first#set v f in
  let _ = List.iter set_first all_vars in
  let get_first_state (var:variable_t) =
    Option.get (var_to_first#get var) in

  let var_to_last = new VariableCollections.table_t in
  let entry_state_sym = cfg#getEntry#getLabel in
  let set_last v =
    let l =
      if JCHSystemUtils.is_constant v then
	SymbolCollections.set_of_list [method_exit_sym]
      else
	let all_states =
	  match (var_to_states#get v, extra_assert_vars#get v) with
	  | (Some states_set, Some extra_states) ->
	      states_set#addSet extra_states;
	      Some states_set
	  | (Some states_set, _) -> Some states_set
	  | (_, Some extra_states) -> Some extra_states
	  | _ -> None in
	match all_states with
	| Some set ->
	    begin
	      set#remove entry_state_sym;
	      set#add (get_first_state v);
	      let last_states =
                rev_dominance_info#find_rev_common_dominator set#toList in
	      SymbolCollections.set_of_list last_states
	    end
	| None ->
	    SymbolCollections.set_of_list [method_exit_sym] in
    var_to_last#set v l in
  let _ = List.iter set_last all_vars in

  let get_last_states (var:variable_t) =
    match var_to_last#get var with
    | Some states -> states#toList
    | None -> [method_exit_sym] in

  let get_read_states (var:variable_t) =
    match var_to_read_states#get var with
    | Some states -> states#toList
    | _ -> [] in

  let get_origins (var:variable_t) =
    match var_to_origins#get var with
    | Some set -> List.sort (fun l1 l2 -> compare l2 l1) set#toList
    | None -> [0] in

  let get_read_pc (var:variable_t) =
    match var_to_read_pc#get var with
    | Some set -> if set#isEmpty then 0 else Option.get set#choose
    | _ -> 0 in

  let aliased_locals = aliases#find_aliased_locals in
  let get_local_indices (var:variable_t) =
    let inds = new IntCollections.set_t in
    let add_index (var:variable_t) =
      let name = var#getName#getBaseName in
      if name.[0] = 'r' && name.[1] <> 'e' then
	inds#add (int_of_string (Str.string_after name 1))
      else () in
    add_index var;
    let others =
      List.filter (fun (_,r) -> var#getIndex = r#getIndex) aliased_locals in
    let other_locals = List.map fst others in
    List.iter add_index other_locals;
    List.sort compare inds#toList in

  let get_types (var:variable_t) =
    if List.mem_assoc var#getIndex var_to_type_list then
      List.assoc var#getIndex var_to_type_list
    else
      let type_list =
	if JCHSystemUtils.is_constant var then
          (* The contants are numeric *)
	  (TBasic Long) ::  (JCHTypeUtils.make_type_list (TBasic Int2Bool))
	else if JCHSystemUtils.is_temp var then
          (* The only temporary vars used are integers *)
	  (JCHTypeUtils.make_type_list (TBasic Int2Bool))
	else if JCHSystemUtils.is_number var then
	  (TBasic Long) ::  (JCHTypeUtils.make_type_list (TBasic Int2Bool))
	else
          [JCHTypeUtils.get_object_vt ()] in
      (type_list, false) in

  let numeric_vars = ref 0 in
  (* variables that could carry numeric info such as int, long, ...,
   * java.lang.Integer, ..., java.util.Collections, ..., java.lang.Object *)
  let number_vars = ref 0 in (* variables that have _num suffix *)

  let get_basic_type vtypes =
    let get_basic t =
      match t with
      | TBasic Void -> (None, false)
      | TBasic Object -> (None, true)
      | TBasic _ -> (Some t, true)
      |	TObject TClass cn ->
	  begin
	    match cn#name with
	    | "java.lang.Integer" -> (Some (TBasic Int) ,true)
	    | "java.lang.Short" -> (Some (TBasic Short), true)
	    | "java.lang.Character" -> (Some (TBasic Char), true)
	    | "java.lang.Byte" -> (Some (TBasic Byte), true)
	    | "java.lang.Long" -> (Some (TBasic Long), true)
	    | "java.lang.Float" -> (Some (TBasic Float), true)
	    | "java.lang.Double" -> (Some (TBasic Double), true)
	    | "java.math.BigInteger" -> (None, true)
	    | "java.math.BigDecimal" -> (None, true)
	    | _ -> (None, false)
	  end
      |	_ -> (None, false) in

    let get_basic_t t =
      match t with
      | TBasic _ -> get_basic t
      | TObject TArray vt ->
         get_basic vt   (* We do not want arrays of collections, etc *)
      | TObject TClass cn ->
	  begin
	    match cn#name with
	    | "java.lang.Integer" -> (Some (TBasic Int) ,true)
	    | "java.lang.Short" -> (Some (TBasic Short), true)
	    | "java.lang.Character" -> (Some (TBasic Char), true)
	    | "java.lang.Byte" -> (Some (TBasic Byte), true)
	    | "java.lang.Long" -> (Some (TBasic Long), true)
	    | "java.lang.Float" -> (Some (TBasic Float), true)
	    | "java.lang.Double" -> (Some (TBasic Double), true)
	    | "java.lang.Object" -> (None, true)
	    | _ ->
		if JCHTypeUtils.is_collection_class cn then (None, true)
		else (None, false)
	  end in

    let add_basic_type (basic_type_opt, is_numeric) vtype =
      let (basic_type_opt', _is_numeric') = get_basic_t vtype in
      let res_basic_type_opt =
	match (basic_type_opt, basic_type_opt') with
	| (Some (TBasic Bool), _) -> basic_type_opt'
	| (Some (TBasic Byte), Some (TBasic Bool)) -> basic_type_opt
	| (Some (TBasic Byte), _ ) -> basic_type_opt'
	| (Some (TBasic Char), Some (TBasic Bool))
	| (Some (TBasic Char), Some (TBasic Byte)) -> basic_type_opt
	| (Some (TBasic Char), Some (TBasic Short)) -> Some (TBasic Int)
	| (Some (TBasic Char), _ ) -> basic_type_opt'
	| (Some (TBasic Short), Some (TBasic Bool))
	| (Some (TBasic Short), Some (TBasic Byte)) -> basic_type_opt
	| (Some (TBasic Short), Some (TBasic Char)) -> Some (TBasic Int)
	| (Some (TBasic Short), _ ) -> basic_type_opt'
	| (Some (TBasic Int), Some (TBasic Bool))
	| (Some (TBasic Int), Some (TBasic Byte))
	| (Some (TBasic Int), Some (TBasic Char)) -> basic_type_opt
	| (Some (TBasic Int), _) -> basic_type_opt'
	| (Some (TBasic Long), Some (TBasic Bool))
	| (Some (TBasic Long), Some (TBasic Byte))
	| (Some (TBasic Long), Some (TBasic Char))
	| (Some (TBasic Long), Some (TBasic Int)) -> basic_type_opt
	| (Some (TBasic Long), _) -> basic_type_opt'
	| (Some (TBasic Float), Some (TBasic Double)) -> basic_type_opt'
	| (Some (TBasic Float), _) -> basic_type_opt
	| (Some (TBasic Double), _) -> basic_type_opt
	| (Some bt1, Some bt2) ->
	    if bt1 = bt2 then Some bt1
	    else None
	| _ -> None in
      (res_basic_type_opt, is_numeric) in

      match vtypes with
      | vtype :: rest_vtypes ->
	  List.fold_left add_basic_type (get_basic_t vtype) rest_vtypes
      | [] -> (None, false) in


  let get_const var = var_to_const#get var in

  (* This will work for phi variables because the other variables are
   * processed first, so the var_to_types will be set for the phi variable
   * before those types are needed *)
  let get_all_types (var:variable_t) =
    let (vtypes, has_length) = get_types var in
    if vtypes = [] then
      ch_error_log#add
        "Variables with no type "
	(LBLOCK [proc_name_pp proc_name; STR " no types found for ";
                 var#toPretty]);

    match var_to_const#get var with
    | Some c ->
       if JCHTypeUtils.integer_interval#contains c then
         (vtypes, Some (TBasic Int), true, false)
       else
         (vtypes, Some (TBasic Long), true, false)
    | _ ->
	begin
	  let (basic_type_opt, is_numeric) = get_basic_type vtypes in
	  if JCHSystemUtils.is_number var
             && Option.is_none (get_const var)
             && Option.is_none basic_type_opt then
	    begin
	      pr_debug [
                  proc_name#toPretty;
                  STR " numeric var without a basic type ";
                  var#toPretty; NL;
		  meth#toPretty; NL;
                  proc#toPretty; NL];
	      raise (JCH_failure (STR "basic type expected"))
	    end;
	  if is_numeric then incr numeric_vars;
	  if JCHSystemUtils.is_number var then incr number_vars;
	  if JCHSystemUtils.is_number var && not is_numeric then
	    ch_error_log#add
              "Numeric variable with wrong type"
	      (LBLOCK [proc_name_pp proc_name; STR " wrong vtypes found for ";
                       var#toPretty]);
	  (vtypes, basic_type_opt, is_numeric, has_length)
	end  in

  let get_read_vars (var:variable_t) =
    match var_to_rvars#get var with
    | Some pretty_list -> pretty_list#vars
    | None -> [] in

  let get_pc op = op.op_name#getSeqNumber in

  let get_ops (var:variable_t) =
    try
      let ops = List.assoc var#getIndex var_ops in
      let compare_op op1 op2 = compare (get_pc op1) (get_pc op2) in
      List.sort compare_op ops
    with _ -> [] in

  let phi_vars = phi_to_vars#listOfKeys in

  let phi_var_to_primary_deps = new VariableCollections.table_t in

  let process_phi_var (var:variable_t) =
    let vars_seen = new VariableCollections.set_t in
    let primary_deps = new VariableCollections.set_t in
    let rec add_deps v =
      if vars_seen#has v then ()
      else
	begin
	  vars_seen#add v;
	  match phi_to_vars#get v with
	  | Some set ->
	      set#iter add_deps
	  | None ->
	      primary_deps#add v
	end in
    add_deps var;
    phi_var_to_primary_deps#set var primary_deps in
  List.iter process_phi_var phi_vars;

  let var_infos = new VariableCollections.table_t in
  let sig_vars = JCHSystemUtils.get_signature_vars proc in

  let _ =                                                (* parameters *)
    let mk_sig_infos (i:int) (var:variable_t) =
      let index = var#getIndex in
      if index = num_return_var_index || index = sym_return_var_index then
	let (vtypes, basic_type_opt, is_numeric, has_length) = get_all_types var in
	let info =
	  new jvar_info_t
              ~variable:var
              ~param_index:(-1)
              ~is_phi:false
	      ~origins:(get_origins var)
              ~pc_in_scope:(get_read_pc var)
	      ~basic_num_vtype:basic_type_opt
              ~vtypes
              ~const:(get_const var)
              ~is_numeric
              ~has_length
	      ~first_state:method_entry_sym
              ~last_states:[method_exit_sym]
              ~read_states:(get_read_states var)
	      ~read_vars:(get_read_vars var)
	      ~return_pc_to_rvar:(Some return_pc_to_rvar)
              ~origin_operations:(get_ops var)
	      ~local_indices:(get_local_indices var) in
        begin
	  var_infos#set var info;
	  i
	end
      else if index = exception_var_index then
	let info =
	  new jvar_info_t
              ~variable:var
              ~param_index:(-1)
              ~is_phi:false
	      ~origins:[0]
              ~pc_in_scope:0
              ~basic_num_vtype:None
              ~vtypes:[JCHTypeUtils.get_throwable_vt ()]
              ~const:None
              ~is_numeric:false
              ~has_length:false
	      ~first_state:method_entry_sym
              ~last_states:[method_exit_sym]
              ~read_states:(get_read_states var)
	      ~read_vars:(get_read_vars var)
	      ~return_pc_to_rvar:None
              ~origin_operations:(get_ops var)
	      ~local_indices:(get_local_indices var) in
        begin
	  var_infos#set var info;
	  i
	end
      else
	let (vtypes, basic_type_opt, is_numeric, has_length) = get_all_types var in
	let info =
	  new jvar_info_t
              ~variable:var
              ~param_index:i
              ~is_phi:false
	      ~origins:[0]
              ~pc_in_scope:0
              ~basic_num_vtype:basic_type_opt
              ~vtypes
              ~const:None
              ~is_numeric
              ~has_length
	      ~first_state:method_entry_sym
              ~last_states:[method_exit_sym]
              ~read_states:(get_read_states var)
	      ~read_vars:(get_read_vars var)
	      ~return_pc_to_rvar:None
              ~origin_operations:(get_ops var)
              ~local_indices:(get_local_indices var) in
        begin
	  var_infos#set var info;
	  succ i;
	end in
    List.fold_left mk_sig_infos 0 sig_vars in

  let _ =                                                 (* SSA variables *)
    let mk_info var =
      if Option.is_some (phi_to_vars#get var) then
        () (* The non-phi variables need to be processed first for type info *)
      else if List.mem var sig_vars then
        ()
      else if JCHSystemUtils.is_loop_counter var then
	let info =
	  new jvar_info_t
              ~variable:var
              ~param_index:(-1)
              ~is_phi:false
	      ~origins:(get_origins var)
              ~pc_in_scope:(List.assoc var lc_to_pc)
              (* None for basic type so that is not wrapped when overflow *)
	      ~basic_num_vtype:None
              ~vtypes:[TBasic Int]
              ~const:None
              ~is_numeric:true
              ~has_length:false
	      ~first_state:(get_first_state var)
              ~last_states:(get_last_states var)
              ~read_states:(get_read_states var)
	      ~read_vars:(get_read_vars var)
	      ~return_pc_to_rvar:None
              ~origin_operations:(get_ops var)
              ~local_indices:(get_local_indices var) in
	var_infos#set var info
      else if JCHSystemUtils.is_length var then
	let info =
	  new jvar_info_t
              ~variable:var
              ~param_index:(-1)
              ~is_phi:false
	      ~origins:(get_origins var)
              ~pc_in_scope:(get_read_pc var)
	      ~basic_num_vtype:(Some (TBasic Int))
              ~vtypes:[TBasic Int]
              ~const:None
              ~is_numeric:true
              ~has_length:false
	      ~first_state:(get_first_state var)
              ~last_states:(get_last_states var)
              ~read_states:(get_read_states var)
	      ~read_vars:(get_read_vars var)
	      ~return_pc_to_rvar:None
              ~origin_operations:(get_ops var)
              ~local_indices:(get_local_indices var) in
	var_infos#set var info
      else
	let (vtypes, basic_type_opt, is_numeric, has_length) =
          get_all_types var in
	let info =
	  new jvar_info_t
              ~variable:var
              ~param_index:(-1)
              ~is_phi:false
	      ~origins:(get_origins var)
              ~pc_in_scope:(get_read_pc var)
	      ~basic_num_vtype:basic_type_opt
              ~vtypes
              ~const:(get_const var)
              ~is_numeric
              ~has_length
	      ~first_state:(get_first_state var)
              ~last_states:(get_last_states var)
              ~read_states:(get_read_states var)
	      ~read_vars:(get_read_vars var)
	      ~return_pc_to_rvar:None
              ~origin_operations:(get_ops var)
              ~local_indices:(get_local_indices var) in
	var_infos#set var info in
    List.iter mk_info all_vars in

  let _ =                                                 (* phi variables *)
    let mk_info phi_var =
      let index = phi_var#getIndex in
      if index = num_return_var_index
         || index = sym_return_var_index
         || index = exception_var_index then ()
      else
	let (vtypes, basic_num_type, is_numeric, has_length) =
          get_all_types phi_var in
	let info =
	  new jvar_info_t
              ~variable:phi_var
              ~param_index:(-1)
              ~is_phi:true
	      ~origins:(get_origins phi_var)
              ~pc_in_scope:(get_read_pc phi_var)
	      ~basic_num_vtype:basic_num_type
              ~vtypes
              ~const:None
              ~is_numeric
              ~has_length
	      ~first_state:(get_first_state phi_var)
              ~last_states:(get_last_states phi_var)
              ~read_states:(get_read_states phi_var)
	      ~read_vars:(get_read_vars phi_var)
	      ~return_pc_to_rvar:None
              ~origin_operations:(get_ops phi_var)
              ~local_indices:(get_local_indices phi_var) in
	var_infos#set phi_var info in
    List.iter mk_info phi_vars in

  (* change has_length for some vars *)
  let _ =
    let phis_to_check =
      ref (List.filter (fun info ->
               info#is_phi && info#has_length) var_infos#listOfValues) in
    let rec work (phi_infos:jvar_info_t list) =
      match phi_infos with
      | phi_info :: rest_phi_infos ->
	  let read_vars = phi_info#get_read_vars in
	  let new_phi_infos = ref rest_phi_infos in
	  let check var =
	    match var_infos#get var with
	    | Some info ->
		if not info#has_length then
		  begin
		    info#set_has_length true;
		    if info#is_phi then new_phi_infos := info :: !new_phi_infos
		  end
	    | _ -> () in
          begin
	    List.iter check read_vars;
	    work !new_phi_infos
          end
      | [] -> () in
    work !phis_to_check in

  (var_infos,
   add_states var_to_var_to_eqs cfg,
   add_states var_to_var_to_ineqs cfg,
   !numeric_vars,
   !number_vars,
   local_var_index_to_pc_to_var)

(* state -> vars that are not used after that state
 * symbolic, constants and loop_counter are not considered, and lengths
 * loop_counters are added / removed separately *)
let make_state_to_done_num_vars
      (var_infos: jvar_info_t VariableCollections.table_t) =
  let state_to_vars = new SymbolCollections.table_t in
  let add_var var_info =
    let var  = var_info#get_variable in
    let add_state (state:symbol_t) =
      if not (state = normal_exit_sym || state = method_exit_sym) then
	let vars =
	  if var_info#has_length then
	    [var; Option.get (fst var_info#get_length)]
	  else [var] in
	match state_to_vars#get state with
	| Some set ->
	   set#addList vars
	| None ->
	   let set = VariableCollections.set_of_list vars in
	   state_to_vars#set state set in
    let read_states = var_info#get_read_states in
    if JCHSystemUtils.is_constant var
       || JCHSystemUtils.is_loop_counter var
       || JCHSystemUtils.is_length var
       || JCHSystemUtils.is_return var then
      ()
    else if not (var_info#is_local_var || var_info#is_parameter)
            && List.length read_states = 1 then
      add_state (List.hd read_states)
    else
      List.iter add_state (var_info#get_last_states) in
  begin
    List.iter add_var (var_infos#listOfValues);
    state_to_vars
  end

(* state -> vars that are introduced in that state *)
let make_state_to_start_num_vars
      (var_infos:jvar_info_t VariableCollections.table_t) =
  let state_to_vars = new SymbolCollections.table_t in
  let add_var var_info =
    let var = var_info#get_variable in
    let state = var_info#get_first_state in
    if not var_info#is_numeric
       || JCHSystemUtils.is_constant var
       || JCHSystemUtils.is_loop_counter var
       || var_info#is_parameter then
      ()
    else
      match state_to_vars#get state with
      | Some set ->
	  set#add var
      | None ->
	  let set = VariableCollections.set_of_list [var] in
	  state_to_vars#set state set in
  begin
    List.iter add_var (var_infos#listOfValues);
    state_to_vars
  end

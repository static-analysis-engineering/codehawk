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

open Big_int_Z

(* chlib *)
open CHAtlas
open CHBounds
open CHDomain
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHAnalysisSetup
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTDictionary
open JCHJTerm

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHPreAPI
open JCHPreFileIO
open JCHPreSumTypeSerializer

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

module H = Hashtbl

let dbg = ref false

(* invariants saved during analysis by jch_op_semantics *)
let numeric_invs:domain_int IntCollections.table_t ref =
  ref (new IntCollections.table_t)     (* pc -> poly_int_dom *)

let old_numeric_invs:domain_int IntCollections.table_t ref =
  ref (new IntCollections.table_t)   (* pc -> poly_int_dom *)

let numeric_invariants = ref (H.create 3) (* cmsix -> pc -> poly_int_dom *)

let get_numeric_invariants (proc_name: symbol_t)  =
  try
    Some (H.find !numeric_invariants proc_name#getSeqNumber)
  with _ -> None

let max_loop_iterations = ref (H.create 3) (* cmsix -> pc -> poly_int_dom *)

let add_exit_loop (cmsix:int) (pc:int) (dom:domain_int) =
  let table: ('a, 'b) H.t =
    match H.find_opt !max_loop_iterations cmsix with
    | Some t -> t
    | _ ->
       let t = H.create 3 in

       (if !dbg then
          pr__debug [STR "add_exit_loop add "; INT cmsix; STR " "; INT pc; NL]);

       H.add !max_loop_iterations cmsix t;
       t in
  match H.find_opt table pc with
  | Some old_dom ->

     (if !dbg then
        pr__debug [STR "add_exit_loop replace "; INT cmsix; STR " "; INT pc; NL]);

     H.replace table pc (old_dom#join ?variables:(Some []) dom)
  | _ ->
     (if !dbg then
        pr__debug [STR "add_exit_loop add "; INT cmsix; STR " "; INT pc; NL]);

     H.add table pc dom

let get_exit_loop (cmsix:int) (pc:int) =

  (if !dbg then
     pr__debug [STR "get_exit_loop "; INT cmsix; STR " "; INT pc; NL]);

  match H.find_opt !max_loop_iterations cmsix with
  | Some table ->
      begin
	(if !dbg then
           pr__debug [STR "get_exit_loop found table"; NL]);

	match H.find_opt table pc with
	| Some dom ->

	   (if !dbg then
              pr__debug [STR "get_exit_loop found dom"; NL]);

	   Some dom
	| _ -> None
      end
  | _ -> None

module TypeCollections = CHCollections.Make
  (struct
     type t = value_type_t
     let compare = compare_value_types
     let toPretty = value_type_to_pretty
   end)

let change_stack_layout
      (proc_name:symbol_t)
      (jproc_info:JCHProcInfo.jproc_info_t)
      (invariant:atlas_t)
      (pc:int) =
  let poly_int_array =
    JCHPolyIntDomainNoArrays.get_poly_int_array
      (invariant#getDomain poly_dom_name) in
  let method_stack_layout =
    jproc_info#get_method_info#get_method_stack_layout in
  let stack_layout = method_stack_layout#get_stack_layout pc in
  let change_slot (slot:logical_stack_slot_int) =
    let var = slot#get_transformed_variable in
    let var_info = jproc_info#get_jvar_info var in
    let var_type = var_info#get_types in
    let slot_type = slot#get_type in

    if JCHTypeUtils.sub_value_type_lists var_type slot_type then
      if JCHSystemUtils.is_number var then
        begin
	  let vtype = Option.get (var_info#get_basic_num_type) in
	  let int =
	    let int = poly_int_array#get_interval var in
	    if slot#has_value then
	      let slot_interval =
	        try
		  JCHAnalysisUtils.get_slot_interval slot
	        with _ ->
                  begin
		    pr__debug [STR "Analysis failed: programming error: problem in get slot interval"; NL];
		    raise
                      (JCHAnalysisUtils.numeric_params#analysis_failed
                         3 "programming error: problem in get slot interval")
                  end in
	      int#join slot_interval
	    else
              int in
	  if JCHTypeUtils.is_bool vtype then
	    match int#singleton with
	    | Some num ->
	       slot#set_value (mk_boolconstant_jterm_range (num#equal numerical_one))
	    | _ -> ()
	  else
	    match vtype with
	    | TBasic Byte
	    | TBasic Short
	    | TBasic Char
	    | TBasic Int
	    | TBasic Int2Bool
	    | TBasic ByteBool ->
	       (try
	          let min_num =
		    match int#getMin#getBound with
		    | NUMBER min -> Some min
		    | _ -> None in
	          let max_num =
		    match int#getMax#getBound with
		    | NUMBER max -> Some max
		    | _ -> None in
	          slot#set_value (mk_intrange min_num max_num)
	        with _ ->
	          begin
		    pr__debug [ STR "expected integer bound: "; INT pc; STR " ";
			        var#toPretty; NL; proc_name#toPretty; NL;
			        invariant#toPretty; NL; jproc_info#toPretty; NL];
		    slot#set_value JCHJTerm.intminmax_jterm_range
	          end)
	    | TBasic Long ->
	       let min_long =
		 match int#getMin#getBound with
		 | NUMBER min -> Some min
		 | _ -> None in
	       let max_long =
		 match int#getMax#getBound with
		 | NUMBER max -> Some max
		 | _ -> None in
	       slot#set_value (mk_intrange min_long max_long)
	    | _ ->
	       let min_float =
		 match int#getMin#getBound with
		 | NUMBER min -> Some (float_of_big_int min#getNum)
		 | _ -> None in
	       let max_float =
		 match int#getMin#getBound with
		 | NUMBER max -> Some (float_of_big_int max#getNum)
		 | _ -> None in
	       slot#set_value (mk_floatrange min_float max_float)
        end in
  List.iter change_slot stack_layout#get_slots

(* taint analysis support *)

let local_var_maps = ref (H.create 0)

let set_local_var_maps (proc_name: symbol_t) (*invs*)  =
  let pc_table = new IntCollections.table_t in
  let add_pc_dom (pc, dom) =
    let map = JCHPolyIntDomainNoArrays.get_local_var_map dom in
    let map_table = new VariableCollections.table_t in
    List.iter (fun (v1, v2) -> map_table#set v1 v2) map;
    pc_table#set pc map_table in
  begin
    List.iter add_pc_dom !numeric_invs#listOfPairs;
    H.replace !local_var_maps proc_name#getSeqNumber pc_table
  end

let get_local_var_maps (proc_name: symbol_t) =
  try
    H.find !local_var_maps proc_name#getSeqNumber
  with _ -> new IntCollections.table_t



(* cost analysis support *)

module JTermCollections = CHCollections.Make
    (struct
      type t = jterm_t
      let compare j1 j2 = JCHJTerm.jterm_compare j1 j2
      let toPretty j = JCHJTerm.jterm_to_pretty j
    end)

let method_arg_lbounds =
  ref (new IntCollections.table_t)  (* cmsix -> pc -> arg no -> lower bounds *)

let method_arg_ubounds =
  ref (new IntCollections.table_t)  (* cmsix -> pc -> arg no -> upper bounds *)

let add_method_arg_bounds
      (is_lower:bool)
      (cmsix:int)
      (pc:int)
      ((var_jterm, bound): jterm_t * jterm_t) =
  let method_bounds =
    if is_lower then
      !method_arg_lbounds
    else
      !method_arg_ubounds in
  let cms_table =
    match method_bounds#get cmsix with
    | Some cms_table -> cms_table
    | _ ->
       let cms_table = new IntCollections.table_t in
       begin
         method_bounds#set cmsix cms_table;
         cms_table
       end in
  let pc_table =
    match cms_table#get pc with
    | Some pc_table -> pc_table
    | _ ->
       let pc_table = new JTermCollections.table_t in
       begin
         cms_table#set pc pc_table;
         pc_table
       end in

  match pc_table#get var_jterm with
  | Some set -> set#add bound
  | _ -> pc_table#set var_jterm (JTermCollections.set_of_list [bound])


let get_method_arg_bounds (cmsix:int) (pc:int) =
  let mk_lists (table: JTermCollections.set_t JTermCollections.table_t) =
    let lists = ref [] in
    let add (jterm_var, bounds) =
      lists := (jterm_var, bounds#toList) :: !lists in
    begin
      List.iter add table#listOfPairs;
      !lists
    end in
  let lbs =
    try
      let cms_table = Option.get (!method_arg_lbounds#get cmsix) in
      let pc_ltable = Option.get (cms_table#get pc) in

      begin
        (if !dbg then
           pr__debug [STR "ltable = "; NL; pc_ltable#toPretty; NL]);

        mk_lists pc_ltable
      end
    with _ -> [] in

  let ubs =
    try
      let cms_table = Option.get (!method_arg_ubounds#get cmsix) in
      let pc_utable = Option.get (cms_table#get pc) in
      begin

        (if !dbg then
           pr__debug [STR "utable = "; NL; pc_utable#toPretty; NL]);

        mk_lists pc_utable
      end
    with _ -> [] in

  (lbs, ubs)

(* cmsix -> head wto -> bounds *)
let iterations_lbs = ref (new IntCollections.table_t)

(* cmsix -> head wto -> bounds *)
let iterations_ubs = ref (new IntCollections.table_t)

let add_iteration_bounds
      (jproc_info:JCHProcInfo.jproc_info_t)
      (pc:int)
      (is_lb:bool)
      (bounds:jterm_t list) =
  let cmsix = jproc_info#get_name#getSeqNumber in
  let iterations = if is_lb then !iterations_lbs else !iterations_ubs in
  let table =
    match iterations#get cmsix with
    | Some table -> table
    | _ ->
       let table = new IntCollections.table_t in
       begin
	 iterations#set cmsix table;
	 table
       end in
  match table#get pc with
  | Some _ -> ()
  | _ ->
     let set = JTermCollections.set_of_list bounds in
     begin

       (if !dbg then
          pr__debug [STR "add_max_iterations "; INT pc; NL; set#toPretty; NL]);

       table#set pc set
     end

let get_iteration_bounds (cmsix:int) (pc:int) =
  let get_bounds iterations =
    match iterations#get cmsix with
    | Some table ->
	begin
	  match table#get pc with
	  | Some set -> set#toList
	  | _ -> []
	end
    | _ -> [] in
  (get_bounds !iterations_lbs, get_bounds !iterations_ubs)

let pos_fields = ref (new IntCollections.table_t)

let set_pos_fields () =
  let manager = JCHFields.int_field_manager in
  let fields = manager#get_all_num_fields in
  let pos_interval =
    new interval_t (bound_of_num numerical_zero) plus_inf_bound in
  let add_field field_info =
    let ints = manager#get_field_intervals field_info in
    if List.length ints >= 1 then
      begin
	let int = List.hd ints in
	if int#leq pos_interval then
	  begin
	    let cnix = field_info#get_class_name#index in
	    let jterm = JCHNumericUtils.get_field_term (-1) field_info in
	    let table =
	      match !pos_fields#get cnix with
	      | Some table -> table
	      | _ ->
		 let table = new JTermCollections.table_t in
                 begin
		   !pos_fields#set cnix table;
		   table
                 end in
	    table#set jterm int
	  end
      end in
  List.iter add_field fields

let is_pos_field (jterm:jterm_t) =
  try (* if jterm is not a field *)
    let cnix =
      match jterm with
      | JStaticFieldValue (cnix,_)
      | JObjectFieldValue (_,_,cnix, _) -> cnix
      | _ -> raise Exit in
    let is_same j =
      match (jterm, j) with
      | (JStaticFieldValue (cnix1,name1), JStaticFieldValue (cnix2,name2))
        | (JObjectFieldValue (_,_,cnix1,name1),
           JObjectFieldValue (_,_,cnix2,name2)) ->
	  cnix1 = cnix2 && name1 = name2
      | _ -> false in
    let res = match !pos_fields#get cnix with
    | Some table -> List.exists is_same table#listOfKeys
    | _ -> false  in
    res
  with _ -> false

let get_pos_field_interval (jterm:jterm_t) =
  try (* if jterm is not a field *)
    let cnix =
      match jterm with
      | JStaticFieldValue (cnix,_)
      | JObjectFieldValue (_,_,cnix, _) -> cnix
      | _ -> raise Exit in
    let is_same (j, _int) =
      match (jterm, j) with
      | (JStaticFieldValue (cnix1,name1), JStaticFieldValue (cnix2,name2))
        | (JObjectFieldValue (_,_,cnix1,name1),
           JObjectFieldValue (_,_,cnix2,name2)) ->
	  cnix1 = cnix2 && name1 = name2
      | _ -> false in
    match !pos_fields#get cnix with
    | Some table -> Some (snd (List.find is_same table#listOfPairs))
    | _ -> None
  with _ -> None

let geq_terms = ref (new IntCollections.table_t) (* cmsix -> join pc -> dom *)

let add_pos_terms
      (jproc_info:JCHProcInfo.jproc_info_t) (pc:int) geqs =
  let cmsix = jproc_info#get_name#getSeqNumber in
  match !geq_terms#get cmsix with
  | Some table ->
     table#set pc geqs
  | _ ->
     let table = new IntCollections.table_t in
     begin
       table#set pc geqs;
       !geq_terms#set cmsix table
     end

let get_pos_terms (cmsix:int) (pc:int) =
  match !geq_terms#get cmsix with
  | Some table ->
      begin
	match table#get pc with
	| Some set -> set#toList
	| _ -> []
      end
  | _ -> []

let get_bounds_var_
      (jproc_info: JCHProcInfo.jproc_info_t)
      (cmsix:int)
      (arg_jterm:jterm_t)
      jvar_info
      dom
      (var:variable_t)
      poly_int_array :(jterm_t * jterm_t) list * (jterm_t * jterm_t) list  =

  (if !dbg
   then pr__debug [STR "get_bounds_var_ "; NL]);

  let fields = poly_int_array#get_extra_infos#get_fields var in
  let get_field_bound field_info =
    let cnix = field_info#get_class_name#index in
    let field_name = field_info#get_class_signature#name in
    let field_jterm field_info =
      if field_info#is_static then
	JStaticFieldValue (cnix, field_name)
      else
	JObjectFieldValue (cmsix, -1, cnix, field_name) in
    if JCHSystemUtils.is_number var then
      if JCHNumericUtils.is_numeric field_info then
        [(arg_jterm, field_jterm field_info)]
      else
        [(arg_jterm, JSize (field_jterm field_info))]
    else
      [(arg_jterm, field_jterm field_info);
       (JSize arg_jterm, JSize (field_jterm field_info))]  in
  let field_bounds = List.concat (List.map get_field_bound fields) in
  let lbs = ref field_bounds in
  let ubs = ref field_bounds in

  let get_bounds_var_param p =

    (if !dbg then
       pr__debug [STR "get_bounds param ";
                  jterm_to_pretty arg_jterm; STR " ";
                  var#toPretty; STR " in arg"; INT p; NL]);

    let v_jterm = JLocalVar p in
    if jvar_info#has_length then
      let length_arg_jterm = JSize (arg_jterm) in
      let length_v_jterm = JSize (v_jterm) in
        begin
	lbs := [(arg_jterm, v_jterm); (length_arg_jterm, length_v_jterm)];
	ubs := [(arg_jterm, v_jterm); (length_arg_jterm, length_v_jterm)]
      end
    else
      begin
	lbs := [(arg_jterm, v_jterm)];
	ubs := [(arg_jterm, v_jterm)]
      end in

  let get_bounds_var_not_param () =
    try (* The variable might not be in poly *)

      (if !dbg then
         pr__debug [STR "get_bounds not param poly_int_array = "; NL;
                    poly_int_array#toPretty; NL]);

      let poly = poly_int_array#get_poly in
      let inds = poly#get_poly_inds in
      let var_to_index = poly_int_array#get_var_to_index in
      let find_poly_ind v =
	let index = v#getIndex in
	let is_ind (var_index, _ind) = var_index = index in
	let ind = snd (List.find is_ind var_to_index) in
	List.find (fun i -> i = ind) inds in
      let var_index = find_poly_ind var in
      let poly_vars = poly_int_array#get_poly_vars in
      let is_var_to_remove (v: variable_t) =
	if v#equal var then false
	else
	  begin
	    try (* v might not be in poly *)
	      let vinfo = jproc_info#get_jvar_info v in
	      if vinfo#is_length then
		let v' = Option.get (fst vinfo#get_variable_from_length) in
		let v'info = jproc_info#get_jvar_info v' in
		not v'info#is_parameter
	      else
                not vinfo#is_parameter
	    with _ ->  false
	  end in
      let vars_to_remove = List.filter is_var_to_remove poly_vars in
      let red_poly_int_array = poly_int_array#project_out vars_to_remove in
      begin
	if red_poly_int_array#get_poly#is_top then
          ()
	else
	  begin

            (if !dbg then
               pr__debug [ STR "get_bounds found arg ";
                           jterm_to_pretty arg_jterm; STR " ";
                           var#toPretty; STR " in poly"; NL;
			   red_poly_int_array#toPretty; NL]);

	    let add_bounds_from_constraint (lbs, ubs) constr =

	      (if !dbg then
                 pr__debug [
                     STR "get_bounds_from_constraint "; constr#toPretty; NL]);

	      let (pairs, const) = constr#get_pairs_const in
	      let get_index col =
		try
		  fst (List.find (fun (_ind, c) -> c = col) var_to_index)
		with _ ->
                  begin
                    pr__debug [STR "variable not found for column "; INT col; NL];
                    raise Exit
                  end in
	      let (res_pairs, const, _coeff, is_eq, is_leq) =
		let rec process (res_pairs, c) pairs =
		  match pairs with
		  | (col, cf) :: other_pairs ->
		      let ind = get_index col in
		      if ind = var_index then
			process (res_pairs, cf) other_pairs
		      else
			let v = List.find (fun v -> v#getIndex = ind) poly_vars in
			process ((v, cf) :: res_pairs, c) other_pairs
		  | [] -> (res_pairs, c) in
		let (ps, c) = process ([], zero_big_int) pairs in
		if ge_big_int c zero_big_int then
		  (List.map (fun (col, cf) -> (col, minus_big_int cf)) ps,
                   minus_big_int const,
		   c,
                   constr#is_equality,
                   false)
		else
		  (ps,
                   const,
                   minus_big_int c,
                   constr#is_equality,
                   not constr#is_equality) in
	      let jterm =
		if ge_big_int const zero_big_int then ref None
		else ref (Some (JConstant (mkNumerical_big const))) in
	      let add_pair (v, cf) =
		let info = jproc_info#get_jvar_info v in
		let var_jterm =
		  if info#is_length then
		    let corresp_v = Option.get (fst info#get_variable_from_length) in
		    let corresp_info = jproc_info#get_jvar_info  corresp_v in
		    let param = Option.get (corresp_info#get_param_index) in
		    JSize (JLocalVar param)
		  else
		    let param = Option.get info#get_param_index in
		    JLocalVar param in
		let prod_jterm =
		  if ge_big_int cf unit_big_int then
                    var_jterm
		  else
                    JArithmeticExpr(
                        JTimes, JConstant (mkNumerical_big cf), var_jterm) in
		match !jterm with
		| None -> jterm := Some prod_jterm
		| Some jt ->
                   jterm := Some (JArithmeticExpr(JPlus, jt, prod_jterm)) in
	      List.iter add_pair res_pairs;
	      let jterm = Option.get !jterm in
	      if is_eq then
                (jterm :: lbs, jterm :: ubs)
	      else if is_leq then
                (lbs, jterm :: ubs)
	      else
                (jterm :: lbs, ubs) in
	    let (ls, us) =
              List.fold_left
                add_bounds_from_constraint
                ([], []) red_poly_int_array#get_poly#get_constraints in
	    lbs := List.map (fun j -> (arg_jterm, j)) ls;
	    ubs := List.map (fun j -> (arg_jterm, j)) us
	  end
      end
    with _ ->
      begin
	try
	  let interv = JCHPolyIntDomainNoArrays.get_interval dom var in
	  (match interv#getMin#getBound with
	  | NUMBER n -> lbs := (arg_jterm, JConstant n) :: !lbs
	  | _ -> ());
	  (match interv#getMax#getBound with
	  | NUMBER n -> ubs := (arg_jterm, JConstant n) :: !ubs
	  | _ -> ())
	with _ -> ()
      end;
  in
  (match jvar_info#get_param_index with
  | Some p -> get_bounds_var_param p
  | _ -> get_bounds_var_not_param ());
  (!lbs, !ubs)



let get_bounds_var
      (jproc_info: JCHProcInfo.jproc_info_t)
      (cmsix:int)
      (arg_no:int)
      jvar_info
      dom
      (var:variable_t):(jterm_t * jterm_t) list * (jterm_t * jterm_t) list  =

  (if !dbg then
     pr__debug [STR "get_bounds_var arg_"; INT arg_no; STR " ";
                jvar_info#toPretty; NL; dom#toPretty; NL]) ;

  let arg_jterm = JLocalVar arg_no in
  match jvar_info#get_constant with
  | Some n -> ([(arg_jterm, JConstant n)], [(arg_jterm, JConstant n)])
  | _ ->
      begin
	let poly_int_array = JCHPolyIntDomainNoArrays.get_poly_int_array dom in

	(if !dbg then
           pr__debug [ STR "var not a constant, poly_int_array = "; NL;
                       poly_int_array#toPretty; NL]);
	try
	  match (poly_int_array#get_interval var)#singleton with
	  | Some n ->
             ([(arg_jterm, JConstant n)], [(arg_jterm, JConstant n)])
	  | _ ->
             get_bounds_var_
               jproc_info cmsix arg_jterm jvar_info dom var poly_int_array
	with _ ->
          get_bounds_var_
            jproc_info cmsix arg_jterm jvar_info dom var poly_int_array
      end

(* end support cost analysis *)

let poly_op_semantics
      ~(invariant:atlas_t)
      ~(stable: bool)
      ~(fwd_direction:bool)
      ~context
      ~operation =

  (if !dbg then
     pr__debug [STR "poly_op_semantics ";
                command_to_pretty 0 (OPERATION operation); NL]);

  let set_write_vars_to_top (invariant:atlas_t) =
    let write_vars = JCHSystemUtils.get_write_vars operation.op_args in
    invariant#analyzeFwd (ABSTRACT_VARS write_vars) in

  let mk_dom_op operation =
    DOMAIN_OPERATION
      ([poly_dom_name],
       { op_name = operation.op_name; op_args = operation.op_args }) in
  let pc = operation.op_name#getSeqNumber in
  match operation.op_name#getBaseName with
  | "init_params"
  | "init_assumptions"
  | "op_get_array_field"
  | "op_put_array_field" ->
    if fwd_direction then
      invariant#analyzeFwd (mk_dom_op operation)
    else invariant
  | "exit_loop" ->
      if fwd_direction && stable then
	begin

	  (if !dbg then
             pr__debug [STR "exit_loop stable"; NL]);

	  let wto_var =
            JCHSystemUtils.get_arg_var "loop_counter" operation.op_args in
	  let jproc_info = JCHAnalysisUtils.get_current_jproc_info () in
	  let cmsix =
            (JCHAnalysisUtils.get_current_proc_name ())#getSeqNumber in
	  let wto_info =
            List.find
              (fun w -> w#get_var#equal wto_var) jproc_info#get_wto_infos in
	  let pc = wto_info#get_entry_pc in
	  let pia = invariant#getDomain poly_dom_name in
          begin
	    add_exit_loop cmsix pc pia;
	    invariant
          end
	end
      else
	let op = {op_name = remove_vars_sym; op_args = operation.op_args} in
	invariant#analyzeFwd (mk_dom_op op)
  | "v" ->
      if fwd_direction && stable then
	begin
	  let new_dom =
	    let dom = invariant#getDomain poly_dom_name in
	    match !old_numeric_invs#get pc with
	    | Some old_dom ->
		dom#meet old_dom
	    | _ ->
		dom in
	  !numeric_invs#set pc new_dom;
	  if not invariant#isBottom
             && JCHAnalysisUtils.numeric_params#use_types then
	    begin
              let proc_name = JCHAnalysisUtils.get_current_proc_name () in
	      let jproc_info = JCHAnalysisUtils.get_current_jproc_info () in
	      change_stack_layout proc_name jproc_info invariant pc
	    end;
	  invariant
	end
      else
        invariant
  | "i"
  | "ii" ->
      begin
        let proc_name = JCHAnalysisUtils.get_current_proc_name () in
	let jproc_info = JCHAnalysisUtils.get_current_jproc_info () in
	let bcloc = get_bytecode_location proc_name#getSeqNumber pc in
	let iInfo = app#get_instruction bcloc in
	JCHPolyIntDomainNoArrays.set_instr_pc pc;

	(if stable
            && not invariant#isBottom
            && JCHAnalysisUtils.numeric_params#use_types then
	   let wvars = JCHSystemUtils.get_write_vars operation.op_args in
	   List.iter JCHPolyIntDomainNoArrays.add_reachable wvars);

	match iInfo#get_opcode with
	| OpPutStatic _
	| OpPutField _ ->
            if fwd_direction && not invariant#isBottom then
	      begin
		let var = JCHSystemUtils.get_arg_var "val" operation.op_args in
		if JCHAnalysisUtils.is_numeric jproc_info var then
		  begin
		    let constr_int_array =
                      JCHPolyIntDomainNoArrays.get_poly_int_array
                        (invariant#getDomain poly_dom_name) in
		    let fInfo = iInfo#get_field_target in
		    let interval = constr_int_array#get_interval var in
		    let length_interval =
		      let jvar_info = jproc_info#get_jvar_info var in
		      if jvar_info#has_length then
			let length = Option.get (jproc_info#get_length var) in
			[constr_int_array#get_interval length]
		      else
                        [] in
		    JCHFields.int_field_manager#put_field
                      proc_name fInfo interval length_interval true var;
                    (* CHANGE : bring back info about the length *)
		    if JCHAnalysisUtils.is_collection_or_array jproc_info var then
		      JCHPolyIntDomainNoArrays.add_variable_to_field var iInfo;
		  end
	      end;
	    if fwd_direction then
	      invariant#analyzeFwd (mk_dom_op operation)
	    else
	      JCHAnalysisUtils.jch_op_semantics
                ~invariant ~stable ~fwd_direction ~context ~operation
	| OpArrayLoad _
        | OpArrayStore _
	| OpNewArray _
	| OpCheckCast _
	| OpDiv Float
	| OpDiv Double
	| OpRem _
	| OpGetStatic _
	| OpGetField _
	| OpAMultiNewArray _
	| OpArrayLength
	| OpI2L
	| OpI2F
	| OpI2D
	| OpL2F
	| OpL2D
	| OpF2D
	| OpL2I
	| OpF2I
	| OpF2L
	| OpD2I
	| OpD2L
	| OpD2F
	| OpI2B
	| OpI2C
	| OpI2S
	| OpNew _
	| OpFloatConst _
	| OpDoubleConst _
	| OpAdd Float
	| OpAdd Double
	| OpSub Float
	| OpSub Double
	| OpMult Float
	| OpMult Double
	| OpIAnd
	| OpLAnd
	| OpIOr
	| OpLOr
	| OpStore _
	  ->
	    if fwd_direction then
	      invariant#analyzeFwd (mk_dom_op operation)
	    else
	      set_write_vars_to_top invariant
	| OpDiv _ -> (* This is analyzed by DIV *)
	    invariant
	| OpInvokeStatic _
	| OpInvokeSpecial _
	| OpInvokeInterface _
	| OpInvokeVirtual _ ->
	    if not JCHAnalysisUtils.numeric_params#create_model && stable then
              begin

		(if !dbg then
                   pr__debug [proc_name#toPretty; STR " "; INT pc;
                              STR " is method call"; NL;
                              command_to_pretty 0 (OPERATION operation); NL;
                              iInfo#toPretty; NL]);

		let dom = Option.get (!numeric_invs#get pc) in

		(if !dbg then
                   pr__debug [dom#toPretty; NL]);

		let func (s, v, _m) =
		  let cmsix = proc_name#getSeqNumber in
		  let arg_no = int_of_string (Str.string_after s 3) in
		  let (lbs, ubs) =
                    get_bounds_var
                      jproc_info cmsix arg_no (jproc_info#get_jvar_info v) dom v in

		  (if !dbg then
                     pr__debug [STR "after get_bounds_var for arg ";
                                INT arg_no; NL]);

		  (if !dbg then
                    pr__debug [STR "lbs = ";
			       pretty_print_list
                                 (List.map snd lbs)
                                 JCHJTerm.jterm_to_pretty "[" ", " "]"; NL]);

		  (if !dbg then
                     pr__debug [STR "ubs = ";
			        pretty_print_list
                                  (List.map snd ubs)
                                  JCHJTerm.jterm_to_pretty "[" ", " "]"; NL]);

		  List.iter (add_method_arg_bounds true cmsix pc) lbs;
		  List.iter (add_method_arg_bounds false cmsix pc) ubs in
		List.iter
                  func
                  (List.filter (fun (_, _, m) -> m = READ) operation.op_args)
	      end;
	    if fwd_direction then
	      invariant#analyzeFwd (mk_dom_op operation)
	    else
	      set_write_vars_to_top invariant
	| _ ->
	   JCHAnalysisUtils.jch_op_semantics
             ~invariant ~stable ~fwd_direction ~context ~operation
      end
  | _ ->
     begin
       (if fwd_direction && stable && not invariant#isBottom then
	  let wvars = JCHSystemUtils.get_write_vars operation.op_args in
	  List.iter  JCHPolyIntDomainNoArrays.add_reachable wvars
        else
          ());
       JCHAnalysisUtils.jch_op_semantics
         ~invariant ~stable ~fwd_direction ~context ~operation
     end

let reset_refs
      (first:bool) wto_pc_to_poly_int_array =

  (if !dbg then
     pr__debug [STR "reset_refs"; NL]);

  old_numeric_invs :=
    if first then new IntCollections.table_t  else !numeric_invs;
  if first then JCHPolyIntDomainNoArrays.set_invs wto_pc_to_poly_int_array;
  numeric_invs := new IntCollections.table_t;
  max_loop_iterations := (H.create 3)

let _get_num_invs () = !numeric_invs

let record_stub jproc_info procedure exit_dom =

  (if !dbg then
     pr__debug [STR "record_stub "; NL; exit_dom#toPretty; NL]);

  let vars =
    JCHAnalysisUtils.include_length_vars
      jproc_info (JCHSystemUtils.get_signature_vars procedure) in
  let restr_dom = JCHPolyIntDomainNoArrays.restrict_to_vars exit_dom vars in

  (if !dbg then
     pr__debug [STR "restr_dom = "; NL; restr_dom#toPretty; NL]);

  let pia = JCHPolyIntDomainNoArrays.get_poly_int_array restr_dom in
  let poly = pia#get_poly in
  let restr_poly_int_array =
    if poly#is_top || poly#is_bottom then
      pia
    else
      pia#simplify_with_intervals in
  let changed_sym_params =
    JCHPolyIntDomainNoArrays.get_changed_sym_params () in
  let changed_extra_infos =
    pia#get_extra_infos#add_changed_sym_params changed_sym_params in
  let changed_poly_int_array =
    restr_poly_int_array#set_extra_infos changed_extra_infos in

  (if !dbg then
     pr__debug [STR "changed_poly_int_array = ";
                changed_poly_int_array#toPretty; NL]);

  JCHIntStubs.int_stub_manager#mk_poly_int_array_stub
    procedure changed_poly_int_array;
  restr_poly_int_array#to_postconditions2 jproc_info

let _get_interval dom lvar =
  JCHPolyIntDomainNoArrays.get_interval dom lvar

(* It augments int_array with the numeric variables of proc that are not
 * in num_params *)
let add_all_vars jproc_info int_array num_params =
  let vars =
    List.filter
      (JCHAnalysisUtils.is_numeric jproc_info) jproc_info#get_variables in
  let param_inds = List.map (fun v -> v#getIndex) num_params in
  let is_other_var var =
    JCHAnalysisUtils.is_numeric
      jproc_info var && not (List.mem var#getIndex param_inds) in
  let other_vars = List.filter is_other_var vars in
  int_array#add_vars jproc_info other_vars

(* This accumulates methods not analyzed over all the passes. Methods that
 * are not analyzed in the first pass, will not be analyzed in the second
 * pass wither *)
let not_analyzed = new SymbolCollections.set_t
let analyzed_with_intervals = ref (new SymbolCollections.set_t)

let method_time_count = Array.make 21 0

let reset_analysis_counts () =
  begin
    analyzed_with_intervals := new SymbolCollections.set_t;
    for i = 0 to 20 do
      method_time_count.(i) <- 0
    done
  end

let print_method_time_count () =
  begin
    for i = 0 to 19 do
      pr__debug [STR "["; INT (5 * i); STR ", "; INT (5 * (i + 1));
                 STR ") seconds : ";
                 INT (method_time_count.(i)); NL]
    done;
    pr__debug [STR "[100, +oo) seconds : "; INT (method_time_count.(20)); NL];
    pr__debug [STR "Methods analyzed only with intervals: ";
               INT (!analyzed_with_intervals#size);
               STR " "; !analyzed_with_intervals#toPretty; NL];
    pr__debug [STR "Methods not analyzed: "; INT not_analyzed#size; STR " ";
               not_analyzed#toPretty; NL]
  end

let rec analyze_proc proc_name jproc_info procedure num_params init_dom =
  let analyzer = mk_analysis_setup () in
  analyzer#setOpSemantics poly_op_semantics;
  analyzer#setStrategy
    { CHIterator.widening =
        (fun i -> i >= JCHAnalysisUtils.numeric_params#number_joins, "");
      CHIterator.narrowing = (fun i -> i >= 2) };

  let count_numeric_vars = jproc_info#get_count_numeric_vars in
  let count_number_vars = jproc_info#get_count_number_vars in
  let loop_depth = jproc_info#get_loop_depth in
  let loop_number = jproc_info#get_loop_number in

  pr__debug [STR " "; proc_name#toPretty; STR " all vars analyzed: ";
             INT count_numeric_vars; STR "; vars of numeric types: ";
             INT count_number_vars;
	     (if count_numeric_vars > 50000 then
                STR " ** very many variables **"
              else
                STR "");
	     STR "; number of loops: "; INT loop_number;
             STR "; loop depth: "; INT loop_depth; NL];

  analyzer#addDomain poly_dom_name init_dom;
  if count_number_vars > 500 then
    JCHAnalysisUtils.numeric_params#set_use_intervals true; (* make it into a parameter *)
  JCHAnalysisUtils.numeric_params#start_numeric_analysis_time;
  try
    analyzer#analyze_procedure
      ~do_loop_counters:false JCHSystem.jsystem#get_transformed_chif procedure;

    pr__debug [STR " number of constraints: ";
               INT JCHAnalysisUtils.numeric_params#max_number_constraints; NL];

    (match (JCHAnalysisUtils.get_exit_invariant ()) with
    | Some invariant ->
	let dom = invariant#getDomain poly_dom_name in
	if JCHAnalysisUtils.numeric_params#use_intervals then
	  begin
	    pr__debug [STR "intervals used "; NL];
	    !analyzed_with_intervals#add proc_name
	  end;
	(dom, true)
    | None -> (JCHPolyIntDomainNoArrays.bottom_poly_int_dom jproc_info, true));
  with _ ->
    let n = JCHAnalysisUtils.numeric_params#get_analysis_status in
    if n <= 2 then
      begin
	JCHAnalysisUtils.numeric_params#reset_analysis_failure_status;
	if n = 2 then JCHAnalysisUtils.numeric_params#set_use_intervals true;

	pr__debug [STR "found error <= 2, reanalyzing with intervals";
                   proc_name#toPretty; NL];

	analyze_proc proc_name jproc_info procedure num_params init_dom;
      end
    else
      begin
	let message =
	  if JCHAnalysisUtils.numeric_params#get_analysis_status < 10 then
	    (JCHAnalysisUtils.numeric_params#get_analysis_failure_reason
             ^ " - abandoned")
	  else
            " out of time - abandoned" in
	pr__debug [STR " number of constraints: ";
                   INT JCHAnalysisUtils.numeric_params#max_number_constraints; NL];
	pr__debug [INT n; STR message; NL];
	(JCHPolyIntDomainNoArrays.top_poly_int_dom jproc_info num_params, false)
      end

(* Returns an initial poly_interval_array infered from the calls to the
 *  method or/ and types
 * in case of main or of if a library is analyzed and the method is
 * not private *)
let make_init_poly
      proc_name
      jproc_info
      known_calls
      sig_read_vars
      poly_params
      method_info
      use_widening
      use_narrowing
      _reset_use_intervals =

  (if !dbg then
     pr__debug [NL; STR "make_init_poly "; proc_name_pp proc_name;
	        STR (if known_calls then " known calls" else " unknown calls");
	        NL; pp_list poly_params; NL]);

  let start_with_unknown_params =
    method_info#is_main_method
    || method_info#is_dynamically_dispatched
    || method_info#is_called_by_reflection
    || method_info#is_indirectly_called in

  let var_to_index = JCHNumericUtils.mk_var_to_index poly_params in

  let make_type_interval_array () =
    JCHIntervalArray.make_from_types jproc_info poly_params in

  let (init_poly, init_interval_array, init_extra_infos) =
    if start_with_unknown_params then
      (JCHPoly.top_poly, make_type_interval_array (),
       new JCHNumericInfo.numeric_info_t)
    else
      begin
	let call_poly_interval_array_opt =
	  if use_narrowing then
            JCHIntStubs.int_stub_manager#get_narrowing_call_poly_int_array
              proc_name known_calls
	  else
            JCHIntStubs.int_stub_manager#get_widening_call_poly_int_array
              use_widening proc_name known_calls in

	match call_poly_interval_array_opt with
	| Some call_poly_interval_array ->
	    JCHIntStubs.int_stub_manager#reset_recursive_calls proc_name;
	    let call_poly = call_poly_interval_array#get_poly in
	    let call_interval_array =
              call_poly_interval_array#get_interval_array in
	    let call_extra_infos = call_poly_interval_array#get_extra_infos in
	    let inds_to_remove =
	      let inds = ref [] in
	      let rec add_ind vars ind =
		match vars with
		| v :: rest_vars ->
		   if not (JCHAnalysisUtils.is_numeric jproc_info v) then
                     inds := ind :: !inds;
		   add_ind rest_vars (succ ind)
		| _ -> () in
	      add_ind sig_read_vars 0;
	      !inds in
	    let red_poly = call_poly#project_out_and_remove inds_to_remove in
	    let red_interval_array =
	      let call_poly_vars = call_poly_interval_array#get_poly_vars in
	      let call_lengths =
                List.filter JCHSystemUtils.is_length call_poly_vars in
	      let dim = (List.length sig_read_vars) + (List.length call_lengths) in
	      call_interval_array#remove_entries dim inds_to_remove in
	    let add_type v =
	      let index = List.assoc v#getIndex var_to_index in
	      let var_info = jproc_info#get_jvar_info v in
	      let tp = var_info#get_basic_num_type in
	      let interval = JCHTypeUtils.get_var_interval_from_type v tp in
	      let new_interval = (red_interval_array#get index)#meet interval in
	      red_interval_array#set index new_interval in
	    List.iter add_type poly_params;
	    (red_poly,
             red_interval_array#set_type_intervals jproc_info poly_params,
             call_extra_infos)
	| None ->
           (JCHPoly.top_poly, make_type_interval_array (),
            new JCHNumericInfo.numeric_info_t)
      end in
  let var_to_const = JCHNumericUtils.get_constants jproc_info in
  let top_poly_int_array =
    JCHPolyIntervalArray.top_poly_interval_array var_to_const poly_params in
  let poly_int_array = top_poly_int_array#set_extra_infos init_extra_infos in
   (poly_int_array#set_poly init_poly)#set_interval_array init_interval_array


let run_poly_analysis
      proc_name
      jproc_info
      procedure
      method_info
      sig_read_vars
      poly_vars
      known_calls
      use_widening
      use_narrowing
      reset_old_join_widening
      reset_use_intervals =
  let init_poly_int_array =
    let pia =
      make_init_poly
        proc_name
        jproc_info
        known_calls
        sig_read_vars
        poly_vars
        method_info
        use_widening
        use_narrowing
        reset_use_intervals in
    add_all_vars jproc_info pia poly_vars in

  let init_poly_dom =
    JCHPolyIntDomainNoArrays.get_poly_dom
      jproc_info
      init_poly_int_array
      reset_old_join_widening
      reset_use_intervals in

  if not_analyzed#has proc_name then
    begin
      pr__debug [STR "skipped"; NL];
      (JCHPolyIntDomainNoArrays.top_poly_int_dom jproc_info poly_vars, false)
    end
  else
    analyze_proc proc_name jproc_info procedure poly_vars init_poly_dom



let run_analysis
      proc_name
      jproc_info
      procedure
      _method_info
      known_calls
      first =
  let sig_read_vars = JCHSystemUtils.get_signature_read_vars procedure in
  let poly_params =
    List.filter (JCHAnalysisUtils.is_numeric jproc_info) sig_read_vars in
  let mInfo = jproc_info#get_method_info in

  let poly_vars =
    let length_vars = ref [] in
    let add_var v =
      try
	let length = Option.get (jproc_info#get_length v) in
	length_vars := length :: !length_vars
      with _ -> () in
    List.iter add_var poly_params;
    poly_params @ !length_vars in

  if JCHSystem.jsystem#get_call_graph_manager#is_recursive proc_name then
    begin
      (* Running with the external calls *)
      pr__debug [STR "running with the external calls"; NL];
      let analyzed =
	ref
          (snd
             (run_poly_analysis
                proc_name
                jproc_info
                procedure
                mInfo
                sig_read_vars
                poly_vars
                known_calls
                false
                false
                first
                true)) in
      if !analyzed then
	begin
          (* Running with the external and internal calls generated *)

	  pr__debug [
              STR "running with the external and interval calls generated"; NL];

	  let res =
            ref
              (run_poly_analysis
                 proc_name
                 jproc_info
                 procedure
                 mInfo
                 sig_read_vars
                 poly_vars
                 known_calls
                 false
                 false
                 first
                 false) in
	  analyzed := snd !res;
	  if !analyzed then
	    begin
	      let count = ref 2 in
	      while !analyzed
                    && not (JCHIntStubs.int_stub_manager#are_recursive_calls_included_in_calls proc_name) do

		pr__debug [STR "recursive calls are not included in calls"; NL];

		if !count < 5 then
		  begin
		    res :=
                      run_poly_analysis
                        proc_name
                        jproc_info
                        procedure
                        mInfo
			sig_read_vars
                        poly_vars
                        known_calls
                        true
                        false
                        false
                        false; (* widen *)
		    analyzed := snd !res
		  end
		else
		  begin

		    pr__debug [STR "recursive calls are included in calls -> widen"; NL];

		    analyzed :=
                      snd
                        (run_poly_analysis
                           proc_name
                           jproc_info
                           procedure
                           mInfo
			   sig_read_vars
                           poly_vars
                           known_calls
                           true
                           false
                           false
                           false); (*widen *)
		    if !analyzed then
		      begin
			incr count;

			pr__debug [STR "narrow"; NL];

			res :=
                          run_poly_analysis
                            proc_name
                            jproc_info
                            procedure
                            mInfo
			    sig_read_vars
                            poly_vars
                            known_calls
                            false
                            true
                            false
                            false; (* narrow *)
			analyzed := snd !res;
		      end
		  end;
		incr count
	      done;
	      if !analyzed then
                !res
	      else
                (JCHPolyIntDomainNoArrays.top_poly_int_dom jproc_info poly_vars,
                 false)
	    end
	  else
            (JCHPolyIntDomainNoArrays.top_poly_int_dom jproc_info poly_vars, false)
	end
      else
        (JCHPolyIntDomainNoArrays.top_poly_int_dom jproc_info poly_vars, false)
    end
  else
    run_poly_analysis
      proc_name
      jproc_info
      procedure
      mInfo
      sig_read_vars
      poly_vars
      known_calls
      false
      false
      first
      true

(* Finds poly invariants. If known_calls then it will use the call poly
 * found in the current analysis of the system. Otherwise it will use the
 * one found in the previousyes iteration *)
let make_numeric_analysis_proc
      proc_name jproc_info procedure known_calls first =

  pr__debug [STR " "; proc_name_pp proc_name; NL];

  JCHPolyIntDomainNoArrays.dbg := !dbg;

  let mInfo = jproc_info#get_method_info in
  JCHSystemUtils.start_time ();

  let (exit_dom, analyzed) =
    run_analysis proc_name jproc_info procedure mInfo known_calls first in
  let time = JCHSystemUtils.get_time () in

  pr__debug [STR (string_of_float time); STR " seconds"; NL];

  let fives = int_of_float (time /. 5.) in
  (if fives > 19 then
     method_time_count.(20) <- method_time_count.(20) + 1
   else
     method_time_count.(fives) <- method_time_count.(fives) + 1);
  let _ = record_stub jproc_info procedure exit_dom in
  analyzed

let total_loop_count = ref 0
let infinite_loop_count = ref 0
let _get_total_loop_count () = !total_loop_count
let _get_infinite_loop_count () = !infinite_loop_count

let reset_loop_counts () =
  total_loop_count := 0;
  infinite_loop_count := 0

(* taint analysis support *)
let unreachable_vars = ref (H.create 0)

let is_unreachable (proc_name: symbol_t) (var: variable_t) =
  try
    let set = H.find !unreachable_vars proc_name#getSeqNumber in
    set#has var#getIndex
  with _ -> false
(* end *)

let record_analyzed
      _jproc_info
      proc
      proc_name
      (_in_bounds,
       _out_of_bounds,
       _no_info,
       _over,
       _under,
       _truncations,
       reach,
       _div0) =
  let all_vars = proc#getScope#getVariables in
  let unreach =
    List.filter (fun v ->
        not ((reach#has v)
             (* we do not analyze exceptions well *)
             || JCHSystemUtils.is_exception v)) all_vars in
  let unreach =
    IntCollections.set_of_list (List.map (fun v -> v#getIndex) unreach) in
  H.replace !unreachable_vars proc_name#getSeqNumber unreach


let set_invariants_and_loop_info jproc_info wtos =

  (if !dbg then
     pr__debug [STR "set_invariants "; jproc_info#get_name#toPretty; NL;
                pp_list_int (List.map fst wtos); NL]);

  let analysis_results = jproc_info#get_analysis_results in
  let set_loop_info (pc: int) dom =

    (if !dbg then
       pr__debug [STR "set_loop_info "; INT pc; NL]);

    try
      let (_, wto_info) = List.find (fun (entry, _) -> entry = pc) wtos in

      (if !dbg then
         pr__debug [STR "set_max_iterations for "; jproc_info#get_name#toPretty;
                    STR " "; INT pc; NL; dom#toPretty; NL]);

      let rel_exprs = JCHPolyIntDomainNoArrays.get_relational_exprs true dom in

      (if !dbg then
         pr__debug [STR "rel_exprs ";
                    pretty_print_list
                      rel_exprs
                      JCHJTerm.relational_expr_to_pretty
                      "[" "; " "]"; NL]);

      incr total_loop_count;
      let (lbounds, ubounds) =
        JCHNumericUtils.get_loop_counter_bounds rel_exprs wto_info#get_first_pc in

      (if !dbg then
         pr__debug [STR "add_iteration lbounds = "; INT pc; STR " ";
                    pretty_print_list
                      lbounds JCHJTerm.jterm_to_pretty "[" "; " "]"; NL]);

      (if !dbg then
         pr__debug [STR "add_iteration ubounds = "; INT pc; STR " ";
                    pretty_print_list
                      ubounds JCHJTerm.jterm_to_pretty "[" "; " "]"; NL]);

      wto_info#set_max_iterations ubounds;

      (* cost analysis support *)
      if not JCHAnalysisUtils.numeric_params#create_model then
	begin
	  let vars =
	    wto_info#get_var ::
	      (JCHAnalysisUtils.include_length_vars
                 jproc_info (JCHSystemUtils.get_signature_vars
                               jproc_info#get_procedure)) in

	  match get_exit_loop jproc_info#get_name#getSeqNumber pc with
	  | Some dom ->
	      begin
		let interval =
                  (JCHPolyIntDomainNoArrays.get_poly_int_array dom)#get_interval
                    wto_info#get_var in
		match interval#singleton with
		| Some n ->
		    let bounds = [JConstant n] in
		    add_iteration_bounds jproc_info pc true bounds;
		    add_iteration_bounds jproc_info pc false bounds;
		| _ ->
		   let rel_exprs =
                     JCHPolyIntDomainNoArrays.get_relational_exprs_vars_fields
                       dom vars in

		   (if !dbg then
                      pr__debug [STR "rel_exprs ";
                                 pretty_print_list
                                   rel_exprs JCHJTerm.relational_expr_to_pretty
                                   "[" "; " "]"; NL]);

		   let (lbounds, ubounds) =
                     JCHNumericUtils.get_loop_counter_bounds
                       rel_exprs wto_info#get_first_pc in
		    add_iteration_bounds jproc_info pc true lbounds;
		    add_iteration_bounds jproc_info pc false ubounds;
	      end
	  | _ -> () (* no exit conditions *)
	end
      with _ -> () in
    (* end cost_analysis support *)

  let set_pc pc dom =
    let dom = JCHPolyIntDomainNoArrays.remove_duplicates dom in
    let rel_exprs = JCHPolyIntDomainNoArrays.get_relational_exprs false dom in
    set_loop_info pc dom;
    analysis_results#set_invariants pc rel_exprs;
    if not JCHAnalysisUtils.numeric_params#create_model then
      begin
	let vars =
          (JCHAnalysisUtils.include_length_vars
             jproc_info
	     (JCHSystemUtils.get_signature_vars jproc_info#get_procedure)) in
	let restr_dom = JCHPolyIntDomainNoArrays.restrict_to_vars dom vars in
	let rel_exprs =
          JCHPolyIntDomainNoArrays.get_relational_exprs true restr_dom in
	let geqs = ref [] in
	let get_jterms rel_expr =
	  match rel_expr with
	  | (JGreaterEqual, jterm1, jterm2) ->
	     geqs :=
               (JArithmeticExpr (JPlus,
                                 jterm1,
                                 JCHNumericUtils.negate_jterm jterm2)) :: !geqs
	  | (JLessEqual, jterm1, jterm2) ->
	     geqs :=
               (JArithmeticExpr (JPlus,
                                 jterm2,
                                 JCHNumericUtils.negate_jterm jterm1)) :: !geqs
	  | (JEquals, jterm1, jterm2) ->
	     geqs :=
               (JArithmeticExpr (JPlus,
                                 jterm1,
                                 JCHNumericUtils.negate_jterm jterm2)) :: !geqs;
	     geqs :=
               (JArithmeticExpr (JPlus,
                                 jterm2,
                                 JCHNumericUtils.negate_jterm jterm1)) :: !geqs
	  | _ -> () in
	List.iter get_jterms rel_exprs;
	add_pos_terms jproc_info pc (JTermCollections.set_of_list !geqs)
      end in
  !numeric_invs#iter set_pc


let make_numeric_analysis bottom_up =
  let system = JCHSystem.jsystem#get_transformed_chif in
  let call_graph_manager = JCHSystem.jsystem#get_call_graph_manager in
  reset_analysis_counts ();
  reset_loop_counts ();
  let (procs, in_loop) =
    if bottom_up then
      call_graph_manager#get_bottom_up_list
    else call_graph_manager#get_top_down_list in
  if bottom_up then
    begin
      numeric_invariants := H.create JCHSystem.jsystem#get_number_procs;
      unreachable_vars := H.create  JCHSystem.jsystem#get_number_procs
    end;
  List.iter (fun name ->
      JCHIntStubs.int_stub_manager#mk_proc_call (system#getProcedure name)) procs;
  let number_method_analyzed = ref 0 in
  let get_p proc_name =
    let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
    let proc = system#getProcedure proc_name in
    incr number_method_analyzed;
    let known_calls =
      not (bottom_up || in_loop#has proc_name) in
    JCHAnalysisUtils.set_current_proc_name proc_name;

    let prev_pc_to_wto_pc = jproc_info#get_wto_prev_pc_to_entry_pcs in
    JCHPolyIntDomainNoArrays.set_prev_pc_to_wto_pc prev_pc_to_wto_pc;
    let wto_pcs = List.sort_uniq compare (List.map snd prev_pc_to_wto_pc) in
    let mk_wto_pc_to_poly_int_array num_invs =
      let table = new IntCollections.table_t in
      let add wto_pc =
	match num_invs#get wto_pc with
	| Some inv ->
	    let poly_int_array = JCHPolyIntDomainNoArrays.get_poly_int_array inv in
	    table#set wto_pc poly_int_array
	| _ ->
	    begin
	      match get_numeric_invariants proc_name with
	      |	Some old_num_invs ->
		  begin
		    match old_num_invs#get wto_pc with
		    | Some inv ->
		       let poly_int_array =
                         JCHPolyIntDomainNoArrays.get_poly_int_array inv in
			table#set wto_pc poly_int_array
		    | _ -> ()
		  end
	      |	_ -> ()
	    end in
      List.iter add wto_pcs;
      table in

    let analyze
          first
          analyzed
          joins
          max_coeff
          nr_vars
          nr_constrs
          use_loop_counters
          use_lengths
          useoverflow
          level =
      let nr_joins = JCHAnalysisUtils.numeric_params#number_joins in
      let analysis_level = JCHAnalysisUtils.numeric_params#analysis_level in
      let use_overflow = JCHAnalysisUtils.numeric_params#use_overflow in

      pr__debug [NL; NL; STR "start analyze "; proc_name#toPretty; STR " ";
                 pp_bool analyzed; STR " joins = "; INT joins;
                 STR " level = "; INT level; NL];

      if analyzed then
	begin
	  reset_refs first (mk_wto_pc_to_poly_int_array !numeric_invs);
	  JCHAnalysisUtils.numeric_params#set_number_joins joins;
	  JCHAnalysisUtils.numeric_params#set_max_poly_coefficient max_coeff;
	  JCHAnalysisUtils.numeric_params#set_max_number_vars_in_constraint_allowed
            nr_vars;
	  JCHAnalysisUtils.numeric_params#set_max_number_constraints_allowed
            nr_constrs;
	  JCHAnalysisUtils.numeric_params#set_use_loop_counters use_loop_counters;
	  JCHAnalysisUtils.numeric_params#set_use_lengths use_lengths;
	  JCHAnalysisUtils.numeric_params#set_use_overflow useoverflow;
	  JCHAnalysisUtils.numeric_params#set_analysis_level level;
	  let res =
            make_numeric_analysis_proc
              proc_name jproc_info proc known_calls first in
	  if jproc_info#get_count_number_vars < 500 then
	    begin

	      (if !dbg then
                 pr__debug [STR "after end analysis with nr_vars ";
                            INT nr_vars; STR " "; pp_bool res; NL]);

	      (if !dbg then
                 pr__debug [STR "   the invariants are: "; NL]);

	      (if !dbg then
                 pr__debug_large_table
		   (fun dom ->
                     let pia = JCHPolyIntDomainNoArrays.get_poly_int_array dom in
		     pia#pr__debug_large_poly_interval_array) !numeric_invs);

	      (if !dbg then
                 pr__debug [NL]);

	    end
	  else

            (if !dbg then
               pr__debug [STR "after end analysis with large nr_vars ";
                          INT nr_vars; STR " "; pp_bool res; NL]);

	  let proc_results = JCHPolyIntDomainNoArrays.get_proc_info () in
	  record_analyzed jproc_info proc proc_name proc_results;
	  JCHAnalysisUtils.numeric_params#set_number_joins nr_joins;
	  JCHAnalysisUtils.numeric_params#set_analysis_level analysis_level;
	  JCHAnalysisUtils.numeric_params#set_use_overflow use_overflow;
	  res
	end
      else
        false in

    let analyzed =
      if JCHAnalysisUtils.numeric_params#analysis_level = 0 then
	begin

	  (if !dbg then
             pr__debug [STR "analyze "; proc_name#toPretty;
                        STR " with analysis_level = 0"; NL]);

	  analyze
            true
            true
            JCHAnalysisUtils.numeric_params#number_joins
            100
            3
            20
            true
            true
            true
            0
	end
      else if List.length jproc_info#get_wto_infos = 0 then
	begin

	  (if !dbg then
             pr__debug [STR "analyze "; proc_name#toPretty;
                        STR " with analysis_level > 0 and with no loops"; NL]);

	  analyze
            true
            true
            JCHAnalysisUtils.numeric_params#number_joins
            20
            4
            20
            true
            true
	    JCHAnalysisUtils.numeric_params#use_overflow
            JCHAnalysisUtils.numeric_params#analysis_level
	end
      else if not JCHAnalysisUtils.numeric_params#use_overflow then
	begin

	  (if !dbg then
             pr__debug [STR "analyze "; proc_name#toPretty;
                        STR " without overflow "; NL]);

	  let res =
            analyze
              true
              true
              JCHAnalysisUtils.numeric_params#number_joins
              100
              3
              20
              true
              true
              false
              JCHAnalysisUtils.numeric_params#analysis_level in
	  res
	end
      else if JCHAnalysisUtils.numeric_params#analysis_level > 1 then
	begin

	  (if !dbg then
             pr__debug [STR "analyze "; proc_name#toPretty;
                        STR " with analysis_level > 1 "; NL]);

	  let res =
            analyze
              true
              true
              JCHAnalysisUtils.numeric_params#number_joins
              100
              2
              20
              true
              true
              true
              1 in
	  let res =
            analyze
              false
              res
              1
              100
              3
              20
              true
              true
              true
              JCHAnalysisUtils.numeric_params#analysis_level in
	  res
	end
      else
	begin

	  (if !dbg then
             pr__debug [STR "analyze "; proc_name#toPretty;
                        STR " with loops, overflow and analysis_level = 1 "; NL]);

	  let res =
            analyze
              true
              true
              JCHAnalysisUtils.numeric_params#number_joins
              100
              2
              20
              true
              true
              true
              1 in
	  let res =
            analyze
              false
              res
              2
              100
              3
              20
              true
              true
              true
              1 in
	  res
	end in

    if analyzed then
      begin
	H.replace !numeric_invariants proc_name#getSeqNumber !numeric_invs;
        if not bottom_up then
	  let wto_infos =
            List.map (fun wto ->
                (wto#get_entry_pc, wto)) jproc_info#get_wto_infos in
          begin
	    set_invariants_and_loop_info jproc_info wto_infos;
	    set_local_var_maps proc_name
	  end
      end
    else
      begin
	JCHFields.int_field_manager#set_unknown_fields jproc_info;
	not_analyzed#add proc_name;
      end in
  List.iter get_p procs;

  pr__debug [NL; NL; STR "Finished a numeric analysis pass of all methods "; NL;
	     STR "The number of methods analyzed: ";
             INT !number_method_analyzed; NL];
  JCHPolyIntDomainNoArrays.print_lost_info ();
  print_method_time_count ()


(* --------------------------------------------------------- save/load xml -- *)

(* taint analysis support *)

let write_xml_unreachable_vars (node: xml_element_int) set =
  let mk_node var_index =
    let vnode = xmlElement "var" in
    begin
      vnode#setIntAttribute "var_index" var_index;
      vnode
    end in
  node#appendChildren (List.map mk_node set#toList)

let read_xml_unreachable_vars (node:xml_element_int) =
  let get_var_index nd = nd#getIntAttribute "var_index" in
  IntCollections.set_of_list (List.map get_var_index (node#getTaggedChildren "var"))

let write_xml_symbol (node:xml_element_int) (s:symbol_t) =
  node#setIntAttribute "seqnr" s#getSeqNumber;
  node#setAttribute "name" s#getBaseName;
  let mk_att_node att =
    let att_node = xmlElement "att" in
    begin
      att_node#setAttribute "att" att;
      att_node
    end in
  node#appendChildren (List.map mk_att_node s#getAttributes)

let read_xml_symbol (node:xml_element_int): symbol_t =
  let seqnr = node#getIntAttribute "seqnr" in
  let name = node#getAttribute "name" in
  let get_att nd = nd#getAttribute "att" in
  let atts =
    List.map get_att (node#getTaggedChildren "att") in (* They might not be in the same order *)
  new symbol_t ~atts ~seqnr name

let write_xml_variable (node: xml_element_int) (v: variable_t) =
  begin
    node#setAttribute
      "type" (variable_type_mfts#ts v#getType);
    write_xml_symbol node v#getName
  end

let read_xml_variable (node: xml_element_int): variable_t =
  let t = variable_type_mfts#fs (node#getAttribute "type") in
  let name_sym = read_xml_symbol node in
  new variable_t name_sym t

let write_xml_local_var_map
      (node: xml_element_int) (local_var_map: variable_t VariableCollections.table_t) =
  let mk_pair_nd (original_var, version_var) =
    let pair_nd = xmlElement "pair" in
    let orig_nd = xmlElement "orig_var" in
    write_xml_variable orig_nd original_var;
    let vers_nd = xmlElement "vers_var" in
    write_xml_variable vers_nd version_var;
    pair_nd#appendChildren [orig_nd; vers_nd];
    pair_nd in
  node#appendChildren (List.map mk_pair_nd local_var_map#listOfPairs)

let read_xml_local_var_map (node: xml_element_int) =
  let table = new VariableCollections.table_t in
  let read_pair nd =
    let orig_nd = nd#getTaggedChild "orig_var" in
    let vers_nd = nd#getTaggedChild "vers_var" in
    table#set (read_xml_variable orig_nd) (read_xml_variable vers_nd) in
  begin
    List.iter read_pair (node#getTaggedChildren "pair");
    table
  end

let write_xml_local_var_maps
      (node: xml_element_int)
      (local_var_maps: variable_t VariableCollections.table_t IntCollections.table_t) =
  let mk_map_nd (pc, table) =
    let map_nd = xmlElement "map" in
    begin
      map_nd#setIntAttribute "pc" pc;
      write_xml_local_var_map map_nd table;
      map_nd
    end in
  node#appendChildren (List.map mk_map_nd local_var_maps#listOfPairs)

let read_xml_local_var_maps (node: xml_element_int) =
  let table = new IntCollections.table_t in
  let read_map nd =
    let pc = nd#getIntAttribute "pc" in
    let t = read_xml_local_var_map nd in
    table#set pc t in
  begin
    List.iter read_map (node#getTaggedChildren "map");
    table
  end

let write_xml_method_taint_support
      (node:xml_element_int) (cms:class_method_signature_int) =
  let cmsix = cms#index in
  begin
    node#setIntAttribute "cmsix" cmsix;
    (try
       let set = H.find !unreachable_vars cmsix in
       let unode = xmlElement "unreachable" in
       begin
         write_xml_unreachable_vars unode set;
         node#appendChildren [unode]
       end
     with _ -> ());
    try
      let local_var_maps = H.find !local_var_maps cmsix in
      let lnode = xmlElement "local_var_maps" in
      begin
        write_xml_local_var_maps lnode local_var_maps;
        node#appendChildren [lnode]
      end
    with _ -> ()
  end

let read_xml_method_taint_support  (node:xml_element_int) =
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let cmsix = node#getIntAttribute "cmsix" in
  (if hasc "unreachable_vars" then
     begin
       let unreach = read_xml_unreachable_vars (getc "unreachable_vars") in
       if not unreach#isEmpty then H.replace !unreachable_vars cmsix unreach
     end);
  (if hasc "local_var_maps" then
     begin
       let lvar_maps = read_xml_local_var_maps (getc "local_var_maps") in
       if lvar_maps#size != 0 then H.replace !local_var_maps cmsix lvar_maps
     end)

let write_xml_class_taint_support (node:xml_element_int) (cInfo:class_info_int) =
  let mmNode = xmlElement "methods" in
  let cn = cInfo#get_class_name in
  begin
    mmNode#appendChildren
      (List.map (fun ms ->
        let cms = make_cms cn ms in
        let mNode = xmlElement "method" in
        begin write_xml_method_taint_support mNode cms; mNode end)
         cInfo#get_methods_defined);
    node#appendChildren [ mmNode]
  end

let _read_xml_class_taint_support (node:xml_element_int) =
  let name = node#getAttribute "name" in
  let package = node#getAttribute "package" in
  try
    List.iter read_xml_method_taint_support
      ((node#getTaggedChild "methods")#getTaggedChildren "method");
  with
  | XmlDocumentError (line,col,p)
    | XmlParseError (line,col,p) ->
     raise
       (JCH_failure (
            LBLOCK [STR "Xml error in "; STR package; STR ".";
                    STR name; STR ": (";
                    INT line; STR ","; INT col; STR "): "; p]))


let save_xml_class_taint_support (cInfo:class_info_int) =
  if cInfo#is_stubbed || cInfo#is_missing then () else
    let cn = cInfo#get_class_name in
    let node = xmlElement "class" in
    begin
      write_xml_class_taint_support node cInfo;
      node#setAttribute "name" cn#simple_name;
      node#setAttribute "package" cn#package_name;
      save_xml_taint_support_data cn node "class";
    end

(* cost analysis support *)

let write_xml_bounds (node:xml_element_int) (bounds:jterm_t list) =
  jtdictionary#write_xml_jterm_list node bounds

let read_xml_bounds (node:xml_element_int):jterm_t list =
  if node#hasNamedAttribute "ijtl" then
    jtdictionary#read_xml_jterm_list node
  else
    []

let write_xml_geq_terms (node:xml_element_int) t =
  let pairs = t#listOfPairs in
  node#appendChildren
    (List.map (fun (joinpc,bounds) ->
         let jnode = xmlElement "join" in
         begin
           jnode#setIntAttribute "pc" joinpc;
           write_xml_bounds jnode bounds#toList;
           jnode
         end) pairs)

let read_xml_geq_terms (node:xml_element_int) t =
  List.iter (fun n ->
      let pc = n#getIntAttribute "pc" in
      let bounds = JTermCollections.set_of_list (read_xml_bounds n) in
      t#set pc bounds) (node#getTaggedChildren "join")

let write_xml_iterations (node:xml_element_int) t =
  let pairs = t#listOfPairs in
  node#appendChildren
    (List.map (fun (headwto,bounds) ->
         let jnode = xmlElement "wtohead" in
         begin
           jnode#setIntAttribute "pc" headwto;
           write_xml_bounds jnode bounds#toList;
           jnode
         end) pairs)

let read_xml_iterations (node:xml_element_int) t =
  List.iter (fun n ->
      let pc = n#getIntAttribute "pc" in
      let bounds = JTermCollections.set_of_list (read_xml_bounds n) in
      t#set pc bounds) (node#getTaggedChildren "wtohead")

let write_xml_arg_bounds (node:xml_element_int) t =
  let pairs = t#listOfPairs in
  node#appendChildren
    (List.map (fun (arg_term,bounds) ->
      let anode = xmlElement "arg_bounds" in
      let arg_node = xmlElement "arg" in
      jtdictionary#write_xml_jterm arg_node arg_term;
      let bounds_node = xmlElement "bounds" in
      write_xml_bounds bounds_node bounds#toList;
      anode#appendChildren [arg_node; bounds_node];
      anode) pairs)

let read_xml_arg_bounds (node:xml_element_int) t =
  List.iter (fun node ->
    let anode = node#getTaggedChild "arg" in
    let arg_term = jtdictionary#read_xml_jterm anode in
    let bounds_node = node#getTaggedChild "bounds" in
    let bounds = JTermCollections.set_of_list (read_xml_bounds bounds_node) in
    t#set arg_term bounds) (node#getTaggedChildren "arg_bounds")

let write_xml_pc_arg_bounds (node:xml_element_int) t =
  let pairs = t#listOfPairs in
  node#appendChildren
    (List.map (fun (pc,argt) ->
         let anode = xmlElement "call" in
         begin
           anode#setIntAttribute "pc" pc;
           write_xml_arg_bounds anode argt;
           anode
         end) pairs)

let read_xml_pc_arg_bounds (node:xml_element_int) t =
  List.iter (fun n ->
      let pc = n#getIntAttribute "pc" in
      let tt = new JTermCollections.table_t in
      begin
        read_xml_arg_bounds n tt;
        t#set pc tt
      end) (node#getTaggedChildren "call")

let write_xml_method_cost_support
      (node:xml_element_int) (cms:class_method_signature_int) =
  let cmsix = cms#index in
  begin
    (match !geq_terms#get cmsix with
     | Some t ->
        let pNode = xmlElement "geq-terms" in
        begin
          write_xml_geq_terms pNode t;
          node#appendChildren [pNode]
        end
     | _ -> ());
    (match !iterations_lbs#get cmsix with
     | Some t ->
        let mNode = xmlElement "its-lbs" in
        begin
          write_xml_iterations mNode t;
          node#appendChildren [mNode]
        end
     | _ -> ());
    (match !iterations_ubs#get cmsix with
     | Some t ->
        let mNode = xmlElement "its-ubs" in
        begin
          write_xml_iterations mNode t;
          node#appendChildren [mNode]
        end
     | _ -> ());
    (match !method_arg_lbounds#get cmsix with
     | Some t ->
        let bNode = xmlElement "arg-lbounds" in
        begin
          write_xml_pc_arg_bounds bNode t;
          node#appendChildren [bNode]
        end
     | _ -> ());
    (match !method_arg_ubounds#get cmsix with
     | Some t ->
        let bNode = xmlElement "arg-ubounds" in
        begin
          write_xml_pc_arg_bounds bNode t;
          node#appendChildren [bNode]
        end
     | _ -> ());
    (try
      let set = H.find !unreachable_vars cmsix in
      let unode = xmlElement "unreachable_vars" in
      write_xml_unreachable_vars unode set;
      node#appendChildren [unode]
    with _ -> ());
    (try
      let local_var_maps = H.find !local_var_maps cmsix in
      let lnode = xmlElement "local_var_maps" in
      write_xml_local_var_maps lnode local_var_maps;
      node#appendChildren [lnode]
    with _ -> ());
    node#setIntAttribute "cmsix" cmsix
  end

let read_xml_method_cost_support  (node:xml_element_int) =
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let cmsix = node#getIntAttribute "cmsix" in
  begin
    (if hasc "geq-terms" then
      let t = new IntCollections.table_t in
      begin
        read_xml_geq_terms (getc "geq-terms") t;
        !geq_terms#set cmsix t
      end);
    (if hasc "its-lbs" then
      let t = new IntCollections.table_t in
      begin
	read_xml_iterations (getc "its-lbs") t;
	!iterations_lbs#set cmsix t
      end);
    (if hasc "its-ubs" then
       let t = new IntCollections.table_t in
       begin
         read_xml_iterations (getc "its-ubs") t;
         !iterations_ubs#set cmsix t
       end);
    (if hasc "arg-lbounds" then
      let t = new IntCollections.table_t in
      begin
	read_xml_pc_arg_bounds (getc "arg-lbounds") t;
	!method_arg_lbounds#set cmsix t
      end);
    (if hasc "arg-ubounds" then
      let t = new IntCollections.table_t in
      begin
        read_xml_pc_arg_bounds (getc "arg-ubounds") t;
        !method_arg_ubounds#set cmsix t
      end);
    (if hasc "unreachable_vars" then (* taint support *)
      begin
	let unreach = read_xml_unreachable_vars (getc "unreachable_vars") in
	if not unreach#isEmpty then H.replace !unreachable_vars cmsix unreach
      end);
    (if hasc "local_var_maps" then (* taint support *)
      begin
	let lvar_maps = read_xml_local_var_maps (getc "local_var_maps") in
	if lvar_maps#size != 0 then H.replace !local_var_maps cmsix lvar_maps
      end)
  end

let bound_to_string b =
  match b#getBound with
  | MINUS_INF -> "-oo"
  | PLUS_INF -> "+oo"
  | NUMBER x -> x#toString

let bound_from_string str =
  if str = "-oo" then
    minus_inf_bound
  else if str = "+oo" then
    plus_inf_bound
  else
    bound_of_num (mkNumericalFromString str)

let _write_xml_interval (node:xml_element_int) int =
  begin
    node#setAttribute "min" (bound_to_string int#getMin);
    node#setAttribute "max" (bound_to_string int#getMax)
  end

let read_xml_interval (node: xml_element_int) =
  let min = bound_from_string (node#getAttribute "min") in
  let max = bound_from_string (node#getAttribute "max") in
  new interval_t min max

let write_xml_field_int_table (node: xml_element_int) table =
  node#appendChildren
    (List.map (fun (field, _int) ->
      let fnode = xmlElement "field" in
      jtdictionary#write_xml_jterm fnode field;
      let intNode = xmlElement "interval" in
      fnode#appendChildren [intNode];
      fnode) table#listOfPairs)

let read_xml_field_int_table (node:xml_element_int) =
  let table = new JTermCollections.table_t in
  let add_node nd =
    let jterm = jtdictionary#read_xml_jterm (nd#getTaggedChild "field") in
    let int = read_xml_interval (nd#getTaggedChild "interval") in
    table#set jterm int in
  begin
    List.iter add_node (node#getTaggedChildren "field");
    table
  end

let write_xml_class_cost_support (node:xml_element_int) (cInfo:class_info_int) =
  let mmNode = xmlElement "methods" in
  node#setIntAttribute "cnix" cInfo#get_index;
  let cn = cInfo#get_class_name in
  begin
    mmNode#appendChildren
      (List.map (fun ms ->
        let cms = make_cms cn ms in
        let mNode = xmlElement "method" in
        begin write_xml_method_cost_support mNode cms; mNode end)
         cInfo#get_methods_defined);
    node#appendChildren [mmNode]
  end;
  (match !pos_fields#get cInfo#get_index with
  | Some table ->
      let pos_fields_node = xmlElement "pos_fields" in
      write_xml_field_int_table pos_fields_node table
  | _ -> ())

let read_xml_class_cost_support (node:xml_element_int) =
  let name = node#getAttribute "name" in
  let package = node#getAttribute "package" in
  let cnix = node#getIntAttribute "cnix" in
  try
    List.iter read_xml_method_cost_support
      ((node#getTaggedChild "methods")#getTaggedChildren "method");
    (if node#hasOneTaggedChild "pos_fields" then
      let table = read_xml_field_int_table node in
      !pos_fields#set cnix table)
  with
  | XmlDocumentError (line,col,p)
    | XmlParseError (line,col,p) ->
     raise
       (JCH_failure (
            LBLOCK [STR "Xml error in "; STR package; STR ".";
                     STR name; STR ": (";
                     INT line; STR ","; INT col; STR "): "; p]))


let save_xml_class_cost_support (cInfo:class_info_int) =
  if cInfo#is_stubbed || cInfo#is_missing then () else
    let cn = cInfo#get_class_name in
    let node = xmlElement "class" in
    begin
      write_xml_class_cost_support node cInfo;
      node#setAttribute "name" cn#simple_name;
      node#setAttribute "package" cn#package_name;
      save_xml_cost_support_data cn node "class";
    end


let load_xml_class_cost_support () =
  List.iter read_xml_class_cost_support (load_xml_cost_support_files ())

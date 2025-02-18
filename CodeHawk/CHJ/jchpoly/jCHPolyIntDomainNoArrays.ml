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
open CHIntervals
open CHLanguage
open CHNonRelationalDomainValues
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
open JCHBytecodeLocation
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

(* jchpoly *)
open JCHPolyIntervalArray

(* Suppress warnings on unused variables *)
[@@@warning "-27"]


exception JCH_no_return_proc of pretty_t

let dbg = ref false
let params = JCHAnalysisUtils.numeric_params

(* A way to get the private variables of poly_doamin_no_arrays_t *)
let st_poly_int_array_opt = ref None
let set_st_poly_int_array poly_int_array =
  st_poly_int_array_opt := Some poly_int_array
let get_st_poly_int_array () = Option.get !st_poly_int_array_opt

let st_bool_opt = ref None
let _set_st_bool b = st_bool_opt := Some b
let _get_st_bool () = Option.get !st_bool_opt

let st_local_var_map = ref None
let set_st_local_var_map local_var_map = st_local_var_map := Some local_var_map
let get_st_local_var_map () = Option.get !st_local_var_map

let st_local_var_invariants = ref None
let _set_st_local_var_invariants local_var_invariants =
  st_local_var_invariants:= Some local_var_invariants
let _get_st_local_var_invariants () = Option.get !st_local_var_invariants

let st_relational_exprs = ref None
let set_st_relational_exprs exprs = st_relational_exprs:= Some exprs
let get_st_relational_exprs () = Option.get !st_relational_exprs

let st_poly_vars = ref None
let set_st_poly_vars vars = st_poly_vars:= Some vars
let get_st_poly_vars () = Option.get !st_poly_vars

let instr_pc = ref (-1)
let set_instr_pc i = instr_pc := i

let prev_pc_to_wto_pc = ref []
let set_prev_pc_to_wto_pc ls = prev_pc_to_wto_pc := ls
let get_wto_pc prev_pc =
  let rec find_wto_pc p =
    try
      List.assoc p !prev_pc_to_wto_pc
    with _ ->
      find_wto_pc (p + 1) in
  find_wto_pc prev_pc

let old_pc_to_join_poly_int_array = ref (new IntCollections.table_t)

let get_old_join_poly_int_array prev_pc var_to_const poly_vars =
  let pc = try List.assoc prev_pc !prev_pc_to_wto_pc with _ -> prev_pc in
  match !old_pc_to_join_poly_int_array#get pc with
  | Some set -> set
  | _ -> top_poly_interval_array var_to_const poly_vars

let pc_to_join_poly_int_array = ref (new IntCollections.table_t)

let set_join_poly_int_array prev_pc poly_int_array =
  let pc = try List.assoc prev_pc !prev_pc_to_wto_pc with _ -> prev_pc in
  !pc_to_join_poly_int_array#set pc poly_int_array

let old_pc_to_widening_poly_int_array = ref (new IntCollections.table_t)

let get_old_widening_poly_int_array prev_pc var_to_const poly_vars =
  if !dbg then
    pr__debug [STR "get_old_widening_poly_int_array ";
               INT prev_pc; NL; pp_assoc_list_ints !prev_pc_to_wto_pc; NL];

  let pc = get_wto_pc prev_pc in
  match !old_pc_to_widening_poly_int_array#get pc with
  | Some pia -> pia
  | _ -> top_poly_interval_array var_to_const poly_vars

let pc_to_widening_poly_int_array = ref (new IntCollections.table_t)

let set_widening_poly_int_array prev_pc poly_int_array =
  let pc = get_wto_pc prev_pc in
  !pc_to_widening_poly_int_array#set pc poly_int_array

let set_invs wto_pc_to_poly_int_array =
  let add_wto wto_pc poly_int_array =
    !old_pc_to_join_poly_int_array#set wto_pc poly_int_array;
    !old_pc_to_widening_poly_int_array#set wto_pc poly_int_array in
  wto_pc_to_poly_int_array#iter add_wto


let pc_to_join_iteration = ref (new IntCollections.table_t)

let increment_join_iteration () =
  match !pc_to_join_iteration#get !instr_pc with
  | Some n -> !pc_to_join_iteration#set !instr_pc (n#add numerical_one)
  | _ -> !pc_to_join_iteration#set !instr_pc numerical_one

let pc_to_widening_iteration = ref (new IntCollections.table_t)
let get_widening_iteration () =
  match !pc_to_widening_iteration#get !instr_pc with
  | Some n -> n#toInt
  | _ -> 0
let increment_widening_iteration () =
  match !pc_to_widening_iteration#get !instr_pc with
  | Some n -> !pc_to_widening_iteration#set !instr_pc (n#add numerical_one)
  | _ -> !pc_to_widening_iteration#set !instr_pc numerical_one

(* These are both numeric and symbolic *)
let reachables = ref (new VariableCollections.set_t)
let is_reachable var = !reachables#has var

(* Symbolic params that might have been changed *)
let changed_sym_params = ref (new VariableCollections.set_t)
let get_changed_sym_params () = !changed_sym_params#toList

let overflow = ref (new VariableCollections.set_t)
let underflow = ref (new VariableCollections.set_t)
let convert_overflow = ref (new VariableCollections.set_t) (* dst of conversion *)

(* The result of a division with a possible 0 divisor *)
let div0 = ref (new VariableCollections.set_t)

let add_overflow var = !overflow#add var
let add_underflow var = !underflow#add var
let add_convert_overflow dst = !convert_overflow#add dst
let add_reachable var = !reachables#add var
let add_div0 var = !div0#add var

let in_bounds_vars = ref (new VariableCollections.set_t)
let out_of_bounds_vars = ref (new VariableCollections.set_t)
let no_info_bounds_vars = ref (new VariableCollections.set_t)


let record_array_access
      (_poly_int_array: JCHPolyIntervalArray.poly_interval_array_t)
      _array
      _index = ()

(* Used to project out variables that are not needed in very long states,
 * such as in clinit that set arrays *)
let pc_to_last_read = ref (new IntCollections.table_t)

(* Used to report truncations in casts of results of operations as over/underflow *)
let arith_casts = ref (new IntCollections.set_t)

module FieldInfoCollections = CHCollections.Make (
  struct
    type t = field_info_int
    let compare f1 f2 = compare f1#get_index f2#get_index
    let toPretty f = f#toPretty
  end)

(* Array and collection variables that were obtained as OpGetField
 * They are needed to check if OpArrayStore or invoked methods do not change them *)
let variable_to_fields = ref (new VariableCollections.table_t)
let add_variable_to_field var iInfo =
  let fInfo = iInfo#get_field_target in
  match !variable_to_fields#get var with
  | Some set -> set#add fInfo
  | None ->
     !variable_to_fields#set var (FieldInfoCollections.set_of_list [fInfo])

let reset_ref_vars
      proc_name jproc_info consts reset_old_join_widening =
  begin
    overflow := new VariableCollections.set_t;
    underflow := new VariableCollections.set_t;
    convert_overflow := new VariableCollections.set_t;
    reachables := VariableCollections.set_of_list consts;
    changed_sym_params := new VariableCollections.set_t;
    div0 := new VariableCollections.set_t;
    variable_to_fields := new VariableCollections.table_t;
    instr_pc := (-1);

    old_pc_to_widening_poly_int_array :=
      if reset_old_join_widening then
        new IntCollections.table_t
      else
        !pc_to_widening_poly_int_array;
    pc_to_widening_poly_int_array := new IntCollections.table_t;

    pc_to_widening_iteration := new IntCollections.table_t;
    old_pc_to_join_poly_int_array :=
      if reset_old_join_widening then
        new IntCollections.table_t
      else
        !pc_to_join_poly_int_array;
    pc_to_join_poly_int_array:= new IntCollections.table_t;

    let (table, set, div2div2quot) =
      JCHCollectors.collect_lin_eqs_info proc_name jproc_info in
    pc_to_last_read := table;
    arith_casts := set;
    div2div2quot
  end

let get_proc_info () =
  let res =
    (!in_bounds_vars,
     !out_of_bounds_vars,
     !no_info_bounds_vars,
     !overflow,
     !underflow,
     !convert_overflow,
     !reachables,
     !div0) in
  begin
    in_bounds_vars := new VariableCollections.set_t;
    out_of_bounds_vars := new VariableCollections.set_t;
    no_info_bounds_vars := new VariableCollections.set_t;
    res
  end

let lost_info_table = new SymbolCollections.table_t

let log_lost_info proc_name v local_var_map =
  let v_table =
    match lost_info_table#get proc_name with
    | Some t -> t
    | None ->
       let t = new VariableCollections.table_t in
       begin
	 lost_info_table#set proc_name t;
	 t
       end in
  try
    let (local_v, _) = List.find (fun (_, u) -> u#equal v) local_var_map in
    let t = new IntCollections.table_t in
    begin
      t#set !instr_pc local_v;
      v_table#set v t
    end
  with _ ->
    v_table#set v (new IntCollections.table_t)


let unlog_lost_info proc_name v =
  let v_table =
    match lost_info_table#get proc_name with
    | Some t -> t
    | None ->
       let t = new VariableCollections.table_t in
       begin
	 lost_info_table#set proc_name t;
	 t
       end in
  v_table#remove v

let has_lost_info proc_name vs =
  let v_table =
    match lost_info_table#get proc_name with
    | Some t -> t
    | None ->
       let t = new VariableCollections.table_t in
       begin
	 lost_info_table#set proc_name t;
	 t
       end in
  List.exists v_table#has vs

let transfer_lost_info proc_name x y local_var_map =
  if has_lost_info proc_name [x] then
    begin
      if not (JCHSystemUtils.is_constant y) then
	log_lost_info proc_name y local_var_map
    end
  else if has_lost_info proc_name [y] then
    if not (JCHSystemUtils.is_constant x) then
      log_lost_info proc_name x local_var_map


let print_lost_info () =
  let table = new SymbolCollections.table_t in
  let add_proc ((proc_name, v_table):
                  symbol_t
                  * variable_t IntCollections.table_t VariableCollections.table_t) =
    if not (v_table#size = 0) then
      begin
	let new_t = new VariableCollections.table_t in
	table#set proc_name new_t;
	let add_var (_v, pc_table)  =
	  let add_local_v (pc, local_v) =
	    match new_t#get local_v with
	    | Some set -> set#add pc
	    | _ ->
		new_t#set local_v (IntCollections.set_of_list [pc]) in
	  List.iter add_local_v pc_table#listOfPairs in
	List.iter add_var v_table#listOfPairs
      end in
  List.iter add_proc lost_info_table#listOfPairs;

  if !dbg then
    pr__debug [STR "lost_info: "; NL; lost_info_table#toPretty; NL];

  pr__debug [STR "lost_info: "; NL; table#toPretty; NL]

(* A poly domain in which the constants are kept separately
 * The variables are added and removed as needed
 * The order of the variables is kept otherwise constant *)
class poly_int_domain_no_arrays_t
        (jproc_info:JCHProcInfo.jproc_info_t)
        (p_int_a:poly_interval_array_t)
        ((orig_local_vs, local_v_map): variable_t list * (variable_t * variable_t) list) =
object (self: 'a)

  inherit ['a] CHCommunications.domain_downlink_t

    val proc_name = jproc_info#get_name
    val cms = retrieve_cms jproc_info#get_name#getSeqNumber
    val mInfo = app#get_method (retrieve_cms jproc_info#get_name#getSeqNumber)

    val poly_int_array = p_int_a

    val orig_local_vars = orig_local_vs
    val phi_infos =
      List.filter (fun info -> info#is_phi) (jproc_info#get_jvar_infos#listOfValues)

    (* original variable -> version variable at current pc *)
    val local_var_map = local_v_map

    method mkBottom =
      {< poly_int_array = bottom_poly_interval_array >}

    method isBottom = poly_int_array#is_bottom

    method mkEmpty =
      {< poly_int_array =
           poly_int_array#mk_empty (self#get_var_to_const) (self#get_poly_vars) >}

    method clone =
      {< poly_int_array = poly_int_array#clone >}

    method isRelational = true

    method private reached_time_limit =
      match params#check_time_limit with
      |	0 -> false
      |	1 ->
         begin
	   pr__debug [STR " Reached constraint analysis time limit "; NL];
	   params#reset_analysis_failure_status;
	   true
         end
      |	_ ->
         begin
	   pr__debug [STR "Analysis failed: reached numeric analysis time limit "; NL];
	   raise (params#analysis_failed 3 "reached numeric analysis time limit ")
         end

    method observer =
      object
	inherit CHDomainObserver.domain_observer_t
	method !getObservedVariables: variable_t list = poly_int_array#get_poly_vars
	method !getMatrix = None
	method !isTop = Some poly_int_array#is_top
	method !isBottom = Some poly_int_array#is_bottom
      end

    method private get_poly_int_array (a: 'a) =
      let _ = a#special "set_poly_int_array" [] in
      get_st_poly_int_array ()

    method private get_local_var_map (a: 'a) =
      let _ = a#special "set_local_var_map" [] in
      get_st_local_var_map ()

    method private change_local_var_map (a: 'a) v w =
      try (* For the case when v or w are not local variables *)
	let alocal_var_map:(variable_t * variable_t) list =
          self#get_local_var_map a in
	let get_var_index var =
          int_of_string (Str.string_after var#getName#getBaseName 1) in
	let v_index = get_var_index v in
	let alocal_v_map =
	  match List.partition
                  (fun (v1, v2) ->
                    v2#equal w && get_var_index v1 = v_index) alocal_var_map with
	  | ((orig_w, _) :: _, rest_local_var_map) ->
	      (orig_w, v) :: rest_local_var_map
	  | _ -> alocal_var_map in
	{< poly_int_array = self#get_poly_int_array a;
	  local_var_map = alocal_v_map >}
	with _ -> a

    method private get_var_to_const = poly_int_array#get_var_to_const

    method private is_const v = poly_int_array#is_const v

    method private get_const_val v = poly_int_array#get_const_val v

    method private get_const_val_n v = poly_int_array#get_const_val_n v

    method private get_poly_vars = poly_int_array#get_poly_vars

    method leq ?(variables: variable_t list option) (a: 'a) =
      let res =
	match (self#isBottom, a#isBottom) with
	| (true, _) -> true
	| (_, true) -> false
	| _ ->
	   if not params#use_types && get_widening_iteration () < 2 then
             false
	    else
	      begin
		let s_poly_int_array = poly_int_array#move_simple_ineqs in
		let a_poly_int_array =
                  (self#get_poly_int_array a)#move_simple_ineqs in
		s_poly_int_array#leq a_poly_int_array
	      end in
      res

    method equal (a: 'a) =
      poly_int_array#equal (self#get_poly_int_array a)

    method meet ?(variables: variable_t list option) (a: 'a) =
      match (self#isBottom, a#isBottom) with
      |	(false, false) ->
         {< poly_int_array =
              poly_int_array#meet false (self#get_poly_int_array a) >}
      |	_ -> self#mkBottom

    method private join_local_var_map (a: 'a) =
      let alocal_var_map = self#get_local_var_map a in
      let join_vars var_index v1 v2 =
	try
	  let is_this_phi (phi_info: JCHVarInfo.jvar_info_t) =
	    let rvars = phi_info#get_read_vars in
	    if (List.hd phi_info#get_local_indices) = var_index then
	      (List.exists (fun v ->
                   v#equal v1) rvars) && (List.exists (fun v -> v#equal v2) rvars)
	    else false in
	  Some (List.find is_this_phi phi_infos)#get_variable
	with _ ->
	  begin
	    let is_v_phi var1 var2 =
	      let var1_info = jproc_info#get_jvar_info var1 in
	      let rvars = var1_info#get_read_vars in
	      var1_info#is_phi && List.exists (fun v -> v#equal var2) rvars in
	    if is_v_phi v1 v2 then Some v1
	    else if is_v_phi v2 v1 then Some v2
	    else None
	  end in
      let join_local_var_map = ref [] in
      let add_var orig_var =
	match (List.filter (fun (ov, _) -> ov#equal orig_var) local_var_map,
	       List.filter (fun (ov, _) -> ov#equal orig_var) alocal_var_map) with
	| ((_, v1) :: _, (_, v2) :: _) ->
	    if v1#equal v2 then join_local_var_map := (orig_var, v1) :: !join_local_var_map
	    else
	      begin
		let var_index =
                  int_of_string (Str.string_after orig_var#getName#getBaseName 1) in
		match join_vars var_index v1 v2 with
		| Some v -> join_local_var_map := (orig_var, v) :: !join_local_var_map
		| _ -> ()
	      end
	| ((_, v) :: _, _)
	| (_, (_, v) :: _) -> join_local_var_map := (orig_var, v) :: !join_local_var_map
	| _ -> () in
      List.iter add_var orig_local_vars;
      !join_local_var_map


    method join ?(variables: variable_t list option) (a: 'a) =
      let _ =
        if !dbg then
          pr__debug [STR "JCHPIDA.join ";  INT (!instr_pc); STR " ";
                     INT (get_widening_iteration ()); NL;
		     self#toPretty; NL; a#toPretty; NL] in

      let join_res =
	match (self#isBottom, a#isBottom) with
	| (true, _) -> a#clone
	| (_, true) -> {< >}
	| _ ->
	    increment_join_iteration();
	    let s_poly_int_array =
	      let pia =
		if params#use_loop_counters then
                  self
		else
                  self#project_out_loop_counters self in
	      let pia =
		if params#use_lengths then
                  pia
		else
                  self#project_out_lengths pia in
	      (self#get_poly_int_array pia)#move_simple_ineqs in
	    let a_poly_int_array =
	      let pia =
		if params#use_loop_counters then
                  a
		else
                  self#project_out_loop_counters a in
	      let pia =
		if params#use_lengths then
                  pia
		else
                  self#project_out_lengths pia in
	      (self#get_poly_int_array pia)#move_simple_ineqs in
	    if self#reached_time_limit then
	      begin
		let s_poly_int_array' = s_poly_int_array#drop_poly in
		let a_poly_int_array' = a_poly_int_array#drop_poly  in
		params#set_use_intervals true;
		{< poly_int_array = s_poly_int_array'#join a_poly_int_array';
		  local_var_map = self#join_local_var_map a >}
	      end
	    else
	      begin
		let old_poly_int_array =
                  get_old_join_poly_int_array
                    !instr_pc self#get_var_to_const self#get_poly_vars in
		let jpoly_int_array =
                  s_poly_int_array#join_with_old a_poly_int_array old_poly_int_array in
		set_join_poly_int_array !instr_pc jpoly_int_array;
		let join_var_map = self#join_local_var_map a in
		{< poly_int_array = jpoly_int_array;
		  local_var_map = join_var_map >}
	      end;

      in let _ =
           if !dbg then
             pr__debug [STR "join res = "; NL; join_res#toPretty; NL] in
      join_res

    method widening ?(kind: string option) ?(variables: variable_t list option) (a: 'a) : 'a =
      try
	self#widening_ self a
      with
      |	JCHAnalysisUtils.JCH_num_analysis_failure _ ->
	if params#get_analysis_status = 1 then
	  begin
	    params#reset_analysis_failure_status;
	    self#widening_
              {< poly_int_array = poly_int_array#drop_poly >}
              {< poly_int_array = (self#get_poly_int_array a)#drop_poly >}
	  end
	else
	  raise
            (params#analysis_failed
               (params#get_analysis_status) (params#get_analysis_failure_reason))
      |	_ ->
         begin
	   pr__debug [STR "Analysis failed: unknown programming error in widening"; NL];
	   raise (params#analysis_failed 3 "unknown programming error in widening")
         end

    method private widening_ (s: 'a) (a: 'a) =
      let _ =
        if !dbg then
          pr__debug [STR "widening_ "; INT (!instr_pc); STR " ";
                     INT (get_widening_iteration ()); NL;
		     s#toPretty; NL; a#toPretty; NL] in
      let res : 'a =
	match (s#isBottom, a#isBottom) with
	| (true, _) -> a#clone
	| (_, true) -> {< >}
	| _ ->
	    let s_poly_int_array = self#get_poly_int_array s in
	    let a_poly_int_array = self#get_poly_int_array a in
	    let old_poly_int_array =
              get_old_widening_poly_int_array
                !instr_pc self#get_var_to_const self#get_poly_vars in
	    JCHPolyIntervalArray.set_local_vars (List.map snd local_var_map);

	    let new_poly_int_array =
	      if self#reached_time_limit then
		begin
		  if !dbg then pr__debug [STR "reached limit"; NL];

		  params#set_use_intervals true;
		  let old_poly_int_array = old_poly_int_array#drop_poly in
		  let s_poly_int_array = s_poly_int_array#drop_poly in
		  let a_poly_int_array = a_poly_int_array#drop_poly in
		  let w_poly_int_array = s_poly_int_array#widening a_poly_int_array in
		  w_poly_int_array#meet false old_poly_int_array
		end
	      else
		begin
		  let s_poly_int_array =
                    poly_int_array#move_simple_ineqs#meet true old_poly_int_array in
		  let a_poly_int_array =
                    a_poly_int_array#move_simple_ineqs#meet true old_poly_int_array in
		  let w_poly_int_array = s_poly_int_array#widening a_poly_int_array in
		  w_poly_int_array#meet false old_poly_int_array;
		end in
	    set_widening_poly_int_array !instr_pc new_poly_int_array;
	    increment_widening_iteration ();
	    {< poly_int_array = new_poly_int_array >} in
      let _ =
        if !dbg then
          pr__debug [STR "widening_ res: "; NL; res#toPretty; NL] in
      res

    method narrowing ?(variables: variable_t list option) (a: 'a) =
      if self#isBottom then
        self#mkBottom
      else {< >}

    method private record_changed_sym_params vars : unit =
      let is_sym_param v =
	let jvar_info = jproc_info#get_jvar_info v in
	jvar_info#is_parameter && not v#isNumerical in
      let changed_params = List.filter is_sym_param vars in
      !changed_sym_params#addList changed_params

    method private copy_num_info (a: 'a) dst_var src_var =
      let apoly_int_array = self#get_poly_int_array a in
       {< poly_int_array = apoly_int_array#copy_num_info dst_var src_var >}

    method special (cmd: string) (args: domain_cmd_arg_t list) : 'a =
      match cmd with
      |	"set_poly_int_array" ->
         begin
	   set_st_poly_int_array poly_int_array;
	   {< >}
         end
      |	"set_local_var_map" ->
         begin
	   set_st_local_var_map local_var_map;
	   {< >}
         end
      |	"restrict_to_vars" ->
	  let add_var vs arg =
	    match arg with VAR_DOM_ARG v -> v :: vs | _ -> vs in
	  let restr_vars = List.fold_left add_var [] args in
	  {< poly_int_array =
               poly_int_array#restrict_to_vars jproc_info (List.rev restr_vars) >}
      |	"get_vars_fields_rel_exprs" ->
	  let add_var vs arg =
	    match arg with VAR_DOM_ARG v -> v :: vs | _ -> vs in
	  let restr_vars =
            VariableCollections.set_of_list (List.fold_left add_var [] args) in
	  let vars_with_fields = poly_int_array#get_vars_with_fields jproc_info in
	  set_st_poly_int_array poly_int_array;
	  restr_vars#addList vars_with_fields;
	  let restr_poly_int_array =
            poly_int_array#restrict_to_vars jproc_info restr_vars#toList in

	  if !dbg then
            pr__debug [STR "get_vars_fields_rel_expres "; NL;
                       restr_poly_int_array#toPretty; NL];

	  let restr_local_var_map =
            List.filter (fun (v1, v2) -> v1#equal v2) local_var_map in
	  let postconds =
            restr_poly_int_array#to_postconditions
              true jproc_info restr_local_var_map vars_with_fields in

	  if !dbg then
            pr__debug [STR "postconds ";
                       pretty_print_list
                         postconds
                         JCHNumericUtils.postcondition_predicate_to_pretty
                         "{" "; " "}"; NL];

	  let rel_exprs =
            List.map JCHNumericUtils.post_predicate_to_relational_expr postconds in
	  set_st_relational_exprs rel_exprs;
	  {< >}

      |	"get_local_var_invariants" ->
	  let include_loop_counters = List.length args > 0 in
	  let postconds =
            poly_int_array#to_postconditions
              include_loop_counters jproc_info local_var_map [] in
	  let rel_exprs =
            List.map JCHNumericUtils.post_predicate_to_relational_expr postconds in
          begin
	    set_st_relational_exprs rel_exprs;
	    {< >}
          end
      |	"set_poly_vars" ->
         begin
	   set_st_poly_vars poly_int_array#get_poly_vars;
	   {< >}
         end
      |	"project_out_loop_counters" ->
	 let restr_poly_int_array =
           self#get_poly_int_array (self#project_out_loop_counters self) in
	  {< poly_int_array = restr_poly_int_array#remove_duplicates >}
      |	"remove_duplicates" ->
	  {< poly_int_array = poly_int_array#remove_duplicates >}
      |	"drop_poly" ->
	  {< poly_int_array = poly_int_array#drop_poly >}
      | _ ->
         begin
	   pr__debug [ STR "Analysis faied: programming error: ";
                       STR "poly domain - unrecognized command"; NL];
	   raise
             (params#analysis_failed
                3 "programming error: poly domain - unrecognized command")
         end

    method private project_out (vs:variable_t list) =
      self#record_changed_sym_params vs;
      {< poly_int_array = poly_int_array#project_out vs >}

    method projectOut (vs:variable_t list) =
      if self#isBottom then
        {< >}
      else
	begin
	  List.iter add_reachable vs;

	  let poly_vars = poly_int_array#get_poly_vars in
	  let num_vs = List.filter (fun v -> List.mem v poly_vars) vs in
	  if num_vs = [] then
	    begin
	      self#record_changed_sym_params vs;
	      {< >}
	    end
	  else
            self#project_out num_vs
	end

    method private remove (vs: variable_t list) =
      if self#isBottom then
        {< >}
      else
	begin
	  let poly_vars = poly_int_array#get_poly_vars in
	  let num_vs = List.filter (fun v -> List.mem v poly_vars) vs in
	  if num_vs = [] then
            {< >}
	  else
	    begin
	      let new_poly_int_array = poly_int_array#project_out num_vs in
	      {< poly_int_array = new_poly_int_array#remove num_vs >}
	    end
	end

    method private is_float v =
      let info = jproc_info#get_jvar_info v in
      JCHTypeUtils.can_be_float info#get_types

   (* We do not record division by 0 for Float or Double because it does not
    * result in an arithmetic exception.
    * It produces and infinite number or NaN *)
    method private record_div0 div0_opt =
      if params#use_types then
	match div0_opt with
	| Some v -> if not (self#is_float v) then add_div0 v
	| _ ->
           if !dbg then
             pr__debug [proc_name#toPretty; STR " record_div0 not possible "; NL];

    method private record_overflow overflow_opt =
      if params#use_types then
	match overflow_opt with
	| Some v ->
	   if not (JCHSystemUtils.is_loop_counter v) then
             add_overflow v
	   else
             pr__debug [STR "loop_counter has overflow"]
	| _ -> ()

    method private record_underflow underflow_opt =
      if params#use_types then
	match underflow_opt with
	| Some v -> add_underflow v
	| _ -> ()

    method private record_down_cast_overflow pc_opt overflow_opt =
      if params#use_types then
	match (pc_opt, overflow_opt) with
	| (Some _pc, Some v) -> add_overflow v;
	| (None, Some v) -> add_convert_overflow v;
	| _ -> ()

    method private record_down_cast_underflow pc_opt underflow_opt =
      if params#use_types then
	match (pc_opt, underflow_opt) with
	| (Some _pc, Some v) -> add_underflow v;
	| (None, Some v) -> add_convert_overflow v;
	 | _ -> ()

    method private affine_image report equality vpair pairs const =
      let v = fst vpair in
      add_reachable v;

      let (new_poly_int_array, overflow_opt, underflow_opt) =
	poly_int_array#affine_image equality vpair pairs const in
      if report then
	begin
	  self#record_overflow overflow_opt;
	  self#record_underflow underflow_opt
	end;
      (if has_lost_info proc_name (List.map fst pairs) then
        log_lost_info proc_name v local_var_map);
      {< poly_int_array = new_poly_int_array >}

    (* v and w are different *)
    method private affine_subst report v w_opt coeff const =
      add_reachable v;

      let (new_poly_int_array, overflow_opt, underflow_opt) =
	poly_int_array#affine_subst v w_opt coeff const in
      if report then
	begin
	  self#record_overflow overflow_opt;
	  self#record_underflow underflow_opt
	end;
      (match w_opt with
       | Some w ->
          if has_lost_info proc_name [w] then
            log_lost_info proc_name v local_var_map
       | _ -> ());
      {< poly_int_array = new_poly_int_array >}

    (* v = v + const *)
    method private affine_increment report v const =
      add_reachable v;

      let (new_poly_int_array, overflow_opt, underflow_opt) =
	poly_int_array#affine_increment v const in
      (if report then
	 begin
	   self#record_overflow overflow_opt;
	   self#record_underflow underflow_opt
	 end);
      {< poly_int_array = new_poly_int_array >}

    method private affine_image_down_cast
                     pc_opt equality vpair pairs const _src _dst dst_interval_opt =
      let v = fst vpair in
      add_reachable v;

      let (new_poly_int_array, overflow_opt, underflow_opt) =
	poly_int_array#affine_image equality vpair pairs const in
      (if has_lost_info proc_name (List.map fst pairs) then
         log_lost_info proc_name v local_var_map);
      if Option.is_some overflow_opt || Option.is_some underflow_opt then
	begin
	  self#record_down_cast_overflow pc_opt overflow_opt;
	  self#record_down_cast_underflow pc_opt underflow_opt;
	  {< poly_int_array = new_poly_int_array >}
	end
      else
	begin
	  match dst_interval_opt with
	  | Some dst_interval ->
	      begin
		let var = fst vpair in
		let interval = new_poly_int_array#get_interval var in
		if not (interval#leq dst_interval) then
		  begin
		    let new_poly_int_array =
                      new_poly_int_array#project_out [var] in
		    (if interval#getMax#gt dst_interval#getMax then
                       self#record_down_cast_overflow pc_opt (Some var));
		    (if interval#getMin#lt dst_interval#getMin then
                       self#record_down_cast_underflow pc_opt (Some var));
		    {< poly_int_array = new_poly_int_array >}
		  end
		else
                  {< poly_int_array = new_poly_int_array >}
	      end
	  |  _ -> {< poly_int_array = new_poly_int_array >}
	end

    method private down_cast_float src dst =
      add_reachable dst;

      let (new_poly_int_array, is_overflow) =
        poly_int_array#down_cast_float src dst in
      (if is_overflow then add_convert_overflow dst);
      {< poly_int_array = new_poly_int_array >}

    method private affine_preimage vpair pairs const =
      {< poly_int_array = poly_int_array#affine_preimage vpair pairs const >}

    method getNonRelationalValue v =
      let interval = poly_int_array#get_interval v in
      mkIntervalValue interval

    method importNumericalConstraints
             (_csts: CHNumericalConstraints.numerical_constraint_t list) =
      {< >}

    method importNonRelationalValues
             ?(refine = true)
             (pairs:(variable_t * non_relational_domain_value_t) list) =
      {< >}

    val neg_unit_big_int = minus_big_int unit_big_int

    method private mult v x y =
      add_reachable v;

      let (new_poly_int_array, overflow_opt, underflow_opt, lost_info) =
	poly_int_array#mult v x y in
      self#record_overflow overflow_opt;
      self#record_underflow underflow_opt;
      (if lost_info then
	 log_lost_info proc_name v local_var_map
       else
         unlog_lost_info proc_name v);
      {< poly_int_array = new_poly_int_array >}

    method private div v x y =
      add_reachable v;

      let is_float = self#is_float v in
      let (new_poly_int_array, div0_opt, overflow_opt, underflow_opt) =
	poly_int_array#div is_float v x y in
      (if not is_float then
	 begin
	   self#record_div0 div0_opt;
	   self#record_overflow overflow_opt;
	   self#record_underflow underflow_opt;
	 end);
      {< poly_int_array = new_poly_int_array >}

    method private rem v x y =
      add_reachable v;

      let is_float = self#is_float v in
      let (new_poly_int_array, div0_opt) = poly_int_array#rem is_float v x y in
      (if not is_float then self#record_div0 div0_opt);
      {< poly_int_array = new_poly_int_array >}

    method private update_fields new_poly_int_array var =
      (match !variable_to_fields#get var with
      | Some fields ->
	  begin
	    let int = new_poly_int_array#get_interval var in
	    match jproc_info#get_length var with
	    | Some length_var ->
		let length_interval = new_poly_int_array#get_interval length_var in
		fields#iter
                  (fun fi ->
                    JCHFields.int_field_manager#put_field
                      proc_name fi int [length_interval] true var)
	    | _ ->
	       fields#iter
                 (fun fi ->
                   JCHFields.int_field_manager#put_field proc_name fi int [] false var)
	  end
      | None -> () )

    method private project_out_fields var =
      match !variable_to_fields#get var with
      | Some fields -> fields#iter JCHFields.int_field_manager#project_out
      | None -> ()

    method private project_out_loop_counters (a: 'a) : 'a =
      let apoly_int_array = self#get_poly_int_array a in
      let loop_counters =
        List.filter JCHSystemUtils.is_loop_counter apoly_int_array#get_poly_vars in
      a#projectOut loop_counters

    method private project_out_lengths (a: 'a) : 'a =
      let apoly_int_array = self#get_poly_int_array a in
      let lengths =
        List.filter JCHSystemUtils.is_length apoly_int_array#get_poly_vars in
      a#projectOut lengths

    method analyzeBwd (cmd: (code_int, cfg_int) command_t) : 'a =
      if self#isBottom then
	match cmd with
	| ASSERT e ->
	    self#mkEmpty#analyzeFwd (ASSERT (negate_bool_exp e))
	| _ ->
	    self#mkBottom
      else
	match cmd with
	| ABSTRACT_VARS l ->
	    self#projectOut l
	| ASSIGN_NUM (v, NUM _n) ->
	   if self#is_const v then
             self#clone
	   else
             self#projectOut [v]

	| ASSIGN_NUM (v, NUM_VAR w) ->
	   if self#is_const v then
             self#clone
	   else if v#equal w then
             self#clone
	   else if self#is_const w then
             self#projectOut [v]
	   else
             self#affine_preimage
               (v, unit_big_int) [(w, unit_big_int)] zero_big_int

	| ASSIGN_NUM (v, PLUS (x, y)) ->
	    if self#is_const x then
	      if self#is_const y then
                self#projectOut [v]
	      else
		self#affine_preimage
                  (v,unit_big_int) [(y,unit_big_int)] (self#get_const_val x)
	    else
	      if self#is_const y then
		self#affine_preimage
                  (v,unit_big_int) [(x,unit_big_int)] (self#get_const_val y)
	      else
		self#affine_preimage
                  (v,unit_big_int) [(x,unit_big_int); (y,unit_big_int)] zero_big_int

	| ASSIGN_NUM (v, MINUS (x, y)) ->
	    if self#is_const x then
	      if self#is_const y then
                self#projectOut [v]
	      else
		self#affine_preimage
                  (v,unit_big_int) [(y, neg_unit_big_int)] (self#get_const_val x)
	    else
	      if self#is_const y then
		self#affine_preimage
                  (v, unit_big_int) [(x,unit_big_int)] (minus_big_int (self#get_const_val y))
	      else
		self#affine_preimage
                  (v,unit_big_int) [(x,unit_big_int); (y, neg_unit_big_int)] zero_big_int

	| ASSIGN_NUM (v, MULT (x,y)) ->
	    if self#is_const x then
	      if self#is_const y then
                self#projectOut [v]
	      else
		self#affine_preimage
                  (v,unit_big_int) [(y,self#get_const_val x)] zero_big_int
	    else
	      if self#is_const y then
		self#affine_preimage
                  (v,unit_big_int) [(x,self#get_const_val y)] zero_big_int
	      else
                self#projectOut [v]

	| ASSIGN_NUM (v, DIV (_x, _y)) -> self#projectOut [v]
	| INCREMENT (v, n) -> self#analyzeFwd (INCREMENT (v, n#neg))
	| ASSERT TRUE -> self#clone
	| ASSERT FALSE -> self#mkBottom
	| ASSERT _ -> self#analyzeFwd cmd
	| _ -> self#clone

    method analyzeFwd (cmd: (code_int, cfg_int) command_t) : 'a =

      let _ =
        if !dbg then
          pr__debug [STR "PolyDom.analyzeFwd ";
                     command_to_pretty 0 cmd; NL; self#to_pretty; NL] in
      try
	self#analyzeFwd_ cmd
      with
      |	JCHAnalysisUtils.JCH_num_analysis_failure _ ->
	if params#get_analysis_status = 1 then
	  begin
	    params#reset_analysis_failure_status;
	    ({< poly_int_array = poly_int_array#drop_poly >})#analyzeFwd cmd
	  end
	else
	  raise
            (params#analysis_failed
               (params#get_analysis_status) (params#get_analysis_failure_reason))
      |	_ ->
         begin
	   pr__debug [STR "Analysis failed:unknown programming error in analyzeFwd"; NL];
	   raise (params#analysis_failed 3 "unknown programming error in analyzeFwd")
         end

    method private analyzeFwd_ (cmd: (code_int, cfg_int) command_t) : 'a =

      let _ =
        if !dbg then
          pr__debug [STR "PolyDom.analyzeFwd_ "; command_to_pretty 0 cmd; NL;
                     self#to_pretty; NL] in

      let res =
        let default () = {< >} in
        let default_v v =
	  add_reachable v;
	  {< >} in
        if self#reached_time_limit then
	  begin
	    params#set_use_intervals true;
	    let a = {< poly_int_array = poly_int_array#drop_poly >} in
	    a#analyzeFwd cmd
	  end
        else if self#isBottom then
          self#mkBottom
        else
	  match cmd with
	  | ABSTRACT_VARS l ->
	     List.iter add_reachable l;
	     let poly_vars = self#get_poly_vars in
	     let red_l = List.filter (fun v -> List.mem v poly_vars) l in
	     self#projectOut red_l

	  | ASSIGN_NUM (v, NUM n) ->
	     if self#is_const v then
               default_v v
	     else
               self#affine_subst false v None zero_big_int n#getNum

	  | ASSIGN_NUM (v, NUM_VAR w) ->
	     begin
	       let a =
		 if self#is_const v then
                   default_v v
		 else if self#is_const w then
		   self#affine_subst
                     false v None zero_big_int (self#get_const_val w)
		 else
		   self#affine_subst false v (Some w) unit_big_int zero_big_int in
	       let b =
		 if JCHSystemUtils.is_length w then
		   let pia = self#get_poly_int_array a in
		   {< poly_int_array = pia#transfer_fields true w v >}
		 else
                   a in
	       self#change_local_var_map b v w
	     end

	  | ASSIGN_NUM (v, PLUS (x, y)) ->
	     if self#is_const x then
	       if self#is_const y then
		 let n = add_big_int (self#get_const_val x) (self#get_const_val y) in
		 self#affine_subst true v None zero_big_int n
	       else if v#equal y then
		 self#affine_increment true v (self#get_const_val x)
	       else
		 self#affine_subst
                   true v (Some y) unit_big_int (self#get_const_val x)
	     else if self#is_const y then
	       if v#equal x then
		 self#affine_increment true v (self#get_const_val y)
	       else
		 self#affine_subst
                   true
                   v
                   (Some x)
                   unit_big_int
                   (self#get_const_val y)
	     else
	       self#affine_image
                 true
                 None
                 (v, unit_big_int)
                 [(x, unit_big_int); (y, unit_big_int)]
                 zero_big_int

	| ASSIGN_NUM (v, MINUS (x, y)) ->
	    if self#is_const x then
	      if self#is_const y then
		let n =
                  add_big_int
                    (self#get_const_val x) (minus_big_int (self#get_const_val y)) in
		self#affine_subst true v None zero_big_int n
	      else if v#equal y then
		self#affine_image
                  true
                  None
                  (v, unit_big_int)
                  [(y, neg_unit_big_int)]
                  (self#get_const_val x)
	      else
		self#affine_subst
                  true v (Some y) neg_unit_big_int (self#get_const_val x)
	    else if self#is_const y then
	      let n = minus_big_int (self#get_const_val y) in
	      if v#equal x then
		self#affine_increment true v n
	      else
		self#affine_subst true v (Some x) unit_big_int n
	    else
	      self#affine_image
                true
                None
                (v, unit_big_int)
                [(x, unit_big_int); (y, neg_unit_big_int)]
                zero_big_int

	| ASSIGN_NUM (v, MULT (x, y)) ->
	    if self#is_const x then
	      if self#is_const y then
		let n = mult_big_int (self#get_const_val x) (self#get_const_val y) in
		self#affine_subst true v None zero_big_int n
	      else if v#equal y then
		self#affine_image
                  true
                  None
                  (v, unit_big_int)
                  [(y, self#get_const_val x)]
                  zero_big_int
	      else
		self#affine_subst
                  true v (Some y) (self#get_const_val x) zero_big_int
	    else if self#is_const y then
	      if v#equal x then
		self#affine_image
                  true
                  None
                  (v, unit_big_int)
                  [(x, self#get_const_val y)]
                  zero_big_int
	      else
		self#affine_subst true v (Some x) (self#get_const_val y) zero_big_int
	    else self#mult v x y

	| ASSIGN_NUM (v, DIV (x, y)) -> self#div v x y
	| INCREMENT (v, n) -> self#affine_increment true v n#getNum
	| ASSERT TRUE -> default ()
	| ASSERT FALSE -> self#mkBottom

	| ASSERT (EQ (x, y)) ->
	   if JCHAnalysisUtils.is_numeric
                jproc_info x && JCHAnalysisUtils.is_numeric jproc_info y then
	      begin
		transfer_lost_info proc_name x y local_var_map;
		{< poly_int_array = poly_int_array#assert_eq x y >}
	      end
	   else default ()

	| ASSERT (GEQ (x, y)) ->
	    transfer_lost_info proc_name x y local_var_map;
	    {< poly_int_array = poly_int_array#assert_geq x y >}
	| ASSERT (GT (x, y)) ->
	    transfer_lost_info proc_name x y local_var_map;
	    {< poly_int_array = poly_int_array#assert_gt x y >}
	| ASSERT (LEQ (x, y)) ->
	    transfer_lost_info proc_name x y local_var_map;
	    {< poly_int_array = poly_int_array#assert_geq y x >}
	| ASSERT (LT (x, y)) ->
	    transfer_lost_info proc_name x y local_var_map;
	    {< poly_int_array = poly_int_array#assert_gt y x >}
	| ASSERT (NEQ (x, y)) ->
	    transfer_lost_info proc_name x y local_var_map;
	    {< poly_int_array = poly_int_array#assert_neq x y >}
	| DOMAIN_OPERATION (doms, op) ->
	    if List.mem poly_dom_name doms then
	      begin
		let pid =
                  self#analyzeOperation
                    ~domain_name:poly_dom_name
                    ~fwd_direction:true
                    ~operation:op in
		pid
	      end
	    else
	      default ()

	| ASSIGN_SYM (v, SYM_VAR w) ->
	    let a =
	      if JCHAnalysisUtils.is_numeric jproc_info v then
		if JCHAnalysisUtils.is_numeric jproc_info w then
		  self#affine_subst false v (Some w) unit_big_int zero_big_int
		else self#projectOut [v]
	      else default_v v in
	    self#change_local_var_map a v w

	| ASSIGN_SYM (v, _)
	| ASSIGN_STRUCT (v, _) ->
	    default_v v
        | _ ->
	    default () in
      let _ =
        if !dbg then
          pr__debug [STR "after PolyDom.analyzeFwd_ res"; NL; res#toPretty; NL] in
      res

    method private to_pretty =
      LBLOCK [ STR "poly_int_domain: ";
	       (if params#use_intervals then STR "use intervals " else STR ""); NL;
	       INDENT (5, poly_int_array#to_pretty); NL ]

    method toPretty = self#to_pretty

    method analyzeFwdInTransaction = self#analyzeFwd

    method analyzeBwdInTransaction = self#analyzeBwd

    method private invoke_with_target
                     (_is_static:bool)
                     (iInfo:instruction_info_int)
	             args
                     num_wvars
                     _num_rvars
                     coll_rvars
                     all_wvars:'a =

      if !dbg then
        pr__debug [STR "invoke_with_target "; NL; iInfo#toPretty; NL];

      let other_lengths =
	let all_wvars_lengths =
	  let ls = ref [] in
	  let add_length v =
	    match jproc_info#get_length v with
	    | Some l -> ls := l :: !ls
	    | _ -> () in
	  List.iter add_length all_wvars;
	  List.rev !ls in
	List.filter (fun v -> not (List.mem v all_wvars)) all_wvars_lengths in

      (if !dbg then
         pr__debug [STR "other_lengths = "; pp_list other_lengths; NL]);

      let invoke_unknown () =
	List.iter self#project_out_fields coll_rvars;
	self#project_out (all_wvars @ other_lengths) in

      let mtarget = iInfo#get_method_target () in
      if mtarget#is_top then
        invoke_unknown ()
      else if mtarget#is_top then
	begin
	  List.iter self#project_out_fields coll_rvars;
	  self#project_out (all_wvars @ other_lengths)
	end
      else
	begin
	  let procs =
            List.filter (fun p ->
                not (JCHSystem.jsystem#not_analyzed p#getSeqNumber)) mtarget#get_procs in
	  let stubs = mtarget#get_stubs in

          let _ = if !dbg then pr__debug [STR "procs = "; pp_list procs; NL] in
          let _ = if !dbg then pr__debug [STR "stubs = "; pp_list stubs; NL] in

          (* record the call so that we know the context in which we have to analyze
           * the callee *)
	  if procs <> [] then
	    begin
	      let record_call invoked_proc_name =
		let (sig_vars, sig_lengths, length_to_var) =
                  JCHIntStubs.int_stub_manager#get_all_call_vars invoked_proc_name in

		(if !dbg then pr__debug [STR "sig_vars = "; pp_list sig_vars; NL]);
		(if !dbg then pr__debug [STR "sig_lengths = "; pp_list sig_lengths; NL]);
		(if !dbg then
                   pr__debug [STR "sig_vars_with_lengths = ";
                              pp_list (length_to_var#listOfValues); NL]);

		let (invoked_args,
                     _sig_lengths_not_included,
                     _missing_length_inds) =
		  JCHAnalysisUtils.include_all_length_vars
                    jproc_info (JCHSystemUtils.get_read_vars args)
                    sig_vars length_to_var in

		(if !dbg then
                   pr__debug [STR "invoked_args = "; pp_list invoked_args; NL]);

		let call_poly_int_array =
                  poly_int_array#get_call jproc_info invoked_args in

		(if !dbg then
                   pr__debug [STR "record_call call_poly_int_array = "; NL;
                              call_poly_int_array#toPretty; NL]);

		JCHIntStubs.int_stub_manager#record_poly_int_array_call
                  jproc_info#get_name invoked_proc_name call_poly_int_array in
	      List.iter record_call procs;

	      if !dbg then pr__debug [STR "after record_call"; NL]
	    end;

	  if procs = [] && stubs = [] then
	    begin
	      List.iter self#project_out_fields coll_rvars;
	      self#project_out (all_wvars @ other_lengths)
	    end
	  else if all_wvars = [] then {< >}
	  else
	    begin
	      let arg_vars = List.map (fun (_,v,_) -> v) args in
              let _ = if !dbg then pr__debug [STR "arg_vars = "; pp_list arg_vars; NL] in
	      let (empty_collections, _non_empty_collections) =
		let is_empty_collection v =
                  poly_int_array#get_extra_infos#is_empty_collection v in
		let (empty, non_empty) = List.partition is_empty_collection coll_rvars in
		(VariableCollections.set_of_list empty, non_empty) in

	      let (invoked_poly_int_array, invoked_conds, sig_vars_opt) =

		let (invoked_proc_poly_int_array, proc_sig_vars, proc_sig_arrays,
		     invoked_stub_poly_int_array, stub_sig_vars, stub_sig_arrays, conds) =
		  JCHIntStubs.int_stub_manager#invoke_poly_int_array jproc_info procs stubs in

		(if !dbg then pr__debug [STR "after invoke_poly_int_array"; NL]);

		let stub_sig_vars_opt =
                  match invoked_stub_poly_int_array with
                  | None -> None
                  | _ -> Some stub_sig_vars in
		let add_invoked
                      res_poly_int_array invoked_poly_int_array_opt sig_vars sig_arrays =
		  match invoked_poly_int_array_opt with
		  | Some invoked_poly_int_array ->

		     (if !dbg then
                       pr__debug [STR "invoked_poly_int_array = "; NL;
                                  invoked_poly_int_array#toPretty; NL]);

		     (if invoked_poly_int_array#is_bottom then
                        raise (JCH_no_return_proc (mtarget#toPretty)));

		     let inds_to_eliminate = ref [] in
		     let invoked_vars = ref [] in
		     let check_arg ind (_, arg, _) =
		       (if JCHAnalysisUtils.is_numeric jproc_info arg then
			 invoked_vars := arg :: !invoked_vars
		       else
                         inds_to_eliminate := ind :: !inds_to_eliminate);
		       ind + 1 in
		     let ind = List.fold_left check_arg 0 args in
		     let assoc_arg_sig = List.combine args sig_vars in

		     (if !dbg then
                       pr__debug [STR "sig_arrays = "; pp_list sig_arrays; NL]);

		     let check_arrays ind array =

		       (if !dbg then
                         pr__debug [STR "check_arrays "; INT ind; STR " ";
                                    array#toPretty; NL]);
		       (if !dbg then
                         pr__debug [STR "sig_vars = "; pp_list sig_vars; NL]);
		       (if !dbg then
                         pr__debug [STR "args = ";
                                    pp_list (List.map (fun (_,v,_) -> v) args); NL]);

		       let ((_,arg,_), _) =
                         List.find (fun (_v, v') ->
                             v'#getName#equal array#getName) assoc_arg_sig in

		       (if !dbg then pr__debug [STR "arg = "; arg#toPretty; NL]);

		       let arg_info = jproc_info#get_jvar_info arg in
		       if not arg_info#has_length then
			 begin
			   (if !dbg then
                              pr__debug [STR "add ind to eliminate for arg_info = ";
                                         arg_info#toPretty; STR " "; INT ind; NL]);

			   inds_to_eliminate := ind :: !inds_to_eliminate
			 end;
		       ind + 1 in
		     let _ = List.fold_left check_arrays ind sig_arrays in
		     let invoked_vars = List.rev !invoked_vars in

		     let (invoked_lengths, invoked_target_lengths) =
                       let lens = ref [] in
		       let target_lens = ref [] in
		       let add_var var target_var =

			 (if !dbg then
                            pr__debug [STR "add_var "; var#toPretty; STR " ";
                                       target_var#toPretty; NL]);

			 match jproc_info#get_length var with
			 | Some len ->
			    lens := len :: !lens;
			    if (List.exists (fun v ->
                                    v#equal target_var) sig_arrays) then
                              (* The invoked target might have argument that are
                               * objects rather than arrays *)
			      target_lens := len :: !target_lens
			 | _ -> () in
		       List.iter2 add_var arg_vars sig_vars;
		       (List.rev !lens, List.rev !target_lens) in
		     let all_invoked_vars = invoked_vars @ invoked_target_lengths in

		     let _ =
                       (if !dbg then
                         pr__debug [STR "all_invoked_vars = ";
                                    pp_list all_invoked_vars; NL]) in

		     let arg_length = List.length arg_vars + List.length sig_arrays in
		     let meet_poly_int_array =
		       res_poly_int_array#meet_invoked
                         invoked_poly_int_array
                         !inds_to_eliminate arg_length
			 invoked_vars
                         invoked_lengths
                         invoked_target_lengths
                         num_wvars
                         coll_rvars in
		     let changed =
                       List.filter
                         invoked_poly_int_array#get_extra_infos#is_changed_sym_param
                         all_invoked_vars in

		     (if !dbg then
                        pr__debug [STR "variables changed in invoke = ";
                                   pp_list changed; NL]);

		     self#record_changed_sym_params changed;

		     (if !dbg then
                        pr__debug [STR "meet_poly_int_array = "; NL;
                                   meet_poly_int_array#toPretty; NL]);

		     meet_poly_int_array
                  |  _ -> poly_int_array#project_out all_wvars in
		(add_invoked
                   (add_invoked
                      poly_int_array
                      invoked_proc_poly_int_array
                      proc_sig_vars
                      proc_sig_arrays)
		   invoked_stub_poly_int_array
                   stub_sig_vars
                   stub_sig_arrays, conds, stub_sig_vars_opt) in

	      (if !dbg then
                 pr__debug [STR "invoked_poly_int_array "; NL;
                            invoked_poly_int_array#toPretty; NL]);

	      (if !dbg then
                 pr__debug [STR "empty_collections = ";
                            empty_collections#toPretty; NL]);

	      let changed_vars = ref [] in
	      let add_cond p_int_array cond =

		(if !dbg then
                   pr__debug [STR "add_cond "; NL; p_int_array#toPretty; NL;
                              JCHIntStubs.stub_condition_to_pretty cond; NL]);
		match cond with
		| JCHIntStubs.CheckReturnType ->
		    let ret = JCHSystemUtils.get_arg_var "return" args in
		    p_int_array#check_type ret
		| JCHIntStubs.JoinInfo (src1, src2, dst) ->
		   begin
		     match sig_vars_opt with
		     | Some sig_vars ->
			(if !dbg then
                           pr__debug [STR "arg_vars = "; pp_list arg_vars; NL]);

			(if !dbg then
                           pr__debug [STR "sig_vars = "; pp_list sig_vars; NL]);

			let sig_var_arg_var =
                          List.combine
                            (List.map (fun v -> v#getIndex) sig_vars) arg_vars in
			let dst_var = List.assoc dst#getIndex sig_var_arg_var in
			let src1_var = List.assoc src1#getIndex sig_var_arg_var in
			let src2_var = List.assoc src2#getIndex sig_var_arg_var in
			changed_vars := dst_var :: !changed_vars;
			if JCHAnalysisUtils.is_numeric jproc_info dst_var then
			  if JCHAnalysisUtils.is_numeric jproc_info src1_var
                             && JCHAnalysisUtils.is_numeric jproc_info src2_var then
			    begin
			      empty_collections#remove dst_var;
			      p_int_array#set_join dst_var src1_var src2_var
			    end
			  else
                            p_int_array#project_out [dst_var]
			else
                          p_int_array
		      | None -> p_int_array
		    end
		| JCHIntStubs.CopyInfo (var1, var2) ->
		   begin

                     (if !dbg then
                        pr__debug [STR "CopyInfo "; var1#toPretty; STR " ";
                                   INT var1#getIndex; STR " "; var2#toPretty;
                                   STR " "; INT var2#getIndex; NL]);

		     match sig_vars_opt with
		     | Some sig_vars ->
			(if !dbg then
                           pr__debug [STR "arg_vars = "; pp_list arg_vars; NL]);

			(if !dbg then
                           pr__debug [STR "sig_vars = "; pp_list sig_vars; NL]);

			let sig_var_arg_var =
                          List.combine
                            (List.map (fun v -> v#getIndex) sig_vars) arg_vars in
			let arg1 = List.assoc var1#getIndex sig_var_arg_var in
			let arg2 = List.assoc var2#getIndex sig_var_arg_var in

			(if !dbg then
                           pr__debug [STR "arg1 = "; arg1#toPretty;
                                      STR ", arg2 = "; arg2#toPretty; NL]);

			changed_vars := arg2 :: !changed_vars;
			if JCHAnalysisUtils.is_numeric jproc_info arg2 then
			  if JCHAnalysisUtils.is_numeric jproc_info arg1 then
			    let interval = poly_int_array#get_interval arg1 in
			    let excluded_vals =
                              poly_int_array#get_extra_infos#get_excluded_vals arg1 in
			    p_int_array#copy_info arg2 interval excluded_vals
			  else
                            p_int_array#project_out [arg2]
			else
                          p_int_array
		     | None -> p_int_array
		   end
		| JCHIntStubs.PostInterval (var, interval) ->
		   begin
		     match sig_vars_opt with
		     | Some sig_vars ->
			let sig_var_arg_var =
                          List.combine (List.map (fun v -> v#getIndex) sig_vars) arg_vars in
			let arg = List.assoc var#getIndex sig_var_arg_var in
			changed_vars := arg :: !changed_vars;
			if JCHAnalysisUtils.is_numeric jproc_info arg then
			  p_int_array#set_interval var interval
			else
                          p_int_array
		     | None -> p_int_array
		   end
		| JCHIntStubs.Abstract var ->
		   begin
		     match sig_vars_opt with
		     | Some sig_vars ->
			let sig_var_arg_var =
                          List.combine (List.map (fun v -> v#getIndex) sig_vars) arg_vars in
			let arg = List.assoc var#getIndex sig_var_arg_var in
			changed_vars := arg :: !changed_vars;
			if JCHAnalysisUtils.is_numeric jproc_info arg then
			  p_int_array#project_out [arg]
			else
                          p_int_array
		     | _ -> p_int_array
		   end in

	      self#record_changed_sym_params !changed_vars;
	      let cond_poly_int =
		let pia_cond =
                  List.fold_left add_cond invoked_poly_int_array invoked_conds in
		let add_empty pia v = pia#add_empty_collection v in
		List.fold_left add_empty pia_cond empty_collections#toList in

	      let length_poly_int =
		let unassigned_lengths =
                  List.filter (fun l ->
                      (cond_poly_int#get_interval l)#isBottom) other_lengths in
		cond_poly_int#project_out unassigned_lengths in
	      let red_poly_int = length_poly_int#move_simple_ineqs in
	      let best_poly_int = red_poly_int#set_best_intervals in
	      let is_restricted v =
                JCHAnalysisUtils.is_numeric jproc_info v && not (self#is_const v) in

	      let restrict_poly_int =
                best_poly_int#restrict_to_type (List.filter is_restricted arg_vars) in

	      List.iter (self#update_fields restrict_poly_int) coll_rvars;
	      if params#use_intervals then
                {< poly_int_array = restrict_poly_int#drop_poly >}
	      else
                {< poly_int_array = restrict_poly_int >}
	    end
	end

    method private invoke
                     (is_static:bool)
                     _cn_msig_opt
                     (iInfo:instruction_info_int)
                     args =

      let _ =
        if !dbg then
          pr__debug [STR "analyze_invoke "; proc_name_pp proc_name; NL;
                     iInfo#toPretty; NL] in

      let res =
        let wvars = JCHSystemUtils.get_write_vars args in
        List.iter add_reachable wvars;
        let num_wvars = List.filter (JCHAnalysisUtils.is_numeric jproc_info) wvars in
        let rvars = JCHSystemUtils.get_read_vars args in
        let num_rvars =
          List.filter (JCHAnalysisUtils.is_numeric jproc_info) rvars in
        let coll_rvars =
          List.filter (JCHAnalysisUtils.is_collection_or_array jproc_info) num_rvars in
        let all_wvars = num_wvars @ coll_rvars in

        (* remove some targets *)
        if iInfo#has_method_target then
	  begin
	    try
	      self#invoke_with_target
                is_static iInfo args num_wvars num_rvars coll_rvars all_wvars
	    with
            | JCH_no_return_proc _pp -> self#mkBottom
	  end
        else
	  begin
	    List.iter self#project_out_fields coll_rvars;
	    self#project_out all_wvars;
	  end in

      let _ =
        begin
          (if !dbg then pr__debug [STR "after invoke, res = "; res#toPretty; NL]);
          if iInfo#has_method_target && !dbg then
            pr__debug [STR "mtarget = "; NL;
                       (iInfo#get_method_target ())#toPretty; NL]
        end in

      res

    method analyzeOperation
             ~(domain_name: string)
             ~(fwd_direction: bool)
             ~(operation: operation_t): 'a =

      let _ =
        if !dbg then
          pr__debug [STR "PolyDom.analyzeOperation ";
                     operation_to_pretty operation; NL;
                     self#toPretty; NL] in

      let res =
        match operation.op_name#getBaseName with
        |"init_params" ->
	  List.iter
            add_reachable (JCHSystemUtils.get_write_vars operation.op_args);
	  if self#isBottom || poly_int_array#is_top then
            {< >}
	  else
	    let simple_poly_int_array = poly_int_array#move_simple_ineqs in
	    {< poly_int_array = simple_poly_int_array >}
        | "init_assumptions" ->
	   List.iter add_reachable (JCHSystemUtils.get_write_vars operation.op_args);
	   if self#isBottom then
             {< >}
	   else
	     let p = poly_int_array#init_assumptions jproc_info in
	     {< poly_int_array = p >}
        | "add_vars" -> {< >}
        | "remove_vars" ->
	   let vars = List.map (fun (_,v,_) -> v) operation.op_args in
	   self#remove vars
        | "i"
        | "ii" ->
	   let pc = operation.op_name#getSeqNumber in
	   let bcloc = get_bytecode_location cms#index pc in
	   let iInfo = app#get_instruction bcloc in
	   begin
	     match mInfo#get_opcode pc with
	     | OpInvokeStatic (cn, msig) ->
	        self#invoke true (Some (cn, msig)) iInfo operation.op_args
	     | OpInvokeVirtual _ ->
                self#invoke false None iInfo operation.op_args
	     | OpInvokeInterface (cn, msig)
	       | OpInvokeSpecial (cn, msig) ->
                self#invoke false (Some (cn, msig)) iInfo operation.op_args
	     | OpNew _cn ->
	        let var = JCHSystemUtils.get_arg_var "ref" operation.op_args in
	        add_reachable var;

	        if JCHAnalysisUtils.is_numeric jproc_info var then
		  let new_poly_int_array = poly_int_array#project_out [var] in
		  if JCHAnalysisUtils.is_collection jproc_info var then
		    {< poly_int_array = new_poly_int_array#add_empty_collection var >}
		  else
                    {< poly_int_array = new_poly_int_array >}
	        else
                  {< >}
	     | OpGetStatic _
	     | OpGetField _ ->
	        let var = JCHSystemUtils.get_arg_var "val" operation.op_args in
	        add_reachable var;

	        JCHFields.int_field_manager#record_field iInfo;
	        if JCHAnalysisUtils.is_numeric jproc_info var then
		  begin
		    if JCHAnalysisUtils.is_collection_or_array jproc_info var then
		      add_variable_to_field var iInfo;
		    let intervals =
                      JCHFields.int_field_manager#get_field_intervals
                        iInfo#get_field_target in
		    let fInfo = iInfo#get_field_target in
		    {< poly_int_array =
                         poly_int_array#get_field jproc_info fInfo intervals var >}
		  end
	        else
                  {< >}
	     | OpPutStatic _
	     | OpPutField _ ->
	        let var = JCHSystemUtils.get_arg_var "val" operation.op_args in
	        if JCHAnalysisUtils.is_numeric jproc_info var then
		  begin
		    let fInfo = iInfo#get_field_target in
		    {< poly_int_array = poly_int_array#add_field var fInfo >}
		  end
	        else {< >}

	     | OpNewArray _ ->
	        let array = JCHSystemUtils.get_arg_var "ref" operation.op_args in
	        let length = JCHSystemUtils.get_arg_var "length" operation.op_args in
	        add_reachable array;

	        if JCHAnalysisUtils.is_numeric jproc_info array then
		  {< poly_int_array = poly_int_array#new_array array [length] >}
	        else
                  {< >}

	     | OpAMultiNewArray _ ->
	        let array = JCHSystemUtils.get_arg_var "ref" operation.op_args in
	        let dims = JCHSystemUtils.get_read_vars operation.op_args in
	        add_reachable array;

	        if JCHAnalysisUtils.is_numeric jproc_info array then
		  {< poly_int_array = poly_int_array#new_array array dims >}
	        else
                  {< >}

	     | OpArrayStore _ ->
	        let array = JCHSystemUtils.get_arg_var "array" operation.op_args in
	        let element = JCHSystemUtils.get_arg_var "val" operation.op_args in
	        let index = JCHSystemUtils.get_arg_var "index" operation.op_args in
	        record_array_access poly_int_array array index;
	        self#record_changed_sym_params [array];

	        if JCHAnalysisUtils.is_numeric jproc_info array then
		  if JCHAnalysisUtils.is_numeric jproc_info element then
		    let new_poly_int_array =
                      poly_int_array#set_join array element array in
                    begin
		      self#update_fields new_poly_int_array array;
		      {< poly_int_array = new_poly_int_array >}
		    end
		  else
		    begin
		      self#project_out_fields array;
		      {< poly_int_array = poly_int_array#project_out_array array >}
		    end
	        else
                  {< >}

	     | OpArrayLoad _ ->
	        let array = JCHSystemUtils.get_arg_var "array" operation.op_args in
	        let element = JCHSystemUtils.get_arg_var "val" operation.op_args in
	        let index = JCHSystemUtils.get_arg_var "index" operation.op_args in
	        record_array_access poly_int_array array index;
	        let new_poly_int_array = poly_int_array in (* CHANGE : bring back info about the dims *)
	        add_reachable element;

	        if JCHAnalysisUtils.is_numeric jproc_info element then
		  if JCHAnalysisUtils.is_numeric jproc_info array then
		    {< poly_int_array = new_poly_int_array#array_load array element >}
		  else
                    self#projectOut [element]
	        else
		  begin
		    self#record_changed_sym_params [array];
		    {< >}
		  end

	     | OpArrayLength ->
	        let var = JCHSystemUtils.get_arg_var "ref" operation.op_args in
	        let length = JCHSystemUtils.get_arg_var "val" operation.op_args in
	        add_reachable length;
	        {< poly_int_array = poly_int_array#transfer_fields false length var >}

	     | OpCheckCast _ ->
	        let ref = JCHSystemUtils.get_arg_var "src1" operation.op_args in
	        let ref_new_type = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	        add_reachable ref_new_type;

	        if JCHAnalysisUtils.is_numeric jproc_info ref_new_type then
		  if JCHAnalysisUtils.is_numeric jproc_info ref then
		    begin
		      (* We are not using affine_image here because there
                       * cannot be over/underflow *)
		      let (new_poly_int_array, _, _) =
		        if self#is_const ref then
			  poly_int_array#affine_subst
                            ref_new_type None zero_big_int (self#get_const_val ref)
		        else
			  poly_int_array#affine_subst
                            ref_new_type (Some ref) unit_big_int zero_big_int in
		      {< poly_int_array = new_poly_int_array >}
		    end
		  else
                    self#copy_num_info (self#projectOut [ref_new_type]) ref_new_type ref
	        else
                  self#copy_num_info self ref_new_type ref

	     | OpI2F -> (* [-2^23,2^23] is a safe conversion range ? *)
	        let src1 = JCHSystemUtils.get_arg_var "src1" operation.op_args in
	        let dst1 = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	        if self#is_const src1 then
		  begin
		    let const = self#get_const_val src1 in
		    if le_big_int const (big_int_of_int 8388608)
		       && ge_big_int const (big_int_of_int (-8388608)) then
		      self#affine_subst false dst1 None zero_big_int const
		    else
		      self#project_out [dst1]  (* CHANGE *)
		  end
	        else
		  begin
		    let src1_int = poly_int_array#get_interval src1 in
		    let max_conversion_int =
		      mkInterval (mkNumerical (-8388608)) (mkNumerical 8388608) in
		    if src1_int#leq max_conversion_int then
		      self#affine_subst false dst1 (Some src1) unit_big_int zero_big_int
		    else self#project_out [dst1]  (* CHANGE *)
		  end

	     | OpI2L
	     | OpI2D
	     | OpL2F
	     | OpL2D
	     | OpF2D ->
	        let src1 = JCHSystemUtils.get_arg_var "src1" operation.op_args in
	        let dst1 = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	        if self#is_const src1 then
		  self#affine_subst
                    false dst1 None zero_big_int (self#get_const_val src1)
	        else
		  self#affine_subst
                    false dst1 (Some src1) unit_big_int zero_big_int

	     | OpD2L
	     | OpD2I
	     | OpF2I
	     | OpF2L ->
	        let src1 = JCHSystemUtils.get_arg_var "src1" operation.op_args in
	        let dst1 = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	        self#down_cast_float src1 dst1

	     | OpL2I ->
	        let src1 = JCHSystemUtils.get_arg_var "src1" operation.op_args in
	        let dst1 = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	        let tp_interval_opt = None in
	        if self#is_const src1 then
		  self#affine_image_down_cast
                    None
                    None
                    (dst1, unit_big_int)
                    []
                    (self#get_const_val src1)
                    src1
                    dst1
                    tp_interval_opt
	        else
		  self#affine_image_down_cast
                    None
                    (Some src1)
                    (dst1, unit_big_int)
                    [(src1, unit_big_int)]
                    zero_big_int
                    src1
                    dst1
                    tp_interval_opt
	  | OpI2B
	  | OpI2C
	  | OpI2S ->
	      let src1 = JCHSystemUtils.get_arg_var "src1" operation.op_args in
	      let dst1 = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	      let pc = iInfo#get_location#get_pc in
	      let tp_interval_opt =
                (* type of the variable could be int although although the
                 * truncation is to byte, char or short *)
		match iInfo#get_opcode with
		| OpI2B -> Some (JCHTypeUtils.byte_interval)
		| OpI2C -> Some (JCHTypeUtils.char_interval)
		| OpI2S -> Some (JCHTypeUtils.short_interval)
		| _ -> None in
	      let pc_opt = if !arith_casts#has pc then Some pc else None in
	      if self#is_const src1 then
		self#affine_image_down_cast
                  pc_opt
                  None
                  (dst1, unit_big_int)
                  []
                  (self#get_const_val src1)
                  src1
                  dst1
                  tp_interval_opt
	      else
		self#affine_image_down_cast
                  pc_opt
                  (Some src1)
                  (dst1, unit_big_int)
                  [(src1, unit_big_int)]
                  zero_big_int
                  src1
                  dst1
                  tp_interval_opt

	  | OpD2F ->
	      let dst1 = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	      self#projectOut [dst1]

	  | OpFloatConst f
	  | OpDoubleConst f ->
	     let dst1 = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
             begin
	       add_reachable dst1;
	       {< poly_int_array = poly_int_array#float_const dst1 f >}
             end

	  | OpAdd Float
	  | OpAdd Double ->
	      let v = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	      let x = JCHSystemUtils.get_arg_var "src1_1" operation.op_args in
	      let y = JCHSystemUtils.get_arg_var "src1_2" operation.op_args in
	      self#affine_image
                false
                None
                (v, unit_big_int)
                [(x, unit_big_int); (y, unit_big_int)]
                zero_big_int

	  | OpSub Float
	  | OpSub Double ->
	      let v = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	      let x = JCHSystemUtils.get_arg_var "src1_1" operation.op_args in
	      let y = JCHSystemUtils.get_arg_var "src1_2" operation.op_args in
	      self#affine_image
                false
                None
                (v, unit_big_int)
                [(x, unit_big_int); (y, neg_unit_big_int)]
                zero_big_int

	  | OpMult Float
	  | OpMult Double ->
	      let v = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	      let x = JCHSystemUtils.get_arg_var "src1_1" operation.op_args in
	      let y = JCHSystemUtils.get_arg_var "src1_2" operation.op_args in
	      self#mult v x y

	  | OpDiv Float
	  | OpDiv Double ->
	     let v = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	     let x = JCHSystemUtils.get_arg_var "src1_1" operation.op_args in
	     let y = JCHSystemUtils.get_arg_var "src1_2" operation.op_args in
	     self#div v x y

	  | OpRem _ ->
	     let x = JCHSystemUtils.get_arg_var "src1_1" operation.op_args in
	     let y = JCHSystemUtils.get_arg_var "src1_2" operation.op_args in
	     let v = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	     self#rem v x y

	  | OpIAnd
	  | OpLAnd ->
	     let x = JCHSystemUtils.get_arg_var "src1_1" operation.op_args in
	     let y = JCHSystemUtils.get_arg_var "src1_2" operation.op_args in
	     let v = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
             begin
	       add_reachable v;
	       {< poly_int_array = poly_int_array#log_and v x y >}
	     end

	  | OpIOr
	  | OpLOr ->
	     let x = JCHSystemUtils.get_arg_var "src1_1" operation.op_args in
	     let y = JCHSystemUtils.get_arg_var "src1_2" operation.op_args in
	     let v = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
             begin
	       add_reachable v;
	       {< poly_int_array = poly_int_array#log_and v x y >}
	     end

	  | OpStore (t, n) ->
	      let is_r_n v =
		let name = v#getName in
		let base_name = name#getBaseName in
		if base_name.[0] = 'r'
                   && base_name.[1] <> 'e'
                   && (int_of_string (Str.string_after base_name 1)) = n then
		  match t with
		  | Object -> (List.hd name#getAttributes) = "sym"
		  | _ -> (List.hd name#getAttributes) = "num"
		else
                  false in
	      let (_, rest_local_var_map) =
                List.partition (fun (orig_v, _v) -> is_r_n orig_v) local_var_map in
	      let new_var = JCHSystemUtils.get_arg_var "dst1" operation.op_args in
	      let orig_var =
		try
		  List.find is_r_n orig_local_vars
		with
		| Not_found ->
		   raise
                     (JCH_failure
			(LBLOCK [
                             STR "original variable not found in ";
			     STR "JCHPolyIntDomainNoArrays.analyzeOperation" ])) in
	      let new_local_var_map = (orig_var, new_var) :: rest_local_var_map in
	      {< local_var_map = new_local_var_map >}

	  | _ ->
             begin
	       pr__debug [
                   STR "Analysis failed: Poly does not implement the operation"; NL;
                   operation_to_pretty operation];
	       raise
                 (params#analysis_failed 3 "Poly does not implement the operation")
             end
	   end
        | _ ->
           begin
	     pr__debug [
                 STR "Analysis failed: Poly does not implement the operation"; NL;
                 operation_to_pretty operation];
	     raise
               (params#analysis_failed 3 "Poly does not implement the operation")
           end in

      let _ =
        if !dbg then
          pr__debug [STR "after analyzeOperation res "; NL; res#toPretty; NL] in
      res

  end


let get_poly_int_array (poly_dom: CHDomain.domain_int) =

  (if !dbg then
     pr__debug [STR "get_poly_int_array "; NL; poly_dom#toPretty; NL]);

  let _ = poly_dom#special "set_poly_int_array" [] in
  get_st_poly_int_array ()

let get_relational_exprs include_loop_counters poly_int_dom =
  if poly_int_dom#isBottom then
    []
  else
    let args =
      if include_loop_counters then
        [NUM_DOM_ARG numerical_zero] else [] in
    let _ = poly_int_dom#special "get_local_var_invariants" args in
    get_st_relational_exprs ()

let get_local_var_map poly_int_dom =
  if poly_int_dom#isBottom then
    []
  else
    let _ = poly_int_dom#special "set_local_var_map" [] in
    get_st_local_var_map ()

let get_poly_vars poly_int_dom =
  if poly_int_dom#isBottom then
    []
  else
    let _ = poly_int_dom#special "set_poly_vars" [] in
    get_st_poly_vars ()


let mk_param_map
      (jproc_info: JCHProcInfo.jproc_info_t):
      (variable_t list * (variable_t * variable_t) list) =
  let name = jproc_info#get_name in
  let orig_proc = (JCHSystem.jsystem#get_original_chif#getProcedure name) in
  let orig_locals =
    List.filter (fun v ->
        JCHSystemUtils.is_register v
        || JCHSystemUtils.is_return v) orig_proc#getScope#getVariables in
  let jvar_infos = jproc_info#get_jvar_infos#listOfValues in
  let params = List.filter (fun info -> info#is_parameter) jvar_infos in
  let map =
    List.map (fun info -> let v = info#get_variable in (v, v)) params in
  (orig_locals, map)

let get_poly_dom
      jproc_info
      init_poly_int_array
      reset_old_join_widening
      reset_use_intervals  =
  let proc_name = jproc_info#get_name in

  (if !dbg then
     pr__debug [jproc_info#get_opcodes#toPretty; NL; jproc_info#toPretty; NL]);

  (if !dbg then
     pr__debug [STR "init_poly_int_array "; init_poly_int_array#toPretty; NL]);

  let consts =
    let is_const var =
      List.exists (fun (i, _) ->
          var#getIndex = i) init_poly_int_array#get_var_to_const in
    List.filter is_const jproc_info#get_variables in
  let div2div2quot =
    reset_ref_vars
      proc_name
      jproc_info
      consts
      reset_old_join_widening in
  params#reset reset_use_intervals;

  let new_init_poly_int_array =
    let new_extra_infos =
      init_poly_int_array#get_extra_infos#add_div_info div2div2quot in
    let pia = init_poly_int_array#set_extra_infos new_extra_infos in
    if params#use_intervals then
      pia#move_simple_ineqs#drop_poly
    else pia in
  new poly_int_domain_no_arrays_t
      jproc_info new_init_poly_int_array (mk_param_map jproc_info)

let get_interval poly_int_dom var =
  let poly_interval_array = get_poly_int_array poly_int_dom in
  poly_interval_array#get_interval var

let bottom_poly_int_dom jproc_info =
  new poly_int_domain_no_arrays_t
      jproc_info bottom_poly_interval_array (mk_param_map jproc_info)

let top_poly_int_dom jproc_info vs =
  let top = top_poly_interval_array [] vs in
  new poly_int_domain_no_arrays_t jproc_info top (mk_param_map jproc_info)

let project_out_loop_counters poly =
  poly#special "project_out_loop_counters" []

let remove_duplicates poly =
  poly#special "remove_duplicates" []

let restrict_to_vars poly vars =
  poly#special "restrict_to_vars" (List.map (fun v -> VAR_DOM_ARG v) vars)

let get_relational_exprs_vars_fields (poly: poly_int_domain_no_arrays_t) vars =
  let _ = poly#special
      "get_vars_fields_rel_exprs" (List.map (fun v -> VAR_DOM_ARG v) vars) in
  get_st_relational_exprs ()

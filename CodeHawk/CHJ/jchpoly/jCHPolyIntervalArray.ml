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

open Big_int_Z

(* chlib *)
open CHBounds
open CHIntervals
open CHLanguage
open CHPretty
open CHNumerical
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes

(* jchpre *)
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHSystemUtils
open JCHPrintUtils

(* jchpoly *)
open JCHLinearConstraint
open JCHPoly
open JCHIntervalArray 
open JCHNumericUtils
open JCHNumericInfo

let dbg = ref false 

let params = JCHAnalysisUtils.numeric_params 
let zero_bound = CHBounds.bound_of_num numerical_zero 
let one_bound = CHBounds.bound_of_num numerical_one

module ConstraintCollections = CHCollections.Make (
  struct
    type t = linear_constraint_t
    let compare c1 c2 = c1#compare c2
    let toPretty c = c#toPretty
  end)

let local_vars = ref [] 
let set_local_vars vs = local_vars := vs

class poly_interval_array_t v2const poly_vs =  
  object (self: 'a) 
  
    val var_to_const : (int * numerical_t) list = v2const 
    val poly_vars : variable_t list = poly_vs

    (* variable to the index used in interval_array *)                                    
    val var_to_index : (int * int) list = mk_var_to_index poly_vs 
    val poly : poly_t = top_poly
    val interval_array : interval_array_t = make_top_intervals 0
    val extra_infos : numeric_info_t = new numeric_info_t

    method get_var_to_const = var_to_const
    method get_poly_vars = poly_vars
    method get_var_to_index = var_to_index 
    method get_poly = poly
    method get_interval_array = interval_array
    method get_extra_infos = extra_infos
    method get_excluded_vals var = 
      extra_infos#get_excluded_vals var

    method has_var (var: variable_t) = 
      (List.exists (fun (i,_) -> var#getIndex = i) var_to_const)
      || (List.exists (fun v -> v#getIndex = var#getIndex) poly_vars)
	
    method set_poly poly = 
      {< poly = poly >}

    method set_interval_array new_interval_array = 
      {< interval_array = new_interval_array >}

    method set_interval var interval = 
      let new_interval_array = interval_array#copy_set (self#get_index var) interval in
      {< interval_array = new_interval_array >} 

    method set_extra_infos extra_infos = 
      {< extra_infos = extra_infos >}

    method private get_dim = List.length poly_vars

    method private mk_bottom = 
      {< var_to_const = [] ;
	poly_vars = [] ;
	var_to_index = [] ;
	poly = bottom_poly ; 
	interval_array = interval_array#make_bottom_intervals 0 ;
	extra_infos = new numeric_info_t >}

    method mk_empty v2const poly_vs = 
      let v2ind = mk_var_to_index poly_vs in
      {< var_to_const = v2const ;
	poly_vars = poly_vs ;
	var_to_index = v2ind ;
	poly = top_poly ;
	interval_array = interval_array#make_bottom_intervals (List.length poly_vs) ;
	extra_infos = new numeric_info_t >}      

    method private mk_top v2const poly_vs = 
      let v2ind = mk_var_to_index poly_vs in
      {< var_to_const = v2const ;
	poly_vars = poly_vs ;
	var_to_index = v2ind ;
	poly = top_poly ;
	interval_array = interval_array#make_top_intervals (List.length poly_vs) ;
	extra_infos = new numeric_info_t >}      

    method drop_poly = 
      if poly#is_bottom then {< >} 
      else {< poly = top_poly >}

    method drop_all = 
      if poly#is_bottom then {< >}
      else {< poly = top_poly ;
              interval_array = interval_array#make_from_types (List.length poly_vars) >}

    method is_bottom = poly#is_bottom

    method is_top = (* what about the excluded values ? *)
      let check_array i = 
	let int = interval_array#get i in
	if int#isTop || int#isBottom then () 
	else raise Exit in
      try (* Just as a way not to look at all the intervals if one is not top or bottom *) 
	if poly#is_top then 
	  begin
	    for i = 0 to pred self#get_dim do
	      check_array i
	    done ;
	    true 
	  end
	else false 
      with Exit -> false 

    method clone = 
      {< poly = poly#clone ;
	 interval_array = interval_array#clone ;
	 extra_infos = extra_infos#clone >}

    (* Change the vars but the info stays the same. 
     * Eliminate the lengths that do not correspont to an array length 
     * in new_poly_length_vars 
     * Add lengths that are in the new_poly_length_vars but not in poly_vars  *)
    method change_vars
             proc_name
             new_proc_name
             (new_poly_vars:variable_t list)
             (new_length_poly_vars:variable_t list) : 'a  =
      
      if !dbg then
        pr__debug [STR "change vars to "; new_proc_name#toPretty; NL;
                   pp_list poly_vars; NL; 
		   pp_list new_poly_vars; STR " ";
                   pp_list new_length_poly_vars; NL] ;

      let (length_poly_vars, non_length_poly_vars) =
        List.partition JCHSystemUtils.is_length poly_vars in
      let (all_new_poly_vars, new_poly, new_interval_array, all_map):
            variable_t list * poly_t * interval_array_t * (int * variable_t) list = 
	let new_jproc_info = JCHSystem.jsystem#get_jproc_info new_proc_name in
	let map_v = List.combine non_length_poly_vars new_poly_vars in
	let length_map = ref [] in
	let lengths_to_stay = ref [] in
	let lengths_to_add = ref [] in
	let all_length_poly_vars = ref [] in
	let index = ref 0 in
	let map = 
	  let mp = ref [] in
	  let add_var v = 
	    mp := (!index, !index) :: !mp ;
	    incr index in
	  List.iter add_var non_length_poly_vars ;
	  mp in
	let index_skip = ref !index in
	let add_new_length new_length = 
	  let new_var =
            Option.get (new_jproc_info#get_variable_from_length new_length) in
	  let (var, _) =
            List.find (fun (v, new_v) -> new_v#equal new_var) map_v in
	  let l = JCHSystemUtils.make_length var in
	  try
	    let length =
              List.find (fun v -> v#getName = l#getName) length_poly_vars in
	    lengths_to_stay := length :: !lengths_to_stay ;
	    length_map := (length#getIndex, new_length) :: !length_map ;
	    all_length_poly_vars := length :: !all_length_poly_vars ; 
	    map := (!index_skip, !index) :: !map ;
	    incr index;
	    incr index_skip 
	  with Not_found -> 
	    lengths_to_add := (l, !index) :: !lengths_to_add ;
	    length_map := (l#getIndex, l) :: !length_map ;
	    all_length_poly_vars := l :: !all_length_poly_vars ;
	    incr index in
        List.iter add_new_length new_length_poly_vars ;
	let lengths_to_add = List.rev !lengths_to_add in
	let add_to_map (var, ind) = 
	  map := (!index_skip, ind) :: !map ;
	  incr index_skip in
	List.iter add_to_map lengths_to_add ;
	let lengths_to_remove =
          List.filter (fun v ->
              not (List.mem v !lengths_to_stay)) length_poly_vars in
	let restr_poly_vars = non_length_poly_vars in
	let new_poly_interval_array = self#project_out lengths_to_remove in 
	let (all_poly, all_interval_array) = 
	  if lengths_to_add = [] then
            (new_poly_interval_array#get_poly,
             new_poly_interval_array#get_interval_array) 
	  else 
	    let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
	    let new_lengths : variable_t list = List.map fst lengths_to_add in
	    let pia = new_poly_interval_array#add_vars jproc_info new_lengths in
	    (pia#get_poly#remap_indices !map,
             pia#get_interval_array#remap (List.length !map) !map) in
	let m = List.combine
                  (List.map (fun v -> v#getIndex) restr_poly_vars) new_poly_vars in 
	(new_poly_vars @ !all_length_poly_vars,
         all_poly, all_interval_array,
         m @ (List.rev !length_map)) in

      let change_var_const (ind, const) = 
	let new_var = 
	  try
	    List.assoc ind all_map 
	  with
	  | Not_found ->
	     raise
               (JCH_failure 
		  (LBLOCK [ STR "Change var constant not found for " ; INT ind ;
			    STR " in JCHPolyIntervalArray.change_var_const" ])) in
	(new_var#getIndex, const) in
      
      {< var_to_const = List.map change_var_const var_to_const ;
	poly_vars = all_new_poly_vars;
	var_to_index = mk_var_to_index all_new_poly_vars ;
	poly = new_poly ;
	interval_array = new_interval_array;
	extra_infos = extra_infos#change_vars all_new_poly_vars
      >}

    method is_const v = 
      List.mem_assoc v#getIndex var_to_const

    method get_const_val (v: variable_t) = 
      try
	(List.assoc v#getIndex var_to_const)#getNum
      with
      | Not_found ->
	 raise
           (JCH_failure
	      (LBLOCK [ STR "Constant value not found for " ; v#toPretty ;
		        STR " in JCHPolyIntervalArray.get_const_val" ]))

    method get_const_val_n v =
      try
	List.assoc v#getIndex var_to_const
      with
      | Not_found ->
	 raise
           (JCH_failure
	      (LBLOCK [ STR "Constant value not found for " ; v#toPretty ; 
		        STR " in JCHPolyIntervalArray.get_const_val_n" ]))
        
    method get_index var = 
      try
	List.assoc var#getIndex var_to_index
      with
      | Not_found ->
	 raise
           (JCH_failure 
	      (LBLOCK [ STR "Variable index not found for " ;
		        var#toPretty ; STR " in JCHPolyIntervalArray.get_index" ]))
        
    method private put_index (var, vl) = 
      (self#get_index var, vl)

    method private is_discrete var = 
      self#is_const var || interval_array#is_discrete (self#get_index var) 

    method private get_related_constrs_inds
                     (constrs:linear_constraint_t list) inds = 
      let ind_to_constrs = new IntCollections.table_t in
      let add_constr constr = 
	let inds = constr#get_used_indices in
	let add ind = 
	  match ind_to_constrs#get ind with 
	  | Some set -> set#add constr
	  | _ -> ind_to_constrs#set
                   ind (ConstraintCollections.set_of_list [constr]) in
	List.iter add inds in
      List.iter add_constr constrs ;
      let related_constrs = ref [] in     
      let related_inds = new IntCollections.set_t in 
      let rec work inds = 
	match inds with 
	| ind :: rest_inds -> 
	    if related_inds#has ind then work rest_inds
	    else 
	      begin
		related_inds#add ind ;
		let ind_constrs = 
		  match ind_to_constrs#get ind with 
		  | Some set -> set
		  | _ -> new ConstraintCollections.set_t in
		let new_inds = new IntCollections.set_t in
		let add constr = 
		  if List.memq constr !related_constrs then () 
		  else 
		    begin
		      related_constrs := constr :: !related_constrs ;
		      let inds = constr#get_used_indices in
		      new_inds#addList inds 
		    end in
		ind_constrs#iter add ;
		new_inds#addList rest_inds ;
		work new_inds#toList
	      end
	| [] -> () in
      work inds ;
      (!related_constrs, related_inds)

    method private get_constrs_for_inds
                     (constrs: linear_constraint_t list) inds = 
      let ind_to_constrs = new IntCollections.table_t in
      let add_constr constr = 
	let inds = constr#get_used_indices in
	let add ind = 
	  match ind_to_constrs#get ind with 
	  | Some set -> set#add constr
	  | _ ->
             ind_to_constrs#set
               ind (ConstraintCollections.set_of_list [constr]) in
	List.iter add inds in
      List.iter add_constr constrs ;
      let constrs_for_inds = new ConstraintCollections.set_t in
      let inds_in_constrs = new IntCollections.set_t in
      let add_ind ind = 
	match ind_to_constrs#get ind with 
	| Some set -> 
	    let add_constr constr = 
	      constrs_for_inds#add constr ;
	      inds_in_constrs#addList constr#get_used_indices in
	    set#iter add_constr
	| _ -> () in
      List.iter add_ind inds;
      (constrs_for_inds#toList, inds_in_constrs)

    method private _get_best_interval' poly' interval_array' index =
      let int = interval_array'#get index in
      if poly'#is_top || int#isBottom || (Option.is_some int#singleton) then
        int
      else 
	begin
	  let constrs = poly'#get_constraints in
	  let (related_constrs, related_inds) = 
	    self#get_related_constrs_inds constrs [index] in
	  if related_constrs = [] then
            int 
	  else 
	    try
	      let related_poly =
		if related_constrs = [] then
                  top_poly
		else
                  mk_poly_from_constraints false related_constrs in
	      let constrs = ref [] in
	      let add_interval_constr index interval = 
		if related_inds#has index then 
		  if interval#isTop || interval#isBottom then
                    () 
		  else
                    constrs :=
                      (mk_constraints_from_interval false index interval) @ !constrs 
		else
                  ()  in 
	      interval_array'#iteri add_interval_constr ;
              
	      if !dbg then
                pr__debug [STR "_get_best_interval' big_poly has ";
                           INT (List.length !constrs); STR " constraints"; NL];
              
	      if List.length !constrs > 12 then int
	      else
		begin
		  let big_poly = related_poly#add_constraints !constrs in 
		  let big_poly_int = big_poly#get_interval index in
		  big_poly_int
		end
	    with (JCHAnalysisUtils.JCH_num_analysis_failure _) ->
	      int 
	end

    method private _get_best_interval poly' interval_array' index =
      let int = self#_get_best_interval' poly' interval_array' index in
      match params#check_time_limit with
      | 0 -> int
      | 1 ->
         begin
	   pr__debug [STR " Reached constraint analysis time limit "; NL] ;
	   params#reset_analysis_failure_status;
	   int
         end
      | _ ->
         begin
	  pr__debug [STR "Analysis failed: reached numeric analysis time limit "; NL] ;
	  raise (params#analysis_failed 3 "reached numeric analysis time limit ") 
         end
        
    method get_best_interval v_index =
      self#_get_best_interval poly interval_array v_index 

    method get_interval v = 
      let interval = 
	if self#is_const v then
          mkSingletonInterval (self#get_const_val_n v)
	else 
	  begin
	    let index = self#get_index v in
	    if List.exists (fun v' -> v#getIndex = v'#getIndex) poly_vars then 
	      self#get_best_interval index
	    else
              interval_array#get_type_interval index (* topInterval *)
	  end in
      interval

    method private get_best_interval_array apoly ainterval_array =
      let dim = self#get_dim in
      let best_array = interval_array#make_bottom_intervals dim in
      begin
        for i = 0 to pred dim do 
	  let interval = self#_get_best_interval apoly ainterval_array i in
	  best_array#set i interval 
        done ;
        best_array
      end

    method set_best_intervals = 
      {< interval_array = self#get_best_interval_array poly interval_array >}

    method move_simple_ineqs =
      
      if !dbg then pr__debug [STR "move_simple_ineqs "; NL; self#toPretty; NL];
      
      let (restr_poly, restr_interval_array) =
        move_simple_ineqs_to_intervals poly interval_array in
      {< poly = restr_poly; interval_array = restr_interval_array  >} 

    (* checks whether apoly + ainterval_array <= constr *)
    method private included_in_constr
                     apoly ainterval_array (constr: linear_constraint_t) = 
      let constr_poly = mk_poly_from_constraints false [constr] in
      
      if !dbg then
        pr__debug [STR "included_in_constr "; NL;
                   apoly#toPretty; NL; constr_poly#toPretty; NL] ;
      
      if apoly#leq constr_poly then true
      else 
	begin
	  let inds = constr#get_used_indices in
	  let aconstrs = apoly#get_constraints in
	  let (related_constrs, related_inds) =
            self#get_related_constrs_inds aconstrs inds in
	  let interval_constrs = ref [] in
	  let add_interval_constr ind = 
	    let interval = ainterval_array#get ind in
	    if interval#isTop then
              () 
	    else
              interval_constrs :=
                (mk_constraints_from_interval false ind interval) @ !interval_constrs in
	  related_inds#iter add_interval_constr ;
	  let new_poly =
            mk_poly_from_constraints false (related_constrs @ !interval_constrs) in
	  new_poly#leq constr_poly
	end

    method private are_excluded interval excluded_vals vals = 
      let is_excluded interval excluded_vals vl = 
	if interval#contains vl then
          List.exists (fun vl' -> vl'#equal vl) excluded_vals
	else
          true in
      List.for_all (is_excluded interval excluded_vals) vals

    (* This does not take into consideration the extra infos - 
     * other than excluded vals. Does it need to? *)
    method leq (a: 'a) =
      
      if !dbg then
        pr__debug [STR "JCHPolyIntervalArray.leq "; NL;
                   self#toPretty; NL; a#toPretty; NL] ;

      let res = 
        let best_interval_array =
          self#get_best_interval_array poly interval_array in (* Is this necessary ? *)
        let abest_interval_array =
          self#get_best_interval_array a#get_poly a#get_interval_array in (* Is this necessary ? *)
        
        if !dbg then
          pr__debug [STR "JCHPolyIntervalArray.leq after abest_interval_array"; NL] ;
      
        let rec check_constrs (constrs: linear_constraint_t list) =
	  match constrs with 
	  | constr :: rest_constrs -> 
	     if self#included_in_constr poly best_interval_array constr then 
	       check_constrs rest_constrs 
	     else
               false
	  | [] -> true in
        let rec check_intervals vars = 
	  match vars with 
	  | var :: rest_vars ->
	     let index = self#get_index var in
	     let int = best_interval_array#get index in
	     let aint = abest_interval_array#get index in
	     if int#leq aint then 
	       let excluded_vals = extra_infos#get_excluded_vals var in
	       let aexcluded_vals = a#get_extra_infos#get_excluded_vals var in 
	       if self#are_excluded int excluded_vals aexcluded_vals then
                 check_intervals rest_vars
	       else 
		 false 
	     else 
	       false
	  | [] -> 
	    let constrs = a#get_poly#get_constraints in
	    check_constrs constrs in
        check_intervals poly_vars in
      
      let _ = if !dbg then
                pr__debug [STR "JCHPolyIntervalArray.leq result = "; pp_bool res; NL] in
      res

    method equal (a: 'a) = 
      (self#leq a) && (a#leq self)

    (* vars are collection vars that are read arguments in a call
     * For these, we want the intervals to be the intervals in a, 
     * which are the exit intervals of the called method
     * However for the library functions there might not be any 
     * intervals in the case when the collections were not changed
     * and the excluded values also need to be the ones from a *) 
    method meet' (a: 'a) vars =
      
      if !dbg then
        pr__debug [STR "meet' "; pp_list vars; NL; self#toPretty; NL; a#toPretty; NL] ;
      
      let new_poly = poly#meet a#get_poly in
      let new_interval_array = interval_array#meet a#get_interval_array true in

      let ainterval_array = a#get_interval_array in
      let aextra_infos = a#get_extra_infos in

      let set_interval ex_infos v = 
	try (* ?? *)
	  let index = self#get_index v in
	  if aextra_infos#is_changed_sym_param v then 
	    new_interval_array#set index (ainterval_array#get index) 
	  else
            interval_array#set index (interval_array#get index) ;
	  match a#get_extra_infos#get_num_info_ind index with 
	  | Some num_info -> ex_infos#set_num_info v num_info 
	  | None -> ex_infos
	with _ -> ex_infos in
      let new_extra_infos = List.fold_left set_interval extra_infos vars in

      let add_excluded ex_infos var = 
	if List.exists (fun v -> var#getIndex = v#getIndex) vars then
	  ex_infos#set_excluded_vals var (aextra_infos#get_excluded_vals var)
	else 
	  begin
	    let new_excluded = new NumericalCollections.set_t in
	    let index = self#get_index var in
	    let meet_interval = new_interval_array#get index in
	    let add_excl_vals vl = 
	      if meet_interval#contains vl then 
		new_excluded#add vl in 
	    List.iter add_excl_vals (extra_infos#get_excluded_vals var) ;
	    List.iter add_excl_vals (aextra_infos#get_excluded_vals var) ;
	    if new_excluded#isEmpty then
              ex_infos
	    else
              ex_infos#set_excluded_vals var new_excluded#toList 
	  end in
      let new_extra_infos = List.fold_left add_excluded new_extra_infos poly_vars in

      let add_infos ex_infos var =
	let index = var#getIndex in
	if List.exists (fun v -> index = v#getIndex) vars then
          ex_infos
	else
	  match (ex_infos#get_num_info_ind index,
                 aextra_infos#get_num_info_ind index) with
	  | (_, None) -> ex_infos
	  | (None, Some anum_info) -> ex_infos#set_num_info var anum_info
	  | (Some num_info, Some anum_info) ->
             ex_infos#set_num_info var (num_info#meet anum_info) in
      let new_extra_infos = List.fold_left add_infos new_extra_infos poly_vars in
      {< poly = new_poly ; 
	interval_array = new_interval_array ;
	extra_infos = new_extra_infos >}  

    method meet (simple: bool) (a: 'a) =
      
      if !dbg then
        pr__debug [STR "JCHPolyIntervalArray.meet "; NL; self#toPretty; NL; a#toPretty; NL] ;
      
      let new_poly = if simple then poly#meet_simple a#get_poly else poly#meet a#get_poly in
      let new_interval_array = interval_array#meet a#get_interval_array false in

      let new_extra_infos = extra_infos#meet a#get_extra_infos in
      let add_excluded ex_info var = 
	let aextra_infos = a#get_extra_infos in
	let new_excluded = new NumericalCollections.set_t in
	let index = self#get_index var in
	let meet_interval = new_interval_array#get index in
	let add_excl_vals vl = 
	  if meet_interval#contains vl then 
	    new_excluded#add vl in 
	List.iter add_excl_vals (extra_infos#get_excluded_vals var) ;
	List.iter add_excl_vals (aextra_infos#get_excluded_vals var) ;
	if new_excluded#isEmpty then
          ex_info
	else
          ex_info#set_excluded_vals var new_excluded#toList in
      let new_extra_infos = List.fold_left add_excluded new_extra_infos poly_vars in

      {< poly = new_poly ; 
	interval_array = new_interval_array ;
	extra_infos = new_extra_infos >}  (* What about divisions and empty collections ? *)

    method private add_extra_join_ineqs
                     join_poly join_interval_array spoly apoly ainterval_array =
      
      let _ =
        if !dbg then
          pr__debug [NL; STR "add_extra_join_ineqs ";
                     join_poly#toPretty; NL; spoly#toPretty; NL;
                     apoly#toPretty; NL] in
      
      let constrs = spoly#get_constraints in
      let ineqs = List.filter (fun c -> not c#is_equality) constrs in
      let ineqs_to_include = ref [] in
      let add_ineq ineq = 
	if not (self#included_in_constr join_poly join_interval_array ineq)
           && self#included_in_constr apoly ainterval_array ineq
           && not ineq#is_0_geq_0 then 
	  ineqs_to_include := ineq :: !ineqs_to_include in
      List.iter add_ineq ineqs ;
      try
	join_poly#add_constraints !ineqs_to_include 
      with (JCHAnalysisUtils.JCH_num_analysis_failure _) -> 
	params#set_use_intervals true ;
	top_poly

    method private join_extra_infos
                     sinterval_array
                     ainterval_array
                     (sextra_infos: numeric_info_t)
                     (aextra_infos : numeric_info_t) =
      
      if !dbg then
        pr__debug [STR "join_extra_infos "; NL; sextra_infos#toPretty; NL;
                   aextra_infos#toPretty; NL] ;
      
      let jextra_infos = sextra_infos#join aextra_infos in
      let add_excluded (ex_infos: numeric_info_t) var = 
	let sexcluded_vals = sextra_infos#get_excluded_vals var in
	let aexcluded_vals = aextra_infos#get_excluded_vals var in
	let common_excluded_vals = 
	  List.filter (fun vl ->
              List.exists vl#equal aexcluded_vals) sexcluded_vals in
	let new_excluded_vals =
          NumericalCollections.set_of_list common_excluded_vals in
	let add_var int_array1 ex_infos1 ex_infos2 = 
	  let interval = int_array1#get (self#get_index var) in
	  let add vl =
            if not (interval#contains vl) then
              new_excluded_vals#add vl in
	  List.iter add (ex_infos2#get_excluded_vals var) in
	add_var sinterval_array sextra_infos aextra_infos ;
	add_var ainterval_array aextra_infos sextra_infos ;
	ex_infos#set_excluded_vals var new_excluded_vals#toList in
      List.fold_left add_excluded jextra_infos poly_vars 

    (* Used for stubs *)
    method simple_join (a: 'a) =
      
      if !dbg then
        pr__debug [STR "simple_join "; NL; self#toPretty; NL; a#toPretty; NL] ;

      let apoly = a#get_poly in
      let ainterval_array = a#get_interval_array in
      let new_extra_infos = 
	self#join_extra_infos interval_array ainterval_array 
	  extra_infos a#get_extra_infos in
      let dim = self#get_dim in
      let new_interval_array = interval_array#join' dim ainterval_array in

      let new_poly = poly#join apoly in

      let (restr_poly, restr_interval_array) =
        move_simple_ineqs_to_intervals new_poly new_interval_array in

      if params#use_intervals then 
	{< poly = top_poly ; 
	  interval_array = restr_interval_array ;
	  extra_infos = new_extra_infos >}
      else
	begin
	  let changed_poly = 
	    let restr_poly' =
              self#add_extra_join_ineqs
                restr_poly restr_interval_array poly apoly ainterval_array in
	    let restr_poly'' =
              self#add_extra_join_ineqs
                restr_poly' restr_interval_array apoly poly interval_array in
	    restr_poly'' in
	  {< poly = changed_poly ; 
	    interval_array = restr_interval_array ;
	    extra_infos = new_extra_infos >}
	end

    method private get_non_bottom_intervals (ainterval_array: interval_array_t) = 
      let pairs = ref [] in
      let add_var v = 
	let i = self#get_index v in
	let interval = ainterval_array#get i in
	if not interval#isBottom then pairs := (i, interval) :: !pairs in
      List.iter add_var poly_vars ;
      !pairs

    method join (a: 'a) =
      
      if !dbg then
        pr__debug [STR "PolyIntervalArray.join "; NL; self#toPretty; NL; a#toPretty; NL] ;
      
      let j = 
        let apoly = a#get_poly in 
        let ainterval_array = a#get_interval_array in
        let new_extra_infos = 
	  self#join_extra_infos interval_array interval_array 
	                        extra_infos a#get_extra_infos in
        let dim = self#get_dim in
        let new_interval_array = interval_array#join' dim ainterval_array in
        
        if params#use_intervals then 
	  {< poly = top_poly ; 
	     interval_array = new_interval_array ; 
	     extra_infos = new_extra_infos
          >}
        else
	  begin
	    try
	      let big_poly = 
	        let intervals = self#get_non_bottom_intervals interval_array in
	        List.fold_left (fun res (index, interval) ->
                    res#add_constrs_from_interval index interval)
                               (fst poly#restrict_number_vars) intervals in

	      let abig_poly = 
	        let aintervals = self#get_non_bottom_intervals ainterval_array in
	        List.fold_left (fun res (index, interval) ->
                    res#add_constrs_from_interval index interval)
                               (fst apoly#restrict_number_vars) aintervals in
              
	      let join_poly = big_poly#join abig_poly in 
              
	      let big_join_poly = 
	        let intervals = self#get_non_bottom_intervals new_interval_array in
	        List.fold_left (fun res (index, interval) ->
                    res#add_constrs_from_interval index interval) join_poly intervals in
              
	      let (small_poly, removed_constraints) = big_join_poly#restrict_number_vars in
              
	      let (restr_poly, restr_interval_array) =
                move_simple_ineqs_to_intervals small_poly new_interval_array in
              
	      {< poly = restr_poly;
	         interval_array = restr_interval_array ;
	         extra_infos = new_extra_infos
              >}
	    with
            | JCHAnalysisUtils.JCH_num_analysis_failure _ ->
	       params#set_use_intervals true ;
	       {< poly = top_poly ; 
		  interval_array = new_interval_array ; 
		  extra_infos = new_extra_infos
               >}
	  end in
      if !dbg then pr__debug [STR "JCHPolyIntervalArray.join res "; NL; j#toPretty; NL] ;
      j

    method private add_constrs_no_loop_counters_lengths (poly: poly_t) : poly_t = 
      let (restr_poly, _) = poly#restrict_number_vars in
      let (restr_poly, _) = restr_poly#restrict_number_constraints in
      let constrs = ConstraintCollections.set_of_list (restr_poly#get_constraints) in
      let is_loop_counter_or_length var = 
	JCHSystemUtils.is_loop_counter var
        || JCHSystemUtils.is_length var (* || not (List.mem var !local_vars) *) in
      let loop_counters_and_lengths = List.filter is_loop_counter_or_length poly_vars in
      let p = poly#project_out (List.map self#get_index loop_counters_and_lengths) in
      let (p, _) = p#restrict_number_vars in
      let (p, _) = p#restrict_number_constraints in
      constrs#addList p#get_constraints ;
      fst (mk_poly_from_constraints false constrs#toList)#restrict_number_vars

    method private get_inds_in_constrs (constrs: linear_constraint_t list) = 
      let inds = new IntCollections.set_t in
      let add_ind constr = inds#addList constr#get_used_indices in
      List.iter add_ind constrs;
      inds#toList

    method private add_constrs_with_fewer_vars (poly: poly_t) : poly_t =
      
      if !dbg then
        pr__debug [STR "add_constrs_no_loop_counters_lengths ";
                   poly#to_pretty poly_vars; NL] ;
      
      let constrs = poly#get_constraints in
      let inds_in_poly = self#get_inds_in_constrs constrs in
      let new_constrs = ConstraintCollections.set_of_list constrs in
      let add_proj ind = 
	let p = poly#project_out [ind] in
	let (p, _) = p#restrict_number_vars in
	new_constrs#addList p#get_constraints in
      List.iter add_proj inds_in_poly ;
      mk_poly_from_constraints false new_constrs#toList

    method join_with_old (a: 'a) (old_poly_int_array : 'a) =
      
      if !dbg then
        pr__debug [STR "PolyIntervalArray.join_with_old "; NL;
                   old_poly_int_array#toPretty; NL; self#toPretty; NL;
                   a#toPretty; NL] ;
      
      let apoly = a#get_poly in 
      let ainterval_array = a#get_interval_array in
      let new_extra_infos = 
	self#join_extra_infos interval_array interval_array 
	  extra_infos a#get_extra_infos in
      let dim = self#get_dim in
      let new_interval_array = interval_array#join' dim ainterval_array in  

      if params#use_intervals then 
	{< poly = top_poly ; 
	  interval_array = new_interval_array ; 
	  extra_infos = new_extra_infos >}
      else
	begin
	  try
	    let big_poly = 
	      let intervals = self#get_non_bottom_intervals interval_array in
	      let p = List.fold_left (fun res (index, interval) ->
                          res#add_constrs_from_interval index interval) poly intervals in
	      fst p#restrict_number_vars in

	    let abig_poly = 
	      let aintervals = self#get_non_bottom_intervals ainterval_array in
	      let ap = List.fold_left (fun res (index, interval) ->
                           res#add_constrs_from_interval index interval) apoly aintervals in
	      fst ap#restrict_number_vars in

	    let (join_poly, join_interval_array) =
              move_simple_ineqs_to_intervals (big_poly#join abig_poly) new_interval_array in

	    let big_join_poly = 
	      let intervals = self#get_non_bottom_intervals new_interval_array in
	      List.fold_left (fun res (index, interval) ->
                  res#add_constrs_from_interval index interval) join_poly intervals in

	    let (small_poly, removed_constraints) = 
	      if params#analysis_level <= 2 then 
		big_join_poly#restrict_number_vars 
	      else 
		let p = self#add_constrs_with_fewer_vars big_join_poly in
		p#restrict_number_vars in

	    let (small_poly, restr_interval_array) =
              move_simple_ineqs_to_intervals small_poly join_interval_array in
	    let (small_poly, _) = small_poly#restrict_number_constraints in

	    let new_poly = small_poly#meet old_poly_int_array#get_poly in
	    {< poly = new_poly;
	      interval_array = restr_interval_array ;
	      extra_infos = new_extra_infos >}
	    with JCHAnalysisUtils.JCH_num_analysis_failure _ -> 
	      params#set_use_intervals true ;
	      {< poly = top_poly ; 
		interval_array = new_interval_array ; 
		extra_infos = new_extra_infos >}
	end

    (* Used for recursive calls *)
    method simple_widening (a: 'a) =
      
      let _ =
        if !dbg then
          pr__debug [STR "JCHPolyIntervalArray.widening "; NL;
                     self#toPretty; NL; a#toPretty; NL] in
      
      let w = 
        let ainterval_array = a#get_interval_array in
        let new_extra_infos = 
	  self#join_extra_infos interval_array ainterval_array 
	                        extra_infos a#get_extra_infos in
        
        let new_interval_array = 
	  interval_array#widening' a#get_interval_array in
        
        if params#use_intervals then 
	  {< poly = top_poly ;
	     interval_array = new_interval_array ;
	     extra_infos = new_extra_infos
          >}
        else 
	  begin
	    let new_poly = poly#widening a#get_poly in 
	    {< poly = new_poly ;
	       interval_array =
                 self#get_best_interval_array new_poly new_interval_array ;
	       extra_infos = new_extra_infos >} 
	  end in
      
      if !dbg then
        pr__debug [STR "JCHPolyIntervalArray.widening res: "; w#toPretty; NL] ;
      w
         
    method widening (a: 'a) =
      
      let _ =
        if !dbg then
          pr__debug [STR "JCHPolyIntervalArray.widening "; NL; self#toPretty; NL; a#toPretty; NL] in
      
      let w = 
        let apoly = a#get_poly in 
        let ainterval_array = a#get_interval_array in
        
        let new_extra_infos = 
	  self#join_extra_infos interval_array ainterval_array 
	                        extra_infos a#get_extra_infos in
        
        let new_interval_array = 
	  interval_array#widening a#get_interval_array in
        
        if params#use_intervals then 
	  {< poly = top_poly ;
	     interval_array = new_interval_array ;
	     extra_infos = new_extra_infos >}
        else 
	  begin
	    let big_poly = 
	      let intervals = self#get_non_bottom_intervals interval_array in
	      List.fold_left (fun res (index, interval) ->
                  res#add_constrs_from_interval
                    index interval) (fst poly#restrict_number_vars) intervals in
            
	    let (small_poly, _) = big_poly#restrict_number_vars in
	    let (small_poly, _) = small_poly#restrict_number_constraints in
            
	    let abig_poly = 
	      let aintervals = self#get_non_bottom_intervals ainterval_array in
	      List.fold_left (fun res (index, interval) ->
                  res#add_constrs_from_interval
                    index interval) (fst apoly#restrict_number_vars) aintervals in
            
	    let (asmall_poly, _) = abig_poly#restrict_number_vars in
	    let (asmall_poly, _) = asmall_poly#restrict_number_constraints in
            
	    let join_poly = small_poly#join asmall_poly in
	    
	    let new_poly = 
	    if params#analysis_level <= 2 then
	      begin
		let sp = self#add_constrs_no_loop_counters_lengths small_poly in
		let jp = self#add_constrs_no_loop_counters_lengths join_poly in
		sp#widening jp 
	      end
	    else 
	      begin
		let sp = self#add_constrs_with_fewer_vars small_poly in
		let jp = self#add_constrs_with_fewer_vars join_poly in
		let sp = self#add_constrs_no_loop_counters_lengths sp in
		let jp = self#add_constrs_no_loop_counters_lengths jp in
		sp#widening jp 
	      end in

	    let (restr_poly, _) =
              move_simple_ineqs_to_intervals new_poly new_interval_array in 

	    {< poly = restr_poly ;
	       interval_array = new_interval_array;
	       extra_infos = new_extra_infos
            >} 
	  end in
      if !dbg then
        pr__debug [STR "JCHPolyIntervalArray.widening res: "; w#toPretty; NL] ;
      w

    method private project_out_in_interval_array interval_array vs = 
      interval_array#project_out (List.map self#get_index vs) 

    method remove vs = 
      {< interval_array = interval_array#remove (List.map self#get_index vs) >}

    method private add_intervals_to_poly' p array vs = 
      let constrs = ref [] in
      let add_constr v =
	let index = self#get_index v in
	let interval = array#get index in
	if interval#isTop || interval#isBottom then
          () 
	else 
	  let cs = mk_constraints_from_interval true index interval in
	  constrs := cs @ !constrs in
      List.iter add_constr vs ;
      if !constrs = [] then p
      else p#add_constraints !constrs

    method add_intervals_to_poly =
      let new_poly = self#add_intervals_to_poly' poly interval_array poly_vars in
      {< poly = new_poly >}

    method project_out vs =  
      let new_extra_infos = 
	let remove_var new_extra_infos v = 
	  let int = self#get_interval v in
	  new_extra_infos#remove_var v int in
	List.fold_left remove_var extra_infos vs in
      if params#use_intervals then 
	{< poly = top_poly ; 
	  interval_array = self#project_out_in_interval_array interval_array vs ;
	  extra_infos = new_extra_infos >}
      else if poly#is_top then 
	begin
	  let new_interval_array =
            self#project_out_in_interval_array interval_array vs in
	  {< poly = top_poly ;
	    interval_array = new_interval_array; 
	    extra_infos = new_extra_infos
          >}
	end
      else
	begin
	  let constrs = poly#get_constraints in
	  let inds = List.map self#get_index vs in
	  let (related_constrs, related_inds) =
            self#get_constrs_for_inds constrs inds in
	  let unrelated_constrs =
            List.filter (fun c -> not (List.mem c related_constrs)) constrs in
	  let related_vs = ref [] in
	  let add_var v = 
	    if related_inds#has (self#get_index v) then
              related_vs := v :: !related_vs 
	    else () in
	  List.iter add_var poly_vars ;
	  let related_poly = mk_poly_from_constraints false related_constrs in
	  let big_related_poly = 
	    self#add_intervals_to_poly' related_poly interval_array !related_vs in 
	  let restr_poly = big_related_poly#project_out inds in
	  let (restr_poly, new_interval_array) =
            move_simple_ineqs_to_intervals restr_poly interval_array in
	  let new_interval_array =
            self#project_out_in_interval_array new_interval_array vs in
	  {< poly = restr_poly#add_constraints unrelated_constrs; 
	    interval_array = new_interval_array; 
	    extra_infos = new_extra_infos
          >}
	end

    method project_out_array v = 
      {< interval_array = self#project_out_in_interval_array interval_array [v] ;
	 extra_infos = extra_infos#remove_all_excluded v >}


    (* is_geq is true if var >= const is to be added
     * is_geq is false if var <= const is to be added *)
    method add_ineq is_geq var const = 
      let const_num = new numerical_t const in 
      let index = self#get_index var in
      let interval = 
	let int = interval_array#get index in
	if int#isBottom then
          interval_array#get_type_interval index (* topInterval *)
	else
          int in
      let ineq_interval = 
	if is_geq then
          new interval_t (bound_of_num const_num) (new bound_t PLUS_INF) 
	else
          new interval_t
              (new bound_t CHBounds.MINUS_INF) (bound_of_num const_num) in
      if interval#leq ineq_interval then
        {< >}
      else 
	begin
	  let new_interval = interval#meet ineq_interval in
	  if new_interval#isBottom then
            self#mk_bottom
	  else 
	    begin
	      let new_interval_array = interval_array#copy_set index new_interval in
	      let new_extra_infos = 
		extra_infos#remove_out_of_interval_excluded var new_interval in 
	      let new_poly_int = 
		if params#use_intervals then 
		  {< poly = top_poly ;
		     interval_array = new_interval_array ;
		     extra_infos = new_extra_infos >}
		else if params#max_number_constraints_allowed <= 10 then 
		  {< interval_array = new_interval_array;
		     extra_infos = new_extra_infos >} 
		else
		  {< interval_array = self#get_best_interval_array poly new_interval_array;
		     extra_infos = new_extra_infos >} in
	      new_poly_int
	    end
	end

    val neg_unit_big_int = minus_big_int unit_big_int

    method private assert_greater is_strict_ineq x y =
      
      if !dbg then
        pr__debug [STR "assert_greater "; x#toPretty; STR " ";
                   y#toPretty; NL; self#toPretty] ;

      let res = 
        let x_index = self#get_index x in
        let x_int = self#get_best_interval x_index in
        let y_int = 
	  if self#is_const y then mkSingletonInterval (self#get_const_val_n y)
	  else self#get_best_interval (self#get_index y) in
        let excluded_vals_x = NumericalCollections.set_of_list (extra_infos#get_excluded_vals x) in
        let excluded_vals_y = NumericalCollections.set_of_list (extra_infos#get_excluded_vals y) in
        let x_int' = 
	  let ymin = y_int#getMin in
	  if is_strict_ineq then 
	    begin
	      if self#is_discrete x then 
	        x_int#strictLowerBound ymin
	      else 
	        begin
		  (match ymin#getBound with 
		   | NUMBER num -> excluded_vals_x#add num 
		   | _ -> () ) ;
		  x_int#lowerBound ymin
	        end
	    end
	  else 
	    begin
	      (if not (self#is_discrete x) then 
	         match ymin#getBound with 
	         | NUMBER num -> 
		    if excluded_vals_y#has num then excluded_vals_x#add num
	         |	_ -> ()) ;
	      x_int#lowerBound ymin 
	    end in
        let y_int' = 
	  let xmax = x_int#getMax in
	  if is_strict_ineq then 
	    begin
	      if self#is_discrete y then 
	        y_int#strictUpperBound xmax 
	      else 
	        begin
		  (match xmax#getBound with 
		   | NUMBER num -> excluded_vals_y#add num 
		   | _ -> () ) ;
		  y_int#upperBound xmax
	        end
	    end
	  else 
	    begin
	      (if not (self#is_discrete y) then 
	         match xmax#getBound with 
	         | NUMBER num -> 
		    if excluded_vals_x#has num then excluded_vals_y#add num
	         |	_ -> ()) ;
	      y_int#upperBound xmax 
	    end in
        if x_int'#isBottom || y_int'#isBottom then self#mk_bottom 
        else 
	  begin
	    let new_interval_array = interval_array#copy in
	    new_interval_array#set x_index x_int' ;
	    if self#is_const y then () 
	    else new_interval_array#set (self#get_index y) y_int' ;
	    let new_extra_infos = extra_infos#set_excluded_vals x excluded_vals_x#toList in
	    let new_extra_infos = new_extra_infos#remove_out_of_interval_excluded x x_int' in
	    let new_extra_infos = new_extra_infos#set_excluded_vals y excluded_vals_y#toList in
	    let new_extra_infos = new_extra_infos#remove_out_of_interval_excluded y y_int' in
	    if params#use_intervals then 
	      let new_poly = 
	        {< poly = top_poly; 
		   interval_array = new_interval_array ;
		   extra_infos = new_extra_infos
                >} in
	      new_poly
	    else 
	      begin
	        let const = if is_strict_ineq then neg_unit_big_int else zero_big_int in
	        let new_poly = 
		  let pairs = [(x, unit_big_int); (y, neg_unit_big_int)] in
		  let pairs' = List.map self#put_index pairs in
		  let constr = new linear_constraint_t false pairs' const in
		  poly#add_constraints [constr] in
	        if new_poly#is_bottom then
                  self#mk_bottom 
	        else 
		  {< poly = new_poly; 
		     interval_array = self#get_best_interval_array new_poly new_interval_array ; 
		     extra_infos = new_extra_infos >} 
	      end
	  end in
      
      if !dbg then
        pr__debug [STR "assert_greater res = "; NL; res#toPretty; NL] ;
      res 
         
         
    method assert_geq x y =
      
      if !dbg then
        pr__debug [STR "assert_geq "; x#toPretty; STR " "; y#toPretty; NL] ;
      
      let res = 
        if self#is_const x then 
	  if self#is_const y then
	    if ge_big_int (self#get_const_val x) (self#get_const_val y) then
              {< >}
	    else
              self#mk_bottom 
	  else
            self#add_ineq false y (self#get_const_val x) 
        else if self#is_const y then
          self#add_ineq true x (self#get_const_val y) 
        else
          self#assert_greater false x y in
      
      if !dbg then
        pr__debug [STR "assert_geq res = "; NL; res#toPretty; NL] ;
      res


    method assert_gt x y =
      
      if !dbg then
        pr__debug [STR "assert_gt "; x#toPretty; STR " "; y#toPretty; NL;
                   self#toPretty; NL] ;

      let res = 
        if self#is_discrete x then 
	  if self#is_const x then 
	    if self#is_const y then
	      if gt_big_int (self#get_const_val x) (self#get_const_val y) then {< >}
	      else self#mk_bottom 
	    else 
	      begin
	        let const = sub_big_int (self#get_const_val x) unit_big_int in
	        self#add_ineq false y const 
	      end
	  else if self#is_const y then 
	    begin
	      let const = add_big_int (self#get_const_val y) unit_big_int in
	      self#add_ineq true x const 
	    end
	  else self#assert_greater true x y 
        else 
	  if self#is_const y then 
	    begin
	      let const = add_big_int (self#get_const_val y) unit_big_int in
	      self#add_ineq true x const 
	    end
	  else 
	    self#assert_greater true x y in
      
      if !dbg then
        pr__debug [STR "assert_gt res = "; NL; res#toPretty; NL] ;
      res


    method assert_neq x y =
      
      if !dbg then
        pr__debug [STR "assert_neq "; x#toPretty; STR " "; y#toPretty; NL] ;

      let res = 
        let x_i = 
	  if self#is_const x then
	    mkSingletonInterval (self#get_const_val_n x) 
	  else 
	    let x_index = self#get_index x in
	    self#get_best_interval x_index in
        let y_i = 
	  if self#is_const y then 
	    mkSingletonInterval (self#get_const_val_n y) 
	  else 
	    let y_index = self#get_index y in
	    self#get_best_interval y_index in
        match (x_i#singleton, y_i#singleton) with
        | (Some x_c, Some y_c) ->
	   if x_c#equal y_c then self#mk_bottom
	   else {< >}
        | (Some x_c, _) ->
	   begin
	     match y_i#getMax#getBound  with
	     | NUMBER max when max#equal x_c -> self#assert_gt x y
	     | NUMBER max when max#lt x_c -> {< >} 
	     | _ ->
		begin
		  match y_i#getMin#getBound with
		  | NUMBER min when min#equal x_c -> self#assert_gt y x
		  | NUMBER min when min#gt x_c -> {< >} 
		  | _ -> 
		     let new_extra_infos = extra_infos#add_excluded_val y x_c in
		     {< extra_infos = new_extra_infos >}
		end
	   end
        | (_, Some y_c) ->
	   begin
	     match x_i#getMax#getBound with
	     | NUMBER max when max#equal y_c -> self#assert_gt y x
	     | NUMBER max when max#lt y_c -> {< >} 
	     | _ ->
		begin
		  match x_i#getMin#getBound with
		  | NUMBER min when min#equal y_c -> self#assert_gt x y 
		  | NUMBER min when min#gt y_c -> {< >}
		  | _ -> 
		     let new_extra_infos = extra_infos#add_excluded_val x y_c in
		     {< extra_infos = new_extra_infos >}
		end
	   end
        | _ -> {< >} in

      if !dbg then
        pr__debug [STR "assert_neq res = "; NL; res#toPretty; NL] ;
      res
         

    method private affine_image_i vpair pairs const =
      
      if !dbg then
        pr__debug [STR "affine_image_i "; NL] ;
      
      let (var, den) = vpair in
      let rhs = ref (mkSingletonInterval (new numerical_t const)) in
      let add_pair (v, i) =
	let coeff = mkSingletonInterval (new numerical_t i) in
	let index = self#get_index v in
	let interval = interval_array#get index in
	rhs := !rhs#add (interval#mult coeff) in
      List.iter add_pair pairs ;
      let den = mkSingletonInterval (new numerical_t den) in
      let interval = !rhs#div den in
      interval

    (* Computes the image of the transformation coeff * var = sum of a * v + const
     * where vpair = (var, coeff) and pairs is a list of (v, a)
     * In case an equality (equality = Some w) is processed then the extra 
     * infos are copied *)
    method affine_image
             (equality:variable_t option)
             (vpair:variable_t * big_int)
             (pairs:(variable_t * big_int) list)
             (const:big_int):('a * variable_t option * variable_t option) = 
      let var = fst vpair in
      let (index, coeff) = self#put_index vpair in
      let old_interval = interval_array#get index in
      let new_interval_array = interval_array#copy in
      let interval = self#affine_image_i vpair pairs const in
      let (min_ok, max_ok) = 
	if params#use_overflow then 
	  begin
	    let tinterval = interval_array#get_type_interval index in
	    let max_ok = tinterval#getMax#geq interval#getMax in
	    let min_ok = tinterval#getMin#leq interval#getMin in
	    (min_ok, max_ok) 
	  end
	else (true, true) in
      if min_ok && max_ok then 
	begin
	  let interval = 
	    if params#use_overflow then
              interval
	    else
              interval#meet (interval_array#get_type_interval index) in
	  new_interval_array#set index interval ;
	  let new_poly = 
	    if params#use_intervals then
              top_poly 
	    else if Option.is_some interval#singleton then 
	      poly#project_out [index]
	    else 
	      let pairs' = List.map self#put_index pairs in 
	      poly#affine_image index coeff pairs' const old_interval in
	  let (restr_poly, restr_interval_array) =
            move_simple_ineqs_to_intervals new_poly new_interval_array in
	  let (restr_poly, _) = restr_poly#restrict_number_constraints in
	  let best_interval_array =
            self#get_best_interval_array restr_poly restr_interval_array in
	  let new_extra_infos = 
	    let ei = 
	      match equality with 
	      | Some w -> 
		  extra_infos#set_same_info var w
	      | _ -> extra_infos in
	    ei#remove_out_of_interval_excluded var interval in
	  ({< poly = restr_poly; 
	    interval_array = best_interval_array ;
	    extra_infos = new_extra_infos
           >}, None, None)
	end
      else 
	(self#project_out [var] ,
	 (if max_ok then None else Some var) ,
	 (if min_ok then None else Some var) ) 


    (* Computes the image of the transformation v = coeff * w + const or v = const *)
    method affine_subst
             (v:variable_t)
             (w_opt:variable_t option)
             (coeff:big_int)
             (const: big_int):('a * variable_t option * variable_t option) = 
      let v_index = self#get_index v in
      let v_interval = interval_array#get v_index in
      let new_interval_array = interval_array#copy in
      match w_opt with 
      |	Some w -> 
	  begin
	    let w_index = self#get_index w in
	    let w_interval = interval_array#get w_index in
	    let new_v_interval =
              (w_interval#mult
                 (mkSingletonInterval
                    (new numerical_t coeff)))#add
                                             (mkSingletonInterval (new numerical_t const)) in
	    let (min_ok, max_ok) = 
	      if params#use_overflow then 
		begin
		  let v_tinterval = interval_array#get_type_interval v_index in
		  let max_ok = v_tinterval#getMax#geq new_v_interval#getMax in
		  let min_ok = v_tinterval#getMin#leq new_v_interval#getMin in
		  (min_ok, max_ok) 
		end 
	      else (true, true) in
	    if min_ok && max_ok then 
	      begin
		let new_v_interval = 
		  if params#use_overflow then
                    new_v_interval
		  else
                    new_v_interval#meet (interval_array#get_type_interval v_index) in
		new_interval_array#set v_index new_v_interval ;
		let new_poly = 
		  if params#use_intervals then
                    top_poly
		  else 
		    begin
		      let proj_poly =
			if List.exists (fun c -> c#has_index v_index) poly#get_constraints then 
			  (self#project_out [v])#get_poly 
			else
                          poly in
		      if Option.is_some new_v_interval#singleton then
                        proj_poly
		      else 
			let neg_coeff = minus_big_int coeff in
			let constr =
                          new linear_constraint_t
                              true
                              [(v_index, unit_big_int); (w_index, neg_coeff)]
                              (minus_big_int const) in
			proj_poly#add_constraints [constr] 
		    end in
		let new_extra_infos = 
		  let ei = 
		    if eq_big_int const zero_big_int then 
		      extra_infos#set_same_info v w
		    else
                      extra_infos in
		  ei#remove_out_of_interval_excluded v new_v_interval in
		({< poly = new_poly; 
		   interval_array = new_interval_array ;
		   extra_infos = new_extra_infos
                 >}, None, None)
	      end
	    else
	      begin
		let new_poly_int_array = self#project_out [v] in
		let new_poly_int_array = 
		  if eq_big_int const zero_big_int && eq_big_int coeff unit_big_int then
		    new_poly_int_array#copy_num_info v w 
		  else
                    new_poly_int_array in
	      (new_poly_int_array,
	       (if max_ok then None else Some v) ,
	       (if min_ok then None else Some v) )
	      end
	  end
      |	_ -> 
	  begin
	    let new_v_interval = mkSingletonInterval (new numerical_t const) in
	    let (min_ok, max_ok) = 
	      if params#use_overflow then
		begin
		  let v_tinterval = interval_array#get_type_interval v_index in
		  let max_ok = v_tinterval#getMax#geq new_v_interval#getMax in
		  let min_ok = v_tinterval#getMin#leq new_v_interval#getMin in
		  (min_ok, max_ok) 
		end 
	      else (true, true) in
	    if min_ok && max_ok then 
	      begin
		new_interval_array#set v_index new_v_interval ;
		let big_poly =
                  poly#add_constraints (mk_constraints_from_interval true v_index v_interval) in
		let proj_poly = big_poly#project_out [v_index] in
		({<poly = proj_poly ;
		   interval_array = new_interval_array
                 >},  None, None)
	      end
	    else 
	      (self#project_out [v] ,
	       (if max_ok then None else Some v) ,
	       (if min_ok then None else Some v) ) 
	  end

    (* Computes the image of the transformation v = v + const *)
    method affine_increment
             (var:variable_t)
             (const:big_int):('a * variable_t option * variable_t option) = 
      let index = self#get_index var in
      let interval = interval_array#get index in
      let new_interval_array = interval_array#copy in
      let new_interval = interval#add (mkSingletonInterval (new numerical_t const)) in
      let (min_ok, max_ok) = 
	if params#use_overflow then
	  begin
	    let tinterval = interval_array#get_type_interval index in
	    let max_ok = tinterval#getMax#geq new_interval#getMax in
	    let min_ok = tinterval#getMin#leq new_interval#getMin in
	    (min_ok, max_ok) 
	  end
	else (true, true) in
      if min_ok && max_ok then 
	begin
	  let new_interval = 
	    if params#use_overflow then
              new_interval
	    else
              new_interval#meet (interval_array#get_type_interval index) in
	  new_interval_array#set index new_interval ;
	  let new_poly = 
	    if params#use_intervals then
              top_poly 
	    else if Option.is_some new_interval#singleton then 
	      poly#project_out [index]
	    else 
	      poly#affine_increment index const in
	  ({< poly = new_poly; 
	    interval_array = new_interval_array >},
	   None, None)
	end
      else 
	(self#project_out [var] ,
	 (if max_ok then None else Some var) ,
	 (if min_ok then None else Some var) ) 


    method affine_preimage
             (vpair:variable_t * big_int)
             (pairs:(variable_t * big_int) list)
             (const:big_int):'a = 
      let (col, coeff) = self#put_index vpair in
      let pairs' = List.map self#put_index pairs in 
      let var = fst vpair in
      let new_interval_array =
        self#project_out_in_interval_array interval_array [var] in
      let new_extra_infos = 
	let int = self#get_interval var in
	extra_infos#remove_var var int in
      if params#use_intervals then 
	{< poly = top_poly; 
	  interval_array = new_interval_array ;
	  extra_infos = new_extra_infos >}
      else 
	{< poly = poly#affine_preimage col coeff pairs' const ;
	  interval_array = new_interval_array;
	  extra_infos = new_extra_infos >}

    method add_vars
             (jproc_info:JCHProcInfo.jproc_info_t)
             (other_vars: variable_t list):'a =
      
      let _ =
        if !dbg then
          pr__debug [STR "add_vars "; pp_list other_vars; NL;
                     self#toPretty; NL] in

      let res = 
        if self#is_bottom then
          {< >} 
        else 
	  begin
	    let is_new var = not (self#is_const var) && not (List.mem var poly_vars) in
	    let vars_to_add = List.filter is_new other_vars in
	    if vars_to_add = [] then
              {< >}
	    else 
	      begin
	        let new_vars = poly_vars @ vars_to_add in
	        let new_dim = List.length new_vars in
	        let new_var_to_index = mk_var_to_index new_vars in
	        let new_interval_array =
                  interval_array#augment self#get_dim new_dim bottomInterval in
	        let new_interval_array =
                  new_interval_array#set_type_intervals jproc_info new_vars in
	        {< poly_vars = new_vars;
		   var_to_index = new_var_to_index ;
		   interval_array = new_interval_array
                >}
	      end
	  end in
      let _ =
        if !dbg then
          pr__debug [STR "after add_vars, res = "; NL; res#toPretty; NL] in
      res 

    method mult
             (v:variable_t)
             (x:variable_t)
             (y:variable_t):('a * variable_t option * variable_t option * bool) = 
      let new_interval_array = interval_array#copy in
      let x_int = 
	let index = (self#get_index x) in
	let int = self#get_best_interval index in
        begin
	  new_interval_array#set index int ;
	  int
        end in
      let y_int = 
	let index = (self#get_index y) in
	let int = self#get_best_interval index in
        begin
	  new_interval_array#set index int ;
	  int
        end in
      let mult_int = 
	if x = y then 
	  let x_min = x_int#getMin in
	  let x_max = x_int#getMax in
	  let max = (x_min#mult x_min)#max (x_max#mult x_max) in
	  new interval_t zero_bound max 
	else
          x_int#mult y_int in
      let v_ind = self#get_index v in 
      let x_ind = self#get_index x in
      let y_ind = self#get_index y in
      new_interval_array#set v_ind mult_int ;
      
      let v_int =  
	if params#use_intervals then
          mult_int 
	else 
	  let divisions = extra_infos#get_divisions y in
	  if divisions = [] then
            mult_int 
	  else 
	    begin
	      let process_division p (dividend, quotient) = 
		try  (* ?? *)
		  let quot_ind = self#get_index quotient in 
		  let (dividend_ind_opt, const_opt) = 
		    if self#is_const dividend then 
		      (None, Some (self#get_const_val dividend))
		    else
                      (Some (self#get_index dividend), None) in
		  if zero_bound#leq y_int#getMin then 
		    p#add_mult_constr
                      v_ind x_ind quot_ind dividend_ind_opt const_opt true 
		  else if y_int#getMax#leq zero_bound then 
		    p#add_mult_constr
                      v_ind x_ind y_ind dividend_ind_opt const_opt false 
		  else p 
		with _ -> p in
	      let poly' = List.fold_left process_division poly divisions in
	      let interval = self#_get_best_interval poly' new_interval_array v_ind in
	      interval#meet mult_int 
	    end in
      let v_index = self#get_index v in
      let new_poly = poly#project_out [v_index] in
      let tinterval = interval_array#get_type_interval v_ind in
      let (min_ok, max_ok) = 
	if params#use_overflow then
	  (tinterval#getMin#leq v_int#getMin, tinterval#getMax#geq v_int#getMax) 
	else
          (true, true) in
      let interval = v_int#meet tinterval in
      new_interval_array#set v_index interval ;
      let overflow = if max_ok then None else Some v in
      let underflow = if min_ok then None else Some v in
      let v_lost_info =
        poly#is_used_ind x_ind
        || poly#is_used_ind y_ind
        || extra_infos#has_fields x
        || extra_infos#has_fields y in
      ({< poly = new_poly; 
	  interval_array = new_interval_array >}, 
       overflow, underflow, v_lost_info)

    method private is_not_excluded v c = 
      let excluded_vals = extra_infos#get_excluded_vals v in
      not (List.exists c#equal excluded_vals)

    method private _can_be_0 y y_int = 
      y_int#contains numerical_zero && self#is_not_excluded y numerical_zero ;

    method can_be_0 y = 
      if self#is_const y then 
	(self#get_const_val_n y)#equal numerical_zero
      else 
	let int = self#get_best_interval (self#get_index y) in 
	int#contains numerical_zero && self#is_not_excluded y numerical_zero

    method div
             (is_float:bool)
             (v:variable_t)
             (x:variable_t)
             (y:variable_t):'a * variable_t option * variable_t option * variable_t option =
      
      if !dbg then
        pr__debug [STR "div "; v#toPretty; STR " "; x#toPretty; STR " ";
                   y#toPretty; NL; self#toPretty; NL] ;

      let new_interval_array = interval_array#copy in
      let x_int = 
	if self#is_const x then mkSingletonInterval (self#get_const_val_n x) 
	else 
	  let index = (self#get_index x) in
	  let int = self#get_best_interval index in
          begin
	    new_interval_array#set index int ;
	    int
          end in
      let y_int = (* not constant *)
	if self#is_const y then
          mkSingletonInterval (self#get_const_val_n y) 
	else 
	  let index = (self#get_index y) in
	  let int = self#get_best_interval index in
          begin
	    new_interval_array#set index int ;
	    int 
	  end in
      let v_int = JCHAnalysisUtils.integer_div x_int y_int in
      let divided_by_0 =
	if self#_can_be_0 y y_int then 
	  if is_float then
            None
	  else
            Some v
	else
          None in
      let v_index = self#get_index v in
      let new_poly = poly#project_out [v_index] in
      let tinterval = interval_array#get_type_interval v_index in
      let interval = v_int#meet tinterval in
      new_interval_array#set v_index interval ;
      
      let overflow = 
	if params#use_overflow then 
	  if y_int#contains numerical_one#neg 
	     && x_int#getMin#leq tinterval#getMin then
            Some v 
	  else
            None 
	else
          None in
      let new_poly_int_array = 
	if not is_float && Option.is_some divided_by_0 then 
	  begin
	    if Option.is_some y_int#singleton then
              self#mk_bottom 
	    else if self#is_const y then 
	      {< poly = new_poly; interval_array = new_interval_array >}
	    else
	      let min = y_int#getMin in
	      let max = y_int#getMax in
	      if min#equal zero_bound then 
		let new_y_int = new interval_t one_bound max in
                begin
		  new_interval_array#set (self#get_index y) new_y_int ;
		  {< poly = new_poly; interval_array = new_interval_array >}
                end
	      else if max#equal zero_bound then 
		let new_y_int = new interval_t min (max#sub one_bound) in
                begin
		  new_interval_array#set (self#get_index y) new_y_int ;
		  {< poly = new_poly; interval_array = new_interval_array >}
                end
	      else 
		let new_extra_infos = extra_infos#add_excluded_val y numerical_zero in
                begin
		  {< poly = new_poly;
                     interval_array = new_interval_array ;
                     extra_infos = new_extra_infos >}
		end
	  end
	else
          {< poly = new_poly; interval_array = new_interval_array >} in 
      (new_poly_int_array, divided_by_0, overflow, None)

    method rem (is_float:bool) (v:variable_t) (x:variable_t) (y:variable_t) =
      
      if !dbg then
        pr__debug [STR "rem "; v#toPretty; STR " "; y#toPretty; NL] ;
      
      let y_int = 
	if self#is_const y then
          mkSingletonInterval (self#get_const_val_n y)
	else
          self#get_best_interval (self#get_index y) in
      match y_int#singleton with 
      | Some n -> 
	 if n#equal numerical_zero then (* y = 0 *)
	   if is_float then (self#project_out [v], None) 
	   else
             (self#mk_bottom, Some y)
	 else if n#gt numerical_zero then  (* y > 0 *)
	   begin
	     if self#is_const x then
	       begin
		 let num = self#get_const_val_n x in
		 let is_x_pos = num#geq numerical_zero in
		 if is_x_pos then 
		   let (pia, _, _) = self#affine_image None (v, unit_big_int) [] num#getNum in
		   (pia, None) 
		 else (self#project_out [v], None) 
	       end
	     else
	       begin
		 let is_x_pos = self#leq (self#drop_all#add_ineq true x zero_big_int) in
		 if is_x_pos then 
		   let (pia, _, _) =
                     self#affine_image
                       None (v, unit_big_int) [(x, unit_big_int)] zero_big_int in
		   (pia, None) 
		 else (self#project_out [v], None) 
	       end
	   end
	 else (* y < 0 *)
	   begin
	     if self#is_const x then
	       begin
		 let num = self#get_const_val_n x in
		 let is_x_neg = num#leq numerical_zero in
		 if is_x_neg then 
		   let (pia, _, _) = self#affine_image None (v, unit_big_int) [] num#getNum in
		   (pia, None) 
		 else (self#project_out [v], None) 
                 
	       end
	     else
	       begin
		 let is_x_neg = self#leq (self#drop_all#add_ineq false x zero_big_int) in
		 if is_x_neg then 
		   let (pia, _, _) =
                     self#affine_image None (v, unit_big_int) [(x, unit_big_int)] zero_big_int in
		   (pia, None) 
		 else (self#project_out [v], None) 
	       end
	   end
      | _ -> 
	 if self#_can_be_0 y y_int then 
	   if is_float then
             (self#project_out [v], None) 
	   else 
	     begin
	       let v_index = self#get_index v in
	       let new_interval_array = interval_array#project_out [v_index] in
	       let new_poly = poly#project_out [v_index] in
	       let min = y_int#getMin in
	       let max = y_int#getMax in
	       if min#equal zero_bound then 
		 let new_y_int = new interval_t one_bound max in
		 new_interval_array#set (self#get_index y) new_y_int ;
		 let new_poly_interval_array =
                   {< poly = new_poly; interval_array = new_interval_array >} in
		 (new_poly_interval_array, Some y) 
	       else if max#equal zero_bound then 
		 let new_y_int = new interval_t min (max#sub one_bound) in
		 new_interval_array#set (self#get_index y) new_y_int ;
		 let new_poly_interval_array =
                   {< poly = new_poly; interval_array = new_interval_array >} in
		 (new_poly_interval_array, Some y)
	       else 
		 let new_extra_infos = extra_infos#add_excluded_val y numerical_zero in
		 let new_poly_interval_array =
                   {< poly = new_poly;
                      interval_array = new_interval_array ;
                      extra_infos = new_extra_infos >} in
		 (new_poly_interval_array, Some y)
	     end
	 else 
	   if y_int#getMin#geq zero_bound then (*  y >= 0 *) 
	     begin
	       if self#is_const x then
		 begin
		   let num = self#get_const_val_n x in
		   let is_x_pos = num#geq numerical_zero in
		   if is_x_pos then 
		     let (pia, _, _) =
                       self#affine_image None (v, unit_big_int) [] num#getNum in
		     (pia, None) 
		   else (self#project_out [v], None) 
		 end
	       else
		 begin
		   let is_x_pos = self#leq (self#drop_all#add_ineq true x zero_big_int) in
		   if is_x_pos then (* x >= 0 *) 
		     let (pia, _, _) =
                       self#affine_image None (v, unit_big_int) [(x, unit_big_int)] zero_big_int in
		     (pia, None) 
		   else (self#project_out [v], None) 
		 end
	     end
	   else if y_int#getMax#leq zero_bound then (* y <= 0 *)
	     begin
	       if self#is_const x then
		 begin
		   let num = self#get_const_val_n x in
		   let is_x_neg = num#leq numerical_zero in
		   if is_x_neg then 
		     let (pia, _, _) = self#affine_image None (v, unit_big_int) [] num#getNum in
		     (pia, None) 
		   else (self#project_out [v], None) 
		 end
	       else
		 begin
		   let is_x_neg = self#leq (self#drop_all#add_ineq false x zero_big_int) in
		   if is_x_neg then   (* x <= 0 *) 
		     let (pia, _, _) =
                       self#affine_image None (v, unit_big_int) [(x, unit_big_int)] zero_big_int in
		     (pia, None) 
		   else (self#project_out [v], None) 
		 end
	     end
	   else (self#project_out [v] , None) 
        
    method log_and (v:variable_t) (x:variable_t) (y:variable_t):'a = 
      let x_int = self#get_interval x in
      let y_int = self#get_interval y in
      let x_min = x_int#getMin in
      let x_max = x_int#getMax in
      let y_min = y_int#getMin in
      let y_max = y_int#getMax in
      let x_pos = x_min#geq zero_bound in
      let y_pos = y_min#geq zero_bound in
      if x_pos || y_pos then
	begin
	  let v_max = 
	    if x_pos then 
	      if y_pos then x_max#min y_max
	      else x_int#getMax 
	    else y_int#getMax in
	  let v_int = new interval_t zero_bound v_max in
	  self#set_interval v v_int
	end
      else 
	begin
	  let x_neg = x_max#leq zero_bound in
	  let y_neg = y_max#leq zero_bound in
	  if x_neg && y_neg then 
	    begin
	      let v_min = x_min#max y_min in
	      let v_int = new interval_t v_min zero_bound in
	      self#set_interval v v_int
	    end
	  else
            self#project_out [v]
	end

    method log_or (v:variable_t) (x:variable_t) (y:variable_t):'a = 
      let x_int = self#get_interval x in
      let y_int = self#get_interval y in
      let x_min = x_int#getMin in
      let x_max = x_int#getMax in
      let y_min = y_int#getMin in
      let y_max = y_int#getMax in
      let x_pos = x_min#geq zero_bound in
      let y_pos = y_min#geq zero_bound in
      if x_pos && y_pos then 
	let v_max = x_max#max y_max in
	let v_int = new interval_t zero_bound v_max in
	self#set_interval v v_int
      else
        self#project_out [v]

    method shr (v:variable_t) (x:variable_t):'a = 
      let x_int = self#get_interval x in
      let x_min = x_int#getMin in
      let x_max = x_int#getMax in
      let x_pos = x_min#geq zero_bound in
      if x_pos then 
	let v_max = x_max#div_floor (bound_of_num (mkNumerical 2)) in
	let v_int = new interval_t zero_bound v_max in
	self#set_interval v v_int
      else
        self#project_out [v]

    method private assert_eq_const v n =
      
      if !dbg then
        pr__debug [STR "assert_eq_const "; v#toPretty; STR " ";
                   n#toPretty; NL; self#toPretty; NL] ;
      
      let new_interval_array = interval_array#copy in 
      let index = (self#get_index v) in
      let interval = self#get_best_interval index in
      let int = mkSingletonInterval n in
      let meet_int = interval#meet int in
      if meet_int#isBottom then
        self#mk_bottom 
      else if params#use_intervals then 
	begin
	  new_interval_array#set index meet_int ;
	  {< poly = top_poly; 
	    interval_array = new_interval_array >}
	end
      else 
	begin
	  new_interval_array#set index meet_int ;
	  {< interval_array = new_interval_array >}
	end

    method assert_non_const_eq (x:variable_t) (y:variable_t):'a =
      
      let _ =
        if !dbg then
          pr__debug [STR "assert_non_const_eq ";
                     x#toPretty; STR " "; y#toPretty; NL; self#toPretty] in
      let res = 
        let x_index = self#get_index x in
        let y_index = self#get_index y in
        let x_int = self#get_best_interval x_index in
        let y_int = self#get_best_interval y_index in
        let int = x_int#meet y_int in 
        if int#isBottom then
          self#mk_bottom 
        else 
	  begin
	    let new_interval_array = interval_array#copy in
	    new_interval_array#set x_index int ;
	    new_interval_array#set y_index int ;
	    if params#use_intervals then 
	      {< poly = top_poly; 
	         interval_array = new_interval_array >}
	    else 
	      match int#singleton with 
	      | Some n -> 
		 {< interval_array = new_interval_array >}
	      | None -> 
		 let new_poly = 
		   let pairs =  [(x_index, unit_big_int); (y_index, neg_unit_big_int)] in 
		   let constr = new linear_constraint_t true pairs zero_big_int in
		   poly#add_constraints [constr] in
		 let new_excluded_vals = 
		   let excluded_x = extra_infos#get_excluded_vals x in
		   let excluded_y = extra_infos#get_excluded_vals y in
		   List.filter (fun vl -> List.exists vl#equal excluded_x) excluded_y in
		 let new_extra_infos = extra_infos#set_excluded_vals x new_excluded_vals in
		 let new_extra_infos = new_extra_infos#set_excluded_vals y new_excluded_vals in
		 {< poly = new_poly ; 
		    interval_array = new_interval_array ;
		    extra_infos = new_extra_infos >}
	  end in
      let _ =
        if !dbg then
          pr__debug [STR "after assert_non_const_eq "; NL; res#toPretty; NL] in
      res

    method assert_eq (x:variable_t) (y:variable_t):'a =
      
      if !dbg then
        pr__debug [STR "assert_eq "; x#toPretty; STR " ";
                   y#toPretty; NL; self#toPretty; NL] ;

      let res = 
        if self#is_bottom then
          self#mk_bottom 
        else if self#is_const x then 
	  let x_n = self#get_const_val_n x in
	  if self#is_const y then 
	    if x_n#equal (self#get_const_val_n y) then
              {< >}
	    else
              self#mk_bottom 
	  else
            self#assert_eq_const y x_n 
        else if self#is_const y then 
	  self#assert_eq_const x (self#get_const_val_n y)
        else
          self#assert_non_const_eq x y in
      
      let _ =
        if !dbg then
          pr__debug [STR "after assert_eq "; NL; res#toPretty; NL] in
      res

    method private add_const_intervals_and_eqs
                     var_to_index int_array eqs vars = 
      let add eqs var = 
	if self#is_const var then 
	  begin
	    let i = 
	      try
		List.assoc var#getIndex var_to_index 
	      with
	      | Not_found ->
		 raise
                   (JCH_failure 
		      (LBLOCK [ STR "Index not found for " ; INT var#getIndex ;
				STR " in JCHPolyIntervalArray.add_const_intervals_and_eqs" ])) in
	    let big_int_const = self#get_const_val var in 
	    int_array#set i (mkSingletonInterval (new numerical_t big_int_const)) ;
            
	    let eq = ([(i, unit_big_int)], minus_big_int big_int_const) in
	    eq :: eqs 
	  end
	else
          eqs in
      List.fold_left add eqs vars


    (* Makes a poly for the call to proc_names
     * Restricts the poly to the variables in invoked_vars *)
    method get_call
             (jproc_info:JCHProcInfo.jproc_info_t)
             (invoked_vars:variable_t list):'a =
      
      if !dbg then
        pr__debug [STR "get_call "; pp_list invoked_vars; NL] ;
      
      let call_var_to_index = ref [] in 
      let repeat_to_index = ref [] in
      let rec add_var i vars = 
	match vars with 
	| var :: rest_vars -> 
	    if List.mem_assoc var !call_var_to_index then 
	      begin
		let j = 
		  try
		    List.assoc var !call_var_to_index
		  with
		  | Not_found ->
		     raise
                       (JCH_failure
			  (LBLOCK [ STR "Call var not found for " ; var#toPretty ;
				    STR " in JCHPolyIntervalArray.get_call" ])) in
		repeat_to_index := (i, j) :: !repeat_to_index 
	      end
	    else 
	      begin 
		call_var_to_index := (var, i) :: !call_var_to_index 
	      end ;
	    add_var (succ i) rest_vars
	| _ -> () in
      add_var 0 invoked_vars ;
      
      let call_var_to_index = List.rev !call_var_to_index in 
      let unique_vars = List.map fst call_var_to_index in 
      let repeats = List.length !repeat_to_index in
      (* CHANGE : Does not work with array lengths *)     
      let (call_poly, call_interval_array, call_extra_infos) = 
	let restr_dom = self#restrict_to_vars jproc_info unique_vars in
	let new_vars = restr_dom#get_poly_vars in
	let p = restr_dom#get_poly in
	let i_array = restr_dom#get_interval_array in
	let call_extra_infos = restr_dom#get_extra_infos in
	let mk_const_constr int_array constrs var = (* add constant value constraints *)
	  if self#is_const var then 
	    begin
	      let i = 
		try
		  List.assoc var call_var_to_index
		with
		| Not_found ->
		   raise
                     (JCH_failure 
			(LBLOCK [ STR "Call var index not found for " ; var#toPretty ;
				  STR " in JCHPolyIntervalArray.get_call" ])) in
	      let big_int_const = self#get_const_val var in 
	      int_array#set i (mkSingletonInterval (new numerical_t big_int_const)) ;
              
	      let constr =
                new linear_constraint_t
                    true [(i, unit_big_int)] (minus_big_int big_int_const) in
	      constr :: constrs 
	    end
	  else
            constrs in
	let number_invoked_vars = List.length invoked_vars in
	if repeats > 0 then 
	  let map = ref [] in
	  let rec add_to_map i i_pos repeat_pos = 
	    if i_pos = number_invoked_vars then
              () 
	    else if List.mem_assoc i_pos !repeat_to_index then
              (* In this case we have to add equalities for the repeats *)
	      begin
		map := (repeat_pos, i_pos) :: !map ; (* A position at the end -> current pos *)
		add_to_map i (succ i_pos) (succ repeat_pos)
	      end
	    else 
	      begin
		map := (i, i_pos) :: !map ;
		add_to_map (succ i) (succ i_pos) repeat_pos
	      end in
	  add_to_map 0 0 (List.length new_vars) ;

	  let big_poly = p#remap_indices !map in
	  let big_array =
            i_array#augment
              (List.length unique_vars)
              (List.length invoked_vars)
              topInterval in  (*unique_vars *)
	  let big_array = big_array#remap number_invoked_vars !map in
	  let big_array = big_array#set_type_intervals jproc_info invoked_vars in
	  let mk_eq_constr (i, j) =
            new linear_constraint_t
                true [(i, unit_big_int); (j, neg_unit_big_int)] zero_big_int in
	  let constrs = List.map mk_eq_constr !repeat_to_index in
	  let constrs =
            List.fold_left (mk_const_constr big_array) constrs new_vars in (* unique_vars *)
	  (big_poly#add_constraints constrs, big_array, call_extra_infos) 
	else  
	  let constrs = List.fold_left (mk_const_constr i_array) [] new_vars in
	  (p#add_constraints constrs, i_array, call_extra_infos) in
      let call_poly_int_array = self#mk_top [] invoked_vars in      
      let call_poly_int_array = call_poly_int_array#set_poly call_poly in
      let call_poly_int_array = call_poly_int_array#set_interval_array call_interval_array in
      call_poly_int_array#set_extra_infos call_extra_infos 

    method meet_invoked
             (a:'a)
             (cols_to_eliminate:int list)
             (arg_length:int)
             (invoked_vars:variable_t list)
             (invoked_lengths:variable_t list)
	     (target_lengths:variable_t list)
             (num_wvars:variable_t list)
             (coll_rvars:variable_t list):'a =
      
      if !dbg then
        pr__debug [STR "meet_invoked "; pp_list_int cols_to_eliminate;
                   STR " "; INT arg_length; STR " "; 
		   pp_list invoked_vars; STR " "; pp_list invoked_lengths; STR " ";
                   pp_list target_lengths; STR " ";
		   pp_list num_wvars; STR " "; pp_list coll_rvars; NL;
		   a#toPretty; NL; self#toPretty; NL] ;
      
      let all_invoked_vars = invoked_vars @ target_lengths in
      let ainterval_array = a#get_interval_array in
      let constrs = a#get_poly#get_constraints in
      let constr_red = ref [] in
      let add_constr constr = 
	if not constr#is_0_geq_0 then constr_red := constr :: !constr_red in
      List.iter add_constr constrs ;
      let apoly = mk_poly_from_constraints false !constr_red in
      let red_poly = apoly#project_out_and_remove cols_to_eliminate in 
      let red_int_array = ainterval_array#remove_entries arg_length cols_to_eliminate in
      let (eliminated_var_to_index, red_var_to_index) =
	List.partition (fun (_, c) -> List.mem c cols_to_eliminate) a#get_var_to_index in
      let (eliminated_vars, kept_vars) = 
	List.partition (fun v ->
            List.exists (fun (i, _) ->
                i = v#getIndex) eliminated_var_to_index) a#get_poly_vars in
	  
      let red_extra_infos =
	a#get_extra_infos#remove_vars eliminated_vars in
	  
      (* Add constant constraints and remove the constant unused indices *)
      let (changed_vars, changed_poly, changed_int_array) = 
	if red_poly#is_bottom then
          (all_invoked_vars, red_poly, red_int_array)
	else 
	  let mk_constr i c = 
	    new linear_constraint_t true [(i, unit_big_int)] (minus_big_int c#getNum) in
	  let rec get_const_constrs (new_vs, const_cols, constrs) i vs = 
	    match vs with 
	    | v :: rest_vs -> 
		begin
		  if self#is_const v then 
		    let c = self#get_const_val_n v in
		    get_const_constrs
                      (new_vs, i :: const_cols, (mk_constr i c) :: constrs) (succ i) rest_vs
		  else
                    get_const_constrs (v :: new_vs, const_cols, constrs) (succ i) rest_vs
		end
	    | _ -> (List.rev new_vs, const_cols, constrs) in 
	  let (new_vars, is, constrs) = get_const_constrs ([], [], []) 0 all_invoked_vars in
	  let new_poly = 
	    if red_poly#is_top then red_poly
	    else 
	      let poly' = if constrs = [] then red_poly else red_poly#add_constraints constrs in
	      poly'#project_out_and_remove is in 
	  let new_int_array = red_int_array#remove_entries (List.length all_invoked_vars) is in
	  (new_vars, new_poly, new_int_array) in

      (* add variables and reorder to get the same variables as in the callee poly *) 
      let (invoked_poly, invoked_interval_array, invoked_extra_infos) = 
	if changed_poly#is_bottom then
          (changed_poly, changed_int_array, red_extra_infos)
	else
	  begin
	    let changed_var_to_index = mk_var_to_index changed_vars in
	    let old_col_to_new_col = 
	      List.map (fun (index, old_col) -> 
		try
		  (old_col, List.assoc index var_to_index)
		with
                | Not_found ->
		   raise
                     (JCH_failure 
			(LBLOCK [ STR "variable not found for " ; INT index ;
				  STR " in JCHPolyIntervalArray.meet_invoked" ]))
		) changed_var_to_index in 

	    let new_poly = 
	      if changed_poly#is_top || changed_poly#is_bottom then changed_poly
	      else 
		begin
		  let constrs = changed_poly#get_constraints in 
		  let new_constrs = List.map (fun c -> c#remap old_col_to_new_col) constrs in
		  mk_poly_from_constraints true new_constrs 
		end in
	    let new_int_array = interval_array#make_bottom_intervals self#get_dim in
	    let add_pair (old_ind, new_ind) = new_int_array#set new_ind (changed_int_array#get old_ind) in
	    List.iter add_pair old_col_to_new_col ;
	    let new_extra_infos =
              (* called variable has length vars that the caller does not have *)              
	      if List.length kept_vars = List.length all_invoked_vars then 
		begin
	      	  let old_v_to_new_v = List.combine kept_vars all_invoked_vars in
		  let old_ind_to_new_var =
                    List.map (fun (old_v, new_v) -> (old_v#getIndex, new_v)) old_v_to_new_v in
		  red_extra_infos#replace_vars old_v_to_new_v old_ind_to_new_var 
		end
	      else
		new numeric_info_t in
	    (new_poly, new_int_array, new_extra_infos)
	  end in

      if invoked_poly#is_bottom then
        self#mk_bottom 
      else 
	begin
	  let top_poly_int_array = self#mk_top var_to_const poly_vars in
	  let invoked_poly_int_array = 
	    let pia =
              if params#use_intervals then
                top_poly_int_array
              else
                top_poly_int_array#set_poly invoked_poly in
	    let pia' = pia#set_interval_array invoked_interval_array in
	    pia'#set_extra_infos invoked_extra_infos in
	  let changed_vars =
            List.filter a#get_extra_infos#is_changed_sym_param all_invoked_vars in
	  let invoked_extra_infos =
            invoked_poly_int_array#get_extra_infos#add_changed_sym_params changed_vars in
	  let invoked_poly_int_array =
            invoked_poly_int_array#set_extra_infos invoked_extra_infos in
	  let proc_poly_int_array = self#project_out (num_wvars @ target_lengths) in 
	  proc_poly_int_array#meet' invoked_poly_int_array coll_rvars
	end

    (* It returns a poly for the new_vars
     * The variables in poly that are not in the new_vars are projected away
     * For the constant variables in new_vars, constant constraints are added
     * All the other variables have a column in the constructed poly but no constraints *) 
    method restrict_to_vars
             (jproc_info:JCHProcInfo.jproc_info_t) (new_vars:variable_t list) =
      
      if !dbg then
        pr__debug [STR "restrict_to_vars "; pp_list new_vars ; NL; self#toPretty; NL] ;
      
      if poly#is_bottom then
        {< >} 
      else 
	let (new_poly_vars, other_vars) =
          List.partition (fun v -> List.mem v poly_vars) new_vars in
	let (vars_that_stay, vars_to_remove) =
          List.partition (fun v -> List.mem v new_poly_vars) poly_vars in
	let inds_to_remove = List.map self#get_index vars_to_remove in
	let new_var_to_index = mk_var_to_index new_vars in
	
	let mk_index_map (next, map) v = (succ next, (v, next) :: map) in
	let (_, red_poly_map) =
          List.fold_left mk_index_map (0, []) (vars_that_stay @ other_vars) in 
	let (_, new_poly_map) = List.fold_left mk_index_map (0, []) new_vars in
	let mk_map_pair v = 
	  try
	    (List.assoc v red_poly_map, List.assoc v new_poly_map)
	  with
	  | Not_found ->
	     raise (JCH_failure 
		      (LBLOCK [ STR "poly map not found for " ; v#toPretty ;
				STR " in JCHPolyIntervalArray.restrict_to_vars" ])) in
	let map = List.map mk_map_pair new_vars in
	let red_poly = 
	  if poly#is_top then
            poly
	  else 
	    begin
	      let rp1 = poly#project_out_and_remove inds_to_remove in
	      rp1#remap_indices map 
	    end in
	let new_dim = List.length new_vars in

	let red_interval_array1 =
          interval_array#remove_entries self#get_dim (List.rev inds_to_remove) in 
	let dim1 = self#get_dim - List.length inds_to_remove in
	let red_interval_array2 =
          red_interval_array1#augment dim1 new_dim topInterval in 
	let red_interval_array = red_interval_array2#remap new_dim map in
	let red_interval_array =
          red_interval_array#set_type_intervals jproc_info new_vars in

        (* Add constraint from the constants *)
	let eqs =
          self#add_const_intervals_and_eqs
            new_var_to_index red_interval_array [] other_vars in
	let constrs =
          List.map (fun (pairs, const) ->
              new linear_constraint_t true pairs const) eqs in

	let red_extra_infos = extra_infos#change_vars new_vars in
	let new_poly = red_poly#add_constraints constrs in
	{< poly = new_poly ; 
	   poly_vars = new_vars ;
	   var_to_index = new_var_to_index ;
	   interval_array = red_interval_array ;
	   extra_infos = red_extra_infos
        >}

    (* It returns a poly for the new_vars
     * The variables in poly that are not in the new_vars are projected 
     * away and removed *)
    method restrict_to_vars_2 (new_vars: variable_t list) =
      let new_vars =
        List.map (fun v ->
            List.find (fun v' -> v'#getName#equal v#getName) poly_vars) new_vars in
      
      if !dbg then
        pr__debug [STR "restrict_to_vars_2 "; pp_list new_vars ; NL; self#toPretty; NL] ;
      
      if poly#is_bottom then
        {< >} 
      else
	let (new_poly_vars, other_vars) =
          List.partition (fun v -> List.mem v poly_vars) new_vars in 
	let (vars_that_stay, vars_to_remove) =
          List.partition (fun v -> List.mem v new_poly_vars) poly_vars in 
	let inds_to_remove = List.map self#get_index vars_to_remove in
	let new_var_to_index = mk_var_to_index new_vars in
	
	let mk_index_map (next, map) v = (succ next, (v, next) :: map) in
	let (_, red_poly_map) =
          List.fold_left mk_index_map (0, []) (vars_that_stay @ other_vars) in 
	let (_, new_poly_map) = List.fold_left mk_index_map (0, []) new_vars in
	let mk_map_pair v = 
	  try
	    (List.assoc v red_poly_map, List.assoc v new_poly_map)
	  with
	  | Not_found ->
	     raise (JCH_failure 
		      (LBLOCK [ STR "poly map not found for " ; v#toPretty ;
				STR " in JCHPolyIntervalArray.restrict_to_vars" ])) in
	let map = List.map mk_map_pair new_vars in
	let red_poly = 
	  if poly#is_top then poly
	  else 
	    begin
	      let rp1 = poly#project_out_and_remove inds_to_remove in
	      rp1#remap_indices map 
	    end in

	let red_interval_array =
          interval_array#remove_entries self#get_dim (List.rev inds_to_remove) in 

	let red_extra_infos = extra_infos#change_vars new_vars in
	{< poly = red_poly ; 
	   poly_vars = new_vars ;
	   var_to_index = new_var_to_index ;
	   interval_array = red_interval_array ;
	   extra_infos = red_extra_infos
        >}

    method check_type (var:variable_t) =
      
      if !dbg then
        pr__debug [STR "check_type "; var#toPretty; NL] ;
      
      let index = self#get_index var in
      let interval = self#get_best_interval index in
      let tinterval = interval_array#get_type_interval (self#get_index var) in
      if interval#leq tinterval then
        {< >}
      else
        self#project_out [var]

    (* Copies the interval and num_info from src to dst *)
    method copy_info
             (dst:variable_t)
             (src_interval:interval_t)
             (src_excluded_vals:numerical_t list):'a =
      
      if !dbg then
        pr__debug [STR "copy_info "; dst#toPretty; STR " ";
                   src_interval#toPretty; NL; self#toPretty; NL] ;
      
      let new_interval_array = interval_array#copy in
      new_interval_array#set (self#get_index dst) src_interval ;
      
      let new_extra_infos = extra_infos#set_excluded_vals dst src_excluded_vals in
      {< interval_array = new_interval_array ;
	 extra_infos = new_extra_infos >} 

    method restrict_to_type (vars:variable_t list):'a =
      
      if !dbg then pr__debug [STR "restrict_to_type "; pp_list vars ; NL] ;
      
      if self#is_bottom then
        {< >} 
      else
        {< interval_array =
             interval_array#restrict_to_type (List.map self#get_index vars) >} 

    method private get_join_excluded (var1:variable_t) (var2:variable_t) = 
      let interval1 = interval_array#get (self#get_index var1) in
      let interval2 = interval_array#get (self#get_index var2) in
      let excluded1 = extra_infos#get_excluded_vals var1 in
      let excluded2 = extra_infos#get_excluded_vals var2 in
      let common_excluded = 
	List.filter (fun vl -> List.exists vl#equal excluded2) excluded1 in
      let new_set = NumericalCollections.set_of_list common_excluded in
      let add_val other_interval vl = 
	if not (other_interval#contains vl) then new_set#add vl in
      List.iter (add_val interval2) excluded1 ;
      List.iter (add_val interval1) excluded2 ;
      new_set#toList

    method add_empty_collection (var:variable_t):'a = 
      {< extra_infos = extra_infos#add_empty_collection var >}

    method set_join
             (dst:variable_t) (src1:variable_t) (src2:variable_t):'a =
      
      if !dbg then
        pr__debug [STR "set_join "; dst#toPretty ; STR " = ";
                   src1#toPretty; STR " U "; src2#toPretty; NL] ;
      
      let new_interval_array = interval_array#copy in 
      let dst_index = self#get_index dst in 
      let src1_int = 
	if self#is_const src1 then 
	  let const = self#get_const_val_n src1 in
	  mkSingletonInterval const 
	else 
	  let src1_index = self#get_index src1 in
	  self#get_best_interval src1_index in
      let src2_int = 
	if self#is_const src2 then 
	  let const = self#get_const_val_n src2 in
	  mkSingletonInterval const 
	else 
	  let src2_index = self#get_index src2 in
	  self#get_best_interval src2_index in
      let jint = 
	if extra_infos#is_empty_collection src1 then
          src2_int
	else if extra_infos#is_empty_collection src2 then
          src1_int
	else
          src1_int#join src2_int in
      let new_interval = 
	let ctp_int = interval_array#get_type_interval dst_index in
	jint#meet ctp_int in
      new_interval_array#set dst_index new_interval ;

      let new_extra_infos = 
	if self#is_const src1 then 
	  if self#is_const src2 then
            extra_infos 
	  else 
	    let new_excluded = extra_infos#get_excluded_vals src2 in
	    extra_infos#set_excluded_vals dst new_excluded 
	else if self#is_const src2 then 
	  let new_excluded = extra_infos#get_excluded_vals src1 in
	  extra_infos#set_excluded_vals dst new_excluded 
	else 
	  let new_excluded = self#get_join_excluded src1 src2 in
	  extra_infos#set_excluded_vals dst new_excluded in

      {< interval_array = new_interval_array; 
	 extra_infos = new_extra_infos >}

    (* values of collections are always in intervals. However, 
       if two variables point to the same object, then they are equal in poly *)
    method add_val_to_collection
             (is_empty_collection:bool)
             (coll_var:variable_t)
             (val_var:variable_t)
             (coll_interval: interval_t):'a = 
      let _ =
        if !dbg then
          pr__debug [STR "add_val_to_collection ";
                     (if is_empty_collection then STR " empty collection " else STR "") ; 
		     coll_var#toPretty; STR " "; val_var#toPretty; STR " ";
                     coll_interval#toPretty; NL; self#toPretty; NL] in
      
      let new_extra_infos = extra_infos#remove_empty_collection coll_var in
      let new_interval_array = interval_array#copy in 
      let coll_index = self#get_index coll_var in 
      let (val_interval, new_extra_infos) = 
	if self#is_const val_var then 
	  let const = self#get_const_val_n val_var in
	  let int = mkSingletonInterval const in
	  (int,
           new_extra_infos#remove_excluded_val coll_var (self#get_const_val_n val_var))
	else 
	  let val_index = self#get_index val_var in
	  let val_int = self#get_best_interval val_index in
	  let new_excluded = self#get_join_excluded coll_var val_var in
	  let ctp_int = interval_array#get_type_interval coll_index in
	  (val_int#meet ctp_int,
           new_extra_infos#set_excluded_vals coll_var new_excluded) in
      begin
        (if is_empty_collection then
           new_interval_array#set coll_index val_interval  (* first element of the collection *)
         else
	   let join_interval = coll_interval#join val_interval in
	   new_interval_array#set coll_index join_interval) ;
        {< interval_array = new_interval_array; 
	   extra_infos = new_extra_infos
        >}
      end

    method get_field
             (jproc_info: JCHProcInfo.jproc_info_t)
             (field_info: JCHPreAPI.field_info_int)
             (intervals: interval_t list) var =
      
      if !dbg then
        pr__debug [STR "get_field "; var#toPretty; NL; pp_list intervals; NL] ;
      
      let index = self#get_index var in
      let new_interval_array = 
	match intervals with 
	| [interval] -> 
	    begin
	      let interval_array' = interval_array#copy_set_typed index interval in
	      try (* If var is an array but the field is not known to be an array. Is that possible ? *)
		let length_var = Option.get (jproc_info#get_length var) in
		interval_array'#copy_set_typed
                  (self#get_index length_var) (JCHTypeUtils.length_interval) 
	      with _ -> interval_array'
	    end
	| interval :: length_interval :: _ -> 
	    begin
	      let interval_array' = interval_array#copy_set_typed index interval in
	      try
		let length_var = Option.get (jproc_info#get_length var) in
		interval_array'#copy_set_typed (self#get_index length_var) length_interval 
	      with _ -> interval_array'
	    end
	| _ ->
           begin
	     pr__debug [STR "Analysis failed: ";
                        STR "JCHPolyIntervalArray.get_field expected intervals <> [] "; NL] ;
             raise (JCHAnalysisUtils.numeric_params#analysis_failed
                      3 "JCHPolyIntervalArray.get_field expected intervals <> [] ")
           end in
      {< interval_array = new_interval_array ;
	 extra_infos = extra_infos#set_fields var [field_info]
      >}

    method new_array (array:variable_t) (dims:variable_t list):'a =
      
      if !dbg then
        pr__debug [STR "new_array "; array#toPretty; STR " "; pp_list dims; NL] ;
      
      let index = self#get_index array in
      let new_interval_array =
        interval_array#copy_set index (mkSingletonInterval numerical_zero) in
      let add_dim_interval dim = 
	let interval = self#get_interval dim in 
	let new_interval = interval#meet JCHTypeUtils.length_interval in
	if not (self#is_const dim) then 
	  new_interval_array#set (self#get_index dim) new_interval in
      begin
        List.iter add_dim_interval dims ;
        {< interval_array = new_interval_array >}
      end
      
    method array_load (array:variable_t) (element:variable_t):'a = 
      let acol = self#get_index array in
      let ecol = self#get_index element in 
      let a_int = self#get_best_interval acol in
      let new_interval_array = interval_array#copy_set_typed ecol a_int in
      if params#use_intervals then
	{< poly = top_poly; interval_array = new_interval_array >}
      else 
	let new_poly = poly#copy_other_col_constrs acol ecol in
	{< poly = new_poly; interval_array = new_interval_array >}

    method down_cast_float (src:variable_t) (dst:variable_t):('a * bool) =
      
      if !dbg then
        pr__debug [STR "down_cast "; src#toPretty; STR " "; dst#toPretty; NL] ;
      
      let src_index = self#get_index src in
      let interval = self#get_best_interval src_index in
      let dst_index = self#get_index dst in
      let tinterval = interval_array#get_type_interval dst_index in
      if interval#leq tinterval then 
	let mx = interval#getMax in
	let mn = interval#getMin in
	let (max, min) = 
	  let excluded_vals = extra_infos#get_excluded_vals src in
	  let max = 
	    match mx#getBound with 
	    | NUMBER num -> 
	       if num#gt numerical_zero
                  && List.exists num#equal excluded_vals then
		  mx#sub one_bound
	       else
                 mx
	    | _ -> mx in
	  let min = 
	    match mn#getBound with 
	    | NUMBER num -> 
	       if num#lt numerical_zero
                  && List.exists num#equal excluded_vals then
		  mn#add one_bound
	       else
                 mn
	    | _ -> mn in
	  (max, min) in
	let new_interval = new interval_t min max in
	let new_interval_array = interval_array#copy_set dst_index new_interval in
	({< interval_array = new_interval_array >}, false)
      else
        (self#project_out [dst], true)

    method float_const (dst1:variable_t) (f:float):'a = 
      let dst1_index = self#get_index dst1 in
      try (* for the case when f is not a number *)
	let dst1_ind = self#get_index dst1 in
	let (min, max, interval) = JCHAnalysisUtils.float_to_interval f in
	let new_interval_array = interval_array#copy_set dst1_index interval in
	let new_extra_infos = 
	  if min#equal max then
            extra_infos
	  else
            extra_infos#set_excluded_vals dst1 [min; max] in
	if params#use_intervals then 
	  {< poly = top_poly; 
	     interval_array = new_interval_array ;
	     extra_infos = new_extra_infos
          >}
	else
	  let constrs = mk_constraints_from_interval false dst1_ind interval in
	  {< poly = poly#add_constraints constrs ; 
	     interval_array = new_interval_array ;
	     extra_infos = new_extra_infos
          >}
      with _ -> self#project_out [dst1] 

    (* This is used for stubs
     * It eliminates the constraints that derive from the intervals for arguments *)
    method simplify_with_intervals =
      
      if !dbg then
        pr__debug [STR "simplify_with_intervals "; NL; self#toPretty; NL] ;
      
      let (returns, params) =
        List.partition (fun v -> JCHSystemUtils.is_return v) poly_vars in
      let vars' = params @ returns in
      let var_to_index' = mk_var_to_index vars' in
      let map =
        List.map (fun v ->
            (self#get_index v, List.assoc v#getIndex var_to_index')) poly_vars in
      let reordered_poly = poly#remap_indices map in
      let dim = List.length poly_vars in
      let remap_interval_array = interval_array#remap dim map in
      let (restr_poly, restr_interval_array) =
        move_simple_ineqs_to_intervals reordered_poly remap_interval_array in
      
      let inv_map = 
	List.map (fun v ->
            (List.assoc v#getIndex var_to_index', self#get_index v)) poly_vars in

      let restr_poly' = restr_poly#remap_indices inv_map in
      let restr_interval_array' = restr_interval_array#remap dim inv_map in
      
      {< poly = restr_poly'; interval_array = restr_interval_array' >}

    (* CHANGE: It does not deal with array lengths *)
    method to_postconditions2 (jproc_info: JCHProcInfo.jproc_info_t) = 
      let vars =
        List.filter (fun v -> not (JCHSystemUtils.is_exception v)) poly_vars in

      (* map from variable index to parameter_index *)
      let map = 
	let get_pair v = 
	  let info = jproc_info#get_jvar_info v in
	  let param_index = 
	    match info#get_param_index with
	    | Some i -> i
	    | _ -> -1 in 
	  (self#get_index v, param_index) in 
	List.map get_pair vars in

      (* Add predicates for poly *) 
      let post_preds = 
	if poly#is_bottom then []
	else 
	  begin 
	    let constrs =
              List.filter (fun c ->
                  not c#is_const_equality) poly#get_constraints in 
	    let add_cond post constr = 
	      try (* For the case when in the transformed chif, 
                     there is a local variable variant which corresponds to a 
                     value that was not stored yet, ... *)
		(constr#to_post_predicate map [] [] [] []) :: post 
	      with _ -> post in
	    List.fold_left add_cond [] constrs
	  end in

      (* Add predicates for the intervals.
       * Parameter intervals that are max intervals are not added. *)
      let post_preds =
	let add_pred post var = 
	  let var_index = self#get_index var in
	  let interval = interval_array#get var_index in
	  let arg_index = List.assoc var_index map in
          (* if the variable is return then make a predicate *)
	  if not (interval#equal topInterval) && (JCHSystemUtils.is_number var) then 
	    begin
	      (interval_to_summary_post_predicates2
                 ~is_loc:true
                 ~is_lc:false
                 ~is_length:false
                 ~is_aux:false
                 ~is_aux_length:false
                 ~var_index:arg_index
                 ~name:""
                 ~interval) @ post
	    end
	  else post in
	List.fold_left add_pred post_preds vars in

      (* Add predicates for the excluded values *)
      let post_preds =
	let add_pred post var = 
	  let excluded = extra_infos#get_excluded_vals var in
	  let arg_index = 
	    try
	      List.assoc (self#get_index var) map 
	    with
	    | Not_found ->
	       raise
                 (JCH_failure 
		    (LBLOCK [ STR "argument index not found for " ; 
			      INT (self#get_index var) ;
			      STR " in JCHPolyIntervalArray.to_postconditions2" ])) in
	  if excluded = [] then
            post_preds
	  else if JCHSystemUtils.is_number var then 
	    (excluded_vals_to_summary_post_predicates arg_index excluded) @ post
	  else
            post in
	List.fold_left add_pred post_preds vars in

      post_preds

    (* This is to be used for a poly_interval_array reduced to the 
     * local vars and return *)
    method to_postconditions
             (include_loop_counters:bool)
             (jproc_info:JCHProcInfo.jproc_info_t)
             (local_var_map:(variable_t * variable_t) list)
	     (aux_vars:variable_t list) = 
      let local_vars =
        List.filter (fun v -> List.mem v poly_vars) (List.map snd local_var_map) in

      let (rev_local_var_map, equal_orig_vars) = 
	let m : VariableCollections.set_t VariableCollections.table_t =
          new VariableCollections.table_t in
	let add_pair (orig_var, var) = 
	  match m#get var with 
	  | Some set -> set#add orig_var
	  | _ -> m#set var (VariableCollections.set_of_list [orig_var]) in
	List.iter add_pair local_var_map ;
	let eq_orig_vars = ref [] in
	let ls = ref [] in
	let add_equal_orig_vars
              (var: variable_t) (orig_vars: VariableCollections.set_t) = 
	  match orig_vars#toList with 
	  | [orig_var] -> ls := (var#getIndex, orig_var) :: !ls
	  | orig_var :: rest_orig_vars -> 
	      let is_argument orig_v = List.mem orig_v poly_vars in
	      let orig_arg = 
		try
		  List.find is_argument (orig_var :: rest_orig_vars)
		with _ -> orig_var in
              begin
	        ls := (var#getIndex, orig_var) :: !ls ;
	        orig_vars#remove orig_arg ;
	        eq_orig_vars := (orig_arg :: (orig_vars#toList)) :: !eq_orig_vars
              end
	  | _ -> () in
        begin
	  m#iter add_equal_orig_vars ;
	  (!ls, !eq_orig_vars)
        end in
        
      let length_vars = 
	let length_vars = ref [] in
	let add_length_var var = 
	  match jproc_info#get_length var with 
	  | Some length_var -> 
	     if List.mem length_var poly_vars then
               length_vars := length_var :: !length_vars 
	  | _ -> () in
	List.iter add_length_var local_vars ;
	!length_vars in
      
      let vars = local_vars @ length_vars in
      let (lc_vars, lc_map) = 
	if include_loop_counters then 
	  begin
	    let add_wto (vars, pairs) w = 
	      try 
		let lc = w#get_var in 
		(lc::vars, (self#get_index lc, w#get_first_pc) :: pairs)
	      with _ -> (vars, pairs) in
	    List.fold_left add_wto ([], []) jproc_info#get_wto_infos 
	  end
	else
          ([], []) in

      (* local var index of an original variable *)
      let get_orig_local_var_index orig_var = 
	let name = orig_var#getName#getBaseName in
	if name.[0] = 'r' && name.[1] <> 'e' then 
	  int_of_string (Str.string_after name 1)
	else
          -1 in
      
      (* map from variable index in the poly to original local var index *)
      let map = 
	let get_pair v = 
	  let orig_var = List.assoc v#getIndex rev_local_var_map in
	  let local_var_index = get_orig_local_var_index orig_var in
	  (self#get_index v, local_var_index) in
	List.map get_pair local_vars in

      (* map from length var index to the array local var index *)
      let length_map = 
	let get_pair v = 
	  let var = Option.get (jproc_info#get_variable_from_length v) in
	  let orig_var = List.assoc var#getIndex rev_local_var_map in
	  let local_var_index = 
	    let name = orig_var#getName#getBaseName in
	    if name.[0] = 'r' && name.[1] <> 'e' then 
	      int_of_string (Str.string_after name 1)
	    else
              -1 in
	  (self#get_index v, local_var_index) in
	List.map get_pair length_vars in

      let aux_map =
	let get_pair v = 
	  (self#get_index v, "aux_" ^ (string_of_int v#getIndex)) in
	List.map get_pair aux_vars in

      let aux_length_vars =
	let length_vars = ref [] in
	let add_length_var var = 
	  match jproc_info#get_length var with 
	  | Some length_var -> 
	     if List.mem length_var poly_vars then
               length_vars := length_var :: !length_vars 
	  | _ -> () in
        begin
	  List.iter add_length_var aux_vars ;
	  !length_vars
	end in
        
      let aux_length_map =
	let get_pair v =
	  let var = Option.get (jproc_info#get_variable_from_length v) in
	  (self#get_index v, "aux_" ^ (string_of_int var#getIndex)) in
	List.map get_pair aux_length_vars in	
	  
      (* Add predicates for the local variables that are equal *)
      let post_preds = 
	let pps = ref [] in
	let add_eqs orig_vars = 
	  match orig_vars with 
	  | orig_var :: rest_orig_vars -> 
	      let arg_index = get_orig_local_var_index orig_var in
	      let add_eq ov = 
		let i = get_orig_local_var_index ov in
		pps := (equality_to_summary_post_predicate i arg_index) :: !pps in
	      List.iter add_eq rest_orig_vars 
	  | _ -> () in
        begin
	  List.iter add_eqs equal_orig_vars ;
	  !pps
        end in

      (* Add predicates for poly *) 
      let post_preds = 
	if poly#is_bottom || params#use_intervals then
          []
	else 
	  begin 
	    let not_included var = 
	      if include_loop_counters then 
		not ((List.mem var vars)
                     || (JCHSystemUtils.is_loop_counter var)
                     || (List.mem var aux_vars))
	      else not ((List.mem var vars) || (List.mem var aux_vars)) in
	    let other_vars = List.filter not_included poly_vars in
	    let constrs =
	      let restr_constrs = 
		try
		  let restr_poly = (self#project_out other_vars)#get_poly in
		  restr_poly#get_constraints 
		with (JCHAnalysisUtils.JCH_num_analysis_failure _) ->
		  let cs = poly#get_constraints in
		  let other_inds = List.map self#get_index other_vars in
		  let does_not_have_other_vars c = 
		    not (List.exists (fun i -> c#has_index i) other_inds) in
		  List.filter does_not_have_other_vars cs in
	      List.filter (fun c -> not c#is_const_equality)  restr_constrs in

	    let add_cond post constr = 
	      try (* For the case when in the transformed chif, there is a local 
                   * variable variant which corresponds to a value that was not
                   * stored yet, ... *)
		(constr#to_post_predicate
                   map lc_map length_map aux_map aux_length_map) :: post
	      with _ -> post in
	    List.fold_left add_cond post_preds constrs
	  end in

      (* Add predicates for the intervals.
       * Parameter intervals that are max intervals are not added. *)
      let post_preds =
	let add_pred is_loc is_lc is_length is_aux is_aux_length post var = 
	  let var_index = self#get_index var in
	  let interval = interval_array#get var_index in
	  let (arg_index, name) = 
	    if is_loc then
              (List.assoc var_index map , "")
	    else if is_lc then
              (List.assoc var_index lc_map , "")
	    else if is_length then
              (List.assoc var_index length_map, "")
	    else if is_aux then
              (-1, List.assoc var_index aux_map)
	    else if is_aux_length then
              (-1, List.assoc var_index aux_length_map)
	    else
              raise
                (JCHBasicTypes.JCH_failure (STR "expected variable type ")) in
	  if not (interval#equal topInterval)
             && (JCHSystemUtils.is_number var) then 
	    begin
	      (interval_to_summary_post_predicates2
                 ~is_loc
                 ~is_lc
                 ~is_length
                 ~is_aux
                 ~is_aux_length
                 ~var_index:arg_index
                 ~name
                 ~interval) @ post
	    end
	  else post in
	let pps =
          List.fold_left (add_pred true false false false false) post_preds local_vars in
	let pps =
          List.fold_left (add_pred false true false false false) pps lc_vars in
	let pps =
          List.fold_left (add_pred false false true false false) pps length_vars in
	let pps =
          List.fold_left (add_pred false false false true false) pps aux_vars in
	List.fold_left (add_pred false false false false true) pps aux_length_vars in

      (* Add predicates for the constants *)
      let post_preds = 
	let add_pred post (ind, const) = 
	  try 
	    let orig_var = List.assoc ind rev_local_var_map in
	    let local_var_index = 
	      let name = orig_var#getName#getBaseName in
	      if name.[0] = 'r' && name.[1] <> 'e' then 
		int_of_string (Str.string_after name 1)
	      else -1 in
	    let interval = mkSingletonInterval const in
	    (interval_to_summary_post_predicates local_var_index interval interval) @ post
	  with _ -> post in
	List.fold_left add_pred post_preds var_to_const in

      (* Add predicates for the excluded values. Does not deal with excluded values for length vars *)
      let post_preds =
	let add_pred post var = 
	  if not (JCHSystemUtils.is_length var) then 
	    begin
	      let excluded = extra_infos#get_excluded_vals var in
	      let arg_index = List.assoc (self#get_index var) map in
	      if excluded = [] then
                post_preds
	      else if JCHSystemUtils.is_number var then 
		(excluded_vals_to_summary_post_predicates arg_index excluded) @ post
	      else
                post
	    end 
	  else
            post in
	List.fold_left add_pred post_preds vars in

      post_preds

    method init_assumptions (jproc_info: JCHProcInfo.jproc_info_t) : 'a = 
      let name_to_index = ref [] in
      let index_to_types = ref [] in
      let add_var_name var = 
	let jvar_info = jproc_info#get_jvar_info var in 
	let var_index = self#get_index var in
	index_to_types := (var_index, jvar_info#get_types) :: !index_to_types ;
	if jvar_info#is_parameter then 
	  let index = Option.get (jvar_info#get_param_index) in
	  name_to_index := ("arg" ^ (string_of_int index), var_index) :: !name_to_index 
	else if jvar_info#is_return then 
	  name_to_index := ("return", var_index) :: !name_to_index 
	else if JCHSystemUtils.is_length var then 
	  begin
	    let var_with_l = Option.get (jproc_info#get_variable_from_length var) in
	    let var_with_l_info = jproc_info#get_jvar_info var_with_l in
	    if var_with_l_info#is_return then 
		name_to_index := ("length_return", var_index) :: !name_to_index 
	    else if var_with_l_info#is_parameter then
	      begin
		let index = List.hd var_with_l_info#get_local_indices in
		name_to_index := ("length_arg" ^ (string_of_int index), var_index) :: !name_to_index 
	      end
	  end in
      List.iter add_var_name poly_vars;
      let rel_exprs = jproc_info#get_method_info#get_argument_assumptions in
      let constrs =
        List.map (mk_arg_constraint_from_rel_expr !name_to_index !index_to_types) rel_exprs in
      let constr_poly = mk_poly_from_constraints true constrs in
      let pia = {< poly = poly#meet constr_poly >}#move_simple_ineqs in
      let new_poly = pia#get_poly in
      let new_interval_array =
        self#get_best_interval_array new_poly pia#get_interval_array in
      {< poly = new_poly; interval_array = new_interval_array >}

    method remove_duplicates : 'a = 
      if self#is_top || self#is_bottom then
        {< >} 
      else 
	begin
	  let new_poly = poly#remove_duplicates in
	  let (restr_poly, restr_interval_array) =
            move_simple_ineqs_to_intervals new_poly interval_array in
	  {< poly = restr_poly; interval_array = restr_interval_array >}
	end

    method set_type_intervals
             (jproc_info:JCHProcInfo.jproc_info_t) (vars:variable_t list) = 
      {< interval_array = interval_array#set_type_intervals jproc_info vars >}
      
    method set_type_intervals_and_restrict
             (jproc_info:JCHProcInfo.jproc_info_t) (vars:variable_t list) = 
      {< interval_array =
           interval_array#set_type_intervals_and_restrict jproc_info vars >}

    method add_field (v:variable_t) (fInfo:field_info_int):'a =
      {< extra_infos = extra_infos#add_field v fInfo >}
      
    method remove_field (v:variable_t) (fInfo:field_info_int):'a =
      {< extra_infos = extra_infos#remove_field v fInfo >}
      
    method set_fields (v:variable_t) (fInfos:field_info_int list):'a =
      {< extra_infos = extra_infos#set_fields v fInfos >}
      
    method get_vars_with_fields
             (jproc_info:JCHProcInfo.jproc_info_t):variable_t list =
      let vars = ref [] in 
      let length_vars = ref [] in
      let add_var v =
	if extra_infos#has_fields v then
	  begin
	    vars := v :: !vars ;
	    let jvar_info = jproc_info#get_jvar_info v in
	    match jvar_info#get_length with
	    | (Some len, _) ->
		length_vars := len :: !length_vars
	    | _ -> () 
	  end in
      begin
        List.iter add_var poly_vars ;
        List.rev_append !vars !length_vars
      end
      
    method transfer_fields
             (remove:bool) (dst_var:variable_t) (src_var:variable_t):'a =
      let src_fields = extra_infos#get_fields src_var in
      let ei = extra_infos#set_fields dst_var src_fields in
      let new_extra_fields =
	if remove then
          ei#set_fields src_var []
	else
          ei in
      {< extra_infos = new_extra_fields >}

    method copy_num_info (dst_var:variable_t) (src_var:variable_t):'a =
      {< extra_infos = extra_infos#set_same_info dst_var src_var >}

    method to_pretty = 
      let pp_vars =
        pretty_print_list
          poly_vars
          (fun v ->
            LBLOCK [STR "("; v#toPretty; STR ", "; INT v#getIndex; STR ")"])
          "{" ", " "}" in
      let pp_poly = try poly#to_pretty poly_vars with _ -> poly#toPretty in
      let pp_ints =
        try interval_array#to_pretty poly_vars with _ -> interval_array#toPretty in
      LBLOCK [ STR "poly_vars: "; INDENT (5, pp_vars); NL;
	       STR "var_to_index: "; INDENT (5, pp_assoc_list_ints var_to_index); NL;
	       STR "poly: "; NL; STR "{"; NL; INDENT (5, pp_poly); NL; STR "}"; NL;
	       STR "interval array: "; NL; INDENT (5, pp_ints); NL;
	       STR "extra_infos: "; NL; INDENT (5, extra_infos#toPretty); NL] 

    method toPretty = self#to_pretty

    method pr__debug_large_poly_interval_array =
      let pp_vars =
        pretty_print_list
          poly_vars
          (fun v -> LBLOCK [STR "("; v#toPretty; STR ", "; INT v#getIndex; STR ")"])
          "{" ", " "}" in
      let pp_poly = try poly#to_pretty poly_vars with _ -> poly#toPretty in
      pr__debug [ STR "poly_vars: "; INDENT (5, pp_vars); NL];
      pr__debug [STR "var_to_index: "; INDENT (5, pp_assoc_list_ints var_to_index); NL];
      pr__debug [STR "poly: "; NL; STR "{"; NL; INDENT (5, pp_poly); NL; STR "}"; NL];
      pr__debug [STR "interval array - excluded intervals: "; NL];
      try
	interval_array#pr__debug_large_interval_array extra_infos "     " poly_vars;
	pr__debug [NL; STR "extra_infos: "; NL;
                   extra_infos#to_pretty_no_excluded poly_vars; NL];
      with _ -> () 

  end

let bottom_poly_interval_array =
  let p = new poly_interval_array_t [] [] in
  p#set_poly bottom_poly 

let top_poly_interval_array v2const poly_vs = 
  let top_poly_int_array = 
    new poly_interval_array_t v2const poly_vs in
  let int_array = make_top_intervals (List.length poly_vs) in
  top_poly_int_array#set_interval_array int_array 

let bottom_poly_int_array = 
    let p = new poly_interval_array_t [] [] in
    p#set_poly bottom_poly 

let top_poly_int_array = 
    new poly_interval_array_t [] [] 



      



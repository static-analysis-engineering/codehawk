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
open CHBounds
open CHLanguage
open CHNonRelationalDomainValues
open CHNonRelationalDomainNoArrays
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHPrettyUtil
open CHInvStore
open CHAnalysisSetup

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

(* jchpoly *)
open JCHPolyIntervalArray
open JCHNumericInfo

let dbg = ref false 

type stub_condition_t = 
  | CheckReturnType  (* Used when extracted info from an object, such as in Unwrap *)
  | CopyInfo  of variable_t * variable_t  (* (src, dst) *)
  | JoinInfo  of variable_t * variable_t * variable_t  (* (dst, src1, src2) *)
  | PostInterval of variable_t * CHIntervals.interval_t (* var, post_interval *)
  (* For the case when an argument array or collection changes in a way that 
   * cannot be expressed *)                  
  | Abstract of variable_t                                 

let stub_condition_to_pretty extra_conds = 
  match extra_conds with 
  | CheckReturnType -> STR "CheckReturnType"   
  | CopyInfo (src, dst) ->
     LBLOCK [STR "CopyInfo "; src#toPretty; STR " "; dst#toPretty; NL] 
  | JoinInfo (src1, src2, dst) ->
     LBLOCK [STR "JoinInfo "; dst#toPretty; STR " ";
             src1#toPretty; STR " "; src2#toPretty; NL] 
  | PostInterval (var, interval) ->
     LBLOCK [STR "PostInterval "; var#toPretty; STR " "; interval#toPretty; NL] 
  | Abstract var -> LBLOCK [STR "Abstract "; var#toPretty; NL] 

(* Numeric metod summaries *)
class int_stub_t 
    ~(stub_name: symbol_t) 
    ~(vars: variable_t list)  (* list of all variables in signature *)
    
    (* list of all variables that have a length in signature *)    
    ~(vars_with_lengths:variable_t list)

    (* list of length of all the vars_with_lengths *)    
    ~(lengths : variable_t list)

    (* the numeric return variable if one exists *)    
    ~(return_var_opt:variable_t option)
    
    (* the length of the return if this is an array *)    
    ~(return_lengths_ope:variable_t option) =
object (self:_)
      
  val var_names = List.map (fun v -> v#getName#getBaseName) vars

  (* It contains the vars and the lengths of the vars in the same order *)                
  val poly_int_array_opt:poly_interval_array_t option ref = ref None  
  val extra_conds : stub_condition_t list ref = ref []

  method get_stub_name = stub_name 
  method get_vars = vars 
  method get_vars_with_lengths = vars_with_lengths
  method get_lengths = lengths
                     
  method set_poly_int_array poly_int_array = 
    poly_int_array_opt := Some poly_int_array ;
    
  method get_poly_int_array = Option.get !poly_int_array_opt

  method set_extra_conds conds = extra_conds := conds 
                               
  method get_extra_conds = !extra_conds 
                         
  method toPretty = 
    let polyp = 
      match !poly_int_array_opt with
      | Some poly_int_array ->
         LBLOCK [STR "poly_int_array:"; NL;
                 INDENT (5, poly_int_array#to_pretty) ; NL]
      | None -> STR "" in
    let condsp = 
      pretty_print_list !extra_conds stub_condition_to_pretty "" "\n" "" in
    let print_stub () = 
      LBLOCK [stub_name#toPretty; NL; 
	      STR "vars: "; pp_list vars; NL; 
	      STR "lengths: "; pp_list lengths; NL;
	      polyp; NL;  
	      STR "extra conditions: "; NL; INDENT (5, condsp); NL] in
    match !poly_int_array_opt with 
    |	Some poly_int_array -> 
	 if poly_int_array#is_bottom then 
	   LBLOCK [stub_name#toPretty; NL;
                   STR "vars: "; pp_list vars;
                   STR "lengths: "; pp_list lengths; NL; polyp; NL] 
	 else
           print_stub () 
    |	_ -> print_stub ()

end

let rec process_cond
          (stub_name:symbol_t)
          (name_vars: (string * variable_t) list)
          name_to_index
          index_to_types
          (constrs, extra_conds)
          (post: postcondition_predicate_t) = 
  try
    let constr =
      JCHLinearConstraint.mk_arg_constraint_from_post_predicate
        name_to_index index_to_types post in
    (constr :: constrs, extra_conds, true)
  with
  | Exit -> 
     match post with 
     | PostTrue ->
        process_cond
          stub_name
          name_vars
          name_to_index
          index_to_types
          (constrs, extra_conds)
	  (PostRelationalExpr (JEquals, JLocalVar (-1), JBoolConstant true))
     | PostFalse ->
        process_cond
          stub_name
          name_vars
          name_to_index
          index_to_types
          (constrs, extra_conds)
	  (PostRelationalExpr (JEquals, JLocalVar (-1), JBoolConstant false))
     | PostNewObject _ -> (constrs, extra_conds, true)
     | PostObjectClass _ -> (constrs, extra_conds, true)
     | PostNull -> (constrs, extra_conds, true)
     | PostNotNull -> (constrs, extra_conds, true)
     | PostSameCollection (JLocalVar i) 
       | PostElement (JLocalVar i) -> 
	let coll_var = List.assoc ("arg"^(string_of_int i)) name_vars in 
	let ret = List.assoc "return" name_vars in
	let extra = CopyInfo (coll_var, ret) in
	(constrs, extra :: extra_conds, true)
     | _ -> 
	pr__debug [STR "postcondition not translated "; stub_name#toPretty;
                   STR " "; postcond_preds_to_pretty [post]; NL] ;
	(constrs, extra_conds, false)


let process_side_effect
      (name_vars: (string * variable_t) list)
      name_to_index
      index_to_types
      (constrs, extra_conds)
      side = 
  match side with 
  | Wrap (term1, term2) -> 
      let constr =
	JCHLinearConstraint.mk_arg_constraint_from_post_predicate
          name_to_index
          index_to_types
	  (PostRelationalExpr (JEquals, term1, term2)) in
      (constr :: constrs, extra_conds) 
  | NumericJoin (JLocalVar i, JLocalVar j, JLocalVar k) -> 
      let argi = List.assoc ("arg"^(string_of_int i)) name_vars in 
      let argj = List.assoc ("arg"^(string_of_int j)) name_vars in 
      let argk = List.assoc ("arg"^(string_of_int k)) name_vars in 
      let extra = JoinInfo (argi, argj, argk) in
      (constrs, extra :: extra_conds) 
  | NumericAbstract (JLocalVar i) -> 
      let argi = List.assoc ("arg"^(string_of_int i)) name_vars in 
      let extra = Abstract argi in
      (constrs, extra :: extra_conds) 
  | _ -> (constrs, extra_conds)

let get_lib_stub stub_info = 
  let cmsig = stub_info#get_cms in
  let is_static = stub_info#is_static in
  let stub_name = new symbol_t cmsig#class_method_signature_string in
  let msig = cmsig#class_method_signature_data#method_signature in
  let msigd = msig#descriptor in
  let get_var_type t = 
    match t with 
    | TObject _
    | TBasic Object -> SYM_VAR_TYPE
    | _ -> NUM_VAR_TYPE in

  let args = ref [] in 
  let arg_with_lengths = ref [] in
  let arg_lengths = ref [] in
  let names = ref [] in 
  let name_to_index = ref [] in
  let index_to_types = ref [] in
  let var_count = ref 0 in
  let (return_var_opt, return_length_opt) = 
    match msigd#return_value with 
    | None
    | Some TBasic Void -> 
	args := [exception_var] ;
	names := ["throw"] ;
	name_to_index := [("throw", 0)] ;
	index_to_types := [(0, [JCHTypeUtils.get_throwable_vt ()])];
	var_count := 1;
	(None, None)
    | Some t -> 
	names := ["throw"; "return"] ;
	name_to_index := [("throw", 1); ("return", 0)] ;
	index_to_types := [(1, [JCHTypeUtils.get_throwable_vt ()]); (0, [t])] ;
	var_count := 2 ;
	let rec is_num t = 
	  match t with 
	  | TObject TClass cn -> Option.is_some (JCHTypeUtils.get_numeric_type cn)
	  | TObject TArray vt -> is_num vt
	  | TBasic Object -> false
	  | _ -> true in
	if is_num t then 
	  begin
	    let v = num_return_var in
	    args := [exception_var; v] ;
	    if JCHTypeUtils.is_type_with_length t then 
	      begin
		arg_with_lengths := [v] ;
		let length_v = JCHSystemUtils.make_length v in
		arg_lengths := [length_v] ;
		(Some v, Some length_v)
	      end
	    else (Some v, None)
	  end
	else 
	  begin
	    args := [exception_var; sym_return_var] ;
	    if JCHTypeUtils.is_type_with_length t then 
	      begin
		arg_with_lengths := [sym_return_var] ;
		let length_v = JCHSystemUtils.make_length sym_return_var in
		arg_lengths := [length_v] ;
		(None, Some length_v)
	      end
	    else (None, None)
	  end in
  
  let number = ref 0 in (* argument index *) 
  if is_static then
    ()
  else 
    begin
      let name = "arg0" in
      let var = make_variable name SYM_VAR_TYPE in
      args := var :: !args ; 
      names := name :: !names ;
      name_to_index := (name, !var_count) :: !name_to_index ;
      let cn = cmsig#class_name in
      index_to_types := (!var_count, [TObject (TClass cn)]) :: !index_to_types ;
	if JCHTypeUtils.is_class_with_length cn then 
	  begin
	    arg_with_lengths := var :: !arg_with_lengths;
	    let arg_length = JCHSystemUtils.make_length var in
	    arg_lengths := arg_length :: !arg_lengths ;
	  end ;
      incr number ;
      incr var_count 
    end ;
  
  let rec addArg types = 
    match types with 
    | t :: rest_types -> 
	let name = "arg"^(string_of_int !number) in
	let var = make_variable name (get_var_type t) in
	args := var :: !args ; 
	names := name :: !names ;
	name_to_index := (name, !var_count) :: !name_to_index ;
	index_to_types := (!var_count, [t]) :: !index_to_types ;
	if JCHTypeUtils.is_type_with_length t then 
	  begin
	    arg_with_lengths := var :: !arg_with_lengths;
	    let arg_length = JCHSystemUtils.make_length var in
	    arg_lengths := arg_length :: !arg_lengths ;
	  end ;
	incr number ;
	incr var_count ;
	addArg rest_types
    | [] -> () in
  addArg msigd#arguments ;
  
  let vars_with_lengths = List.rev !arg_with_lengths in
  let lengths = List.rev !arg_lengths in
  let vars = List.rev !args in

  let add_len var_with_length = 
    let name = "length_" ^ var_with_length#getName#getBaseName in
    names := name :: !names ;
    name_to_index := (name, !var_count) :: !name_to_index;
    index_to_types := (!var_count, [TBasic Int]) :: !index_to_types in
  List.iter add_len vars_with_lengths ;

  let names = List.rev !names in
  let name_to_index = List.rev !name_to_index in
  let index_to_types = List.rev !index_to_types in
  let name_vars = List.combine names (vars @ lengths) in

  let unknown_condition = ref false in
  let add_post (constrs, extra_conds) post = 
    let (new_constrs, new_extra_conds, processed) = 
      process_cond
        stub_name
        name_vars
        name_to_index
        index_to_types
        (constrs, extra_conds)
        post#get_predicate in
    if not processed then 
      begin
	unknown_condition := true ;
	raise (JCH_failure (STR "condition not parsed")) 
      end
    else
      (new_constrs, new_extra_conds) in
  let (constrs, extra_conds) = 
    try
      List.fold_left add_post ([], []) stub_info#get_post
    with _ -> ([], []) in
  let (error_constrs, extra_conds) = 
    try
      List.fold_left add_post ([], extra_conds) stub_info#get_error_post
    with _ -> ([], []) in

  let add_side (constrs, extra_conds) side = 
    process_side_effect
      name_vars
      name_to_index
      index_to_types
      (constrs, extra_conds)
      side in
  let (constrs, extra_conds) = 
    if !unknown_condition then
      ([], []) 
    else
      List.fold_left add_side (constrs, extra_conds) stub_info#get_sideeffects in

  let add_safety_cond res (exception_info: exception_info_int) = 
    if exception_info#has_safety_condition then 
      begin
	let add_safety (constrs, extra_conds) scond = 
	  let post = JCHNumericUtils.pre_to_post_predicate scond in
	  let (new_constrs, new_extra_conds, processed) =
            process_cond
              stub_name
              name_vars
              name_to_index
              index_to_types
              (constrs, extra_conds)
              post in
	  (new_constrs, new_extra_conds) in
	let (constrs, _) =
          List.fold_left add_safety ([], []) exception_info#get_safety_condition in
	constrs
      end 
    else
      res in
  let safety_constrs =
    List.fold_left add_safety_cond [] stub_info#get_exception_infos in

  let poly = JCHPoly.mk_poly_from_constraints true (safety_constrs @ constrs) in

  let add_error_constr p constr = 
    let error_poly = JCHPoly.mk_poly_from_constraints false [constr] in
    let res = p#join error_poly in
    res in
  let poly = List.fold_left add_error_constr poly error_constrs in 

  let top_poly_int_array = top_poly_interval_array [] (vars @ lengths) in
  let all_poly_int_array = top_poly_int_array#set_poly poly in
  let restr_poly_int_array = all_poly_int_array#move_simple_ineqs in

  let stub = new int_stub_t stub_name vars vars_with_lengths lengths return_var_opt return_length_opt in 
  stub#set_poly_int_array restr_poly_int_array ;
  stub#set_extra_conds extra_conds ;
  stub
  

class call_t
        (proc_name: symbol_t)
        (jproc_info: JCHProcInfo.jproc_info_t)
        (vars: variable_t list)
        (length_vars: variable_t list)
        (length_to_array: variable_t VariableCollections.table_t) = 
  object (self: 'a)

    val poly_int_array_opt : poly_interval_array_t option ref = ref None

    (* calls from within the method itself *)                                                              
    val rec_poly_int_array_opt : poly_interval_array_t option ref = ref None 
    val widening_poly_int_array_opt : poly_interval_array_t option ref = ref None 

    method get_all_vars = (vars, length_vars, length_to_array)

    method get_widening_poly_int_array_opt use_widening = 
      match (!widening_poly_int_array_opt, !rec_poly_int_array_opt) with 
      |	(Some widening_poly_int_array, Some rec_poly_int_array) ->
         begin
	   widening_poly_int_array_opt := 
	     Some (if use_widening then
                     widening_poly_int_array#simple_widening rec_poly_int_array
	           else
                     widening_poly_int_array#simple_join rec_poly_int_array) ;
	   !widening_poly_int_array_opt
         end
      |	(None, Some rec_poly_int_array) -> 
	  begin
	    match !poly_int_array_opt with 
	    | Some poly_int_array ->
               begin
		 widening_poly_int_array_opt := 
		   Some (if use_widening then
                           poly_int_array#simple_widening rec_poly_int_array
		         else
                           poly_int_array#simple_join rec_poly_int_array) ;
		 !widening_poly_int_array_opt
               end
	    | _ -> None
	  end
      |	_ -> !poly_int_array_opt 

    method get_narrowing_poly_int_array_opt = 
      match (!poly_int_array_opt, !rec_poly_int_array_opt) with 
      |	(Some poly_int_array, Some rec_poly_int_array) -> 
	  Some (poly_int_array#simple_join rec_poly_int_array)
      |	(Some poly_int_array, None) -> Some poly_int_array
      |	(None, _) -> None
      
    method are_rec_calls_included_in_calls = 
      match (!widening_poly_int_array_opt, !rec_poly_int_array_opt) with 
      |	(Some widening_poly_int_array, Some rec_poly_int_array) ->
	  rec_poly_int_array#leq widening_poly_int_array 
      |	(Some widening_poly_int_array, None) ->
	  widening_poly_int_array#is_top
      |	_ -> true

    method reset_rec_poly_int_array = 
      rec_poly_int_array_opt := None ;

    method get_rec_poly_int_array = 
      match !rec_poly_int_array_opt with 
      |	Some poly_int_array -> poly_int_array
      |	None -> top_poly_int_array

    method add_poly_int_array
             caller_proc_name
             (caller_poly_int_array:poly_interval_array_t) = 
      if proc_name#equal caller_proc_name then 
	begin
	  match !rec_poly_int_array_opt with 
	  | Some rec_old_poly_int_array -> 
	      rec_poly_int_array_opt := 
		let p = caller_poly_int_array#change_vars caller_proc_name proc_name vars length_vars in
		let p = p#add_intervals_to_poly in
		let typed_p = p#set_type_intervals_and_restrict jproc_info (vars @ length_vars) in
		let typed_p = typed_p#move_simple_ineqs in
		Some (rec_old_poly_int_array#simple_join typed_p) 
	  | None -> 
	      rec_poly_int_array_opt := 
		let p = caller_poly_int_array#change_vars caller_proc_name proc_name vars length_vars in
		let p = p#add_intervals_to_poly in
		let typed_p = p#set_type_intervals_and_restrict jproc_info (vars @ length_vars) in
		let typed_p = typed_p#move_simple_ineqs in
		Some typed_p
	end 
      else 
	begin
	  match !poly_int_array_opt with 
	  | Some old_poly_int_array -> 
	      poly_int_array_opt := 
		let p = caller_poly_int_array#change_vars caller_proc_name proc_name vars length_vars in
		let p = p#add_intervals_to_poly in
		let typed_p = p#set_type_intervals_and_restrict jproc_info (vars @ length_vars) in
		let typed_p = typed_p#move_simple_ineqs in
		Some (old_poly_int_array#simple_join typed_p)
	  | None -> 
	      poly_int_array_opt := 
		let p = caller_poly_int_array#change_vars caller_proc_name proc_name vars length_vars in
		let p = p#add_intervals_to_poly in
		let typed_p = p#set_type_intervals_and_restrict jproc_info (vars @ length_vars) in
		let typed_p = typed_p#move_simple_ineqs in
		Some typed_p
	end ;
      if !dbg then
        pr__debug [STR "after add_poly_int_array for "; proc_name#toPretty;
                   STR " caller: "; caller_proc_name#toPretty; NL; self#toPretty; NL] ;

    method toPretty = 
      let varspp = LBLOCK [STR "vars: "; pp_list vars; NL] in
      let lengthspp =
        if length_vars = [] then
          STR ""
        else
          LBLOCK [STR "length_to_array: "; length_to_array#toPretty; NL] in

      let poly_int_array_pp str poly_opt = 
	match poly_opt with
	| Some poly_int_array -> 
	    LBLOCK [STR (str ^ ": "); NL; INDENT(5, poly_int_array#to_pretty) ; NL]
	| None ->
	    LBLOCK [STR (str ^ ": None"); NL] in
      let poly_pp = poly_int_array_pp "poly_int_array" !poly_int_array_opt in
      let rec_poly_pp =
        poly_int_array_pp "rec_poly_int_array" !rec_poly_int_array_opt in
      let wid_poly_pp =
        poly_int_array_pp "widening_poly_int_array" !widening_poly_int_array_opt in

      LBLOCK [proc_name#toPretty; NL;
              INDENT(5, LBLOCK [varspp; lengthspp; poly_pp; rec_poly_pp; wid_poly_pp]) ]
  end

module FunctionSummaryCollections = CHCollections.Make
    (struct 
      type t = function_summary_int 
      let compare s1 s2 = compare s1#get_cms#index 
	  s2#get_cms#index
      let toPretty s = s#toPretty
    end)
	
class int_stub_manager_t = 
object (self: _) 
    val stub_map : int_stub_t SymbolCollections.table_t ref =
      ref (new SymbolCollections.table_t)
    val lib_stub_table = new FunctionSummaryCollections.table_t
    val call_map = ref (new SymbolCollections.table_t) (* proc -> call poly *)
    val new_call_map = ref (new SymbolCollections.table_t) 

    method get_lib_func_summaries = lib_stub_table#listOfKeys
    method get_lib_stubs = lib_stub_table#listOfValues

    method private get_stub_p (procedure:procedure_int) = 
      let proc_name = procedure#getName in
      let res = 
        match !stub_map#get proc_name with 
        | Some stub -> stub
        | None -> 
	   let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
	   let bind_vars = JCHSystemUtils.get_signature_vars procedure in
	   let (bind_lengths, bind_arrays, _) =
             JCHAnalysisUtils.get_length_vars jproc_info bind_vars in
	   let (ret_var, ret_length_var)  = 
	     try 
	       let (_, ret) =
                 List.find (fun (s,_) ->
                     s#getBaseName = "return") procedure#getBindings in
	       let v = 
		 if JCHAnalysisUtils.is_numeric jproc_info ret then
                   Some ret
		 else
                   None in
	       let l_v = jproc_info#get_length ret in
	       (v, l_v) 
	     with _ -> (None, None) in 
	   let stub =
             new int_stub_t
                 proc_name bind_vars bind_arrays bind_lengths ret_var ret_length_var in 
	   !stub_map#set proc_name stub ;
	   stub in
      
      if !dbg then
        pr__debug [STR "get_stub_p "; proc_name#toPretty; NL; res#toPretty; NL];
      res

    method mk_poly_int_array_stub (procedure: procedure_int) restr_poly_int_array = 
      let stub = self#get_stub_p procedure in 
      stub#set_poly_int_array restr_poly_int_array 

    method mk_lib_stub stub_info = 
      match lib_stub_table#get stub_info with 
      | Some stub -> stub
      | None -> 
	 let stub = get_lib_stub stub_info in
         begin
	   lib_stub_table#set stub_info stub ;
	   stub
         end

    method mk_proc_call proc = 
      let proc_name = proc#getName in
      let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
      let vars = JCHSystemUtils.get_signature_read_vars proc in
      let (length_vars, array_vars, length_to_array) =
        JCHAnalysisUtils.get_length_vars jproc_info vars in
      let call = new call_t proc_name jproc_info vars length_vars length_to_array in
      !new_call_map#set proc_name call 
      
    method private get_call proc_name = 
      Option.get (!new_call_map#get proc_name)

    method get_all_call_vars invoked_proc_name = 
      let call = self#get_call invoked_proc_name in
      call#get_all_vars

    method record_poly_int_array_call
             caller_proc_name invoked_proc_name caller_poly_int_array =
      
      if !dbg then
        pr__debug [STR "record_poly_int_array_call "; caller_proc_name#toPretty;
                   STR " "; invoked_proc_name#toPretty; NL;
                   caller_poly_int_array#toPretty; NL] ;
      
      if caller_poly_int_array#is_bottom then
        () 
      else 
	begin
	  let call = self#get_call invoked_proc_name in
	  if !dbg then pr__debug [STR "call = "; call#toPretty; NL];
	  call#add_poly_int_array caller_proc_name caller_poly_int_array ;
	end

    method invoke_poly_int_array
             (jproc_info:JCHProcInfo.jproc_info_t)
             (proc_names: symbol_t list)
             (stub_infos: function_summary_int list) =
      if !dbg then pr__debug [STR "invoke_poly_int_array "; NL] ;
      if List.exists (fun n -> not (!stub_map#has n)) proc_names then
	(None, [], [],  None, [], [], [])
      else 
	begin
	  let invoke_one_p
                (res_poly_int_array_opt, res_vars, res_vars_with_lengths, res_lengths)
                (proc_name:symbol_t) =
            
	    if !dbg then
              pr__debug [STR "IntStubs.invoke_one_p "; proc_name#toPretty; NL] ;
            
	    let stub = Option.get (!stub_map#get proc_name) in
            
	    if !dbg then pr__debug [stub#toPretty; NL];
            
	    let poly_int_array = stub#get_poly_int_array in
	    match res_poly_int_array_opt with 
	    | Some res_poly_int_array ->
		if res_poly_int_array#is_bottom then
		  (Some poly_int_array,
                   stub#get_vars,
		   VariableCollections.set_of_list
                     stub#get_vars_with_lengths,
                   VariableCollections.set_of_list stub#get_lengths)
		else if poly_int_array#is_bottom then
		  (Some res_poly_int_array,
                   res_vars,
                   res_vars_with_lengths,
                   res_lengths)
		else
		  begin
		    let p_vars_with_lengths =
                      VariableCollections.set_of_list stub#get_vars_with_lengths in
		    let p_lengths =
                      VariableCollections.set_of_list stub#get_lengths in
		    let new_vars_with_lengths =
                      res_vars_with_lengths#inter p_vars_with_lengths in
		    let new_lengths = res_lengths#inter p_lengths in
		    let remaining_vars = res_vars @ new_lengths#toList in
		    let restricted_res_poly_int_array =
		      if new_lengths#size < res_lengths#size then
			res_poly_int_array#restrict_to_vars_2 remaining_vars
		      else res_poly_int_array in
                    
		    if !dbg then
                      pr__debug [STR "restricted_res_poly_int_array ";
                                 pp_list remaining_vars; NL;
				 restricted_res_poly_int_array#toPretty; NL] ;
                    
		    let restricted_poly_int_array =
		      if new_lengths#size < p_lengths#size then 
			poly_int_array#restrict_to_vars_2 remaining_vars 
		      else
                        poly_int_array in
		    if !dbg then
                      
                      pr__debug [STR "restricted_poly_int_array ";
                                 pp_list remaining_vars; NL;
				 restricted_poly_int_array#toPretty; NL] ;
                    
		    (Some (restricted_res_poly_int_array#join restricted_poly_int_array),
                     res_vars, new_vars_with_lengths, new_lengths)
		  end
	    | _ ->
	       (Some poly_int_array,
                stub#get_vars,
		VariableCollections.set_of_list stub#get_vars_with_lengths,
                VariableCollections.set_of_list stub#get_lengths) in
	  let (proc_p, proc_vs, proc_vls, _) =
	    List.fold_left
              invoke_one_p
              (None, [], new VariableCollections.set_t, new VariableCollections.set_t)
	      proc_names in

	  let invoke_one_s
                ((res_poly_int_array_opt, res_vars, res_vars_with_lengths, res_lengths), res_conds)
                stub_info =
            
	    if !dbg then pr__debug [STR "invoke_one_s "; NL] ;
            
	    let stub = self#mk_lib_stub stub_info in
            
	    if !dbg then pr__debug [stub#toPretty; NL];
            
	    let poly_int_array = stub#get_poly_int_array in
	    match res_poly_int_array_opt with 
	    | Some res_poly_int_array -> 
		if res_poly_int_array#is_bottom then
		  ((Some poly_int_array,
                    stub#get_vars,
		    VariableCollections.set_of_list stub#get_vars_with_lengths,
                    VariableCollections.set_of_list stub#get_lengths),
		   stub#get_extra_conds)
		else if poly_int_array#is_bottom then
		  ((Some res_poly_int_array,
                    res_vars,
                    res_vars_with_lengths,
                    res_lengths), res_conds) 
		else
		  begin
                    (* Conditions are assumed to be the same for different stubs *)                    
		    let all_conds = stub#get_extra_conds @ res_conds in  
		    let p_vars_with_lengths =
                      VariableCollections.set_of_list stub#get_vars_with_lengths in
		    let p_lengths = VariableCollections.set_of_list stub#get_lengths in
		    let new_vars_with_lengths =
                      res_vars_with_lengths#inter p_vars_with_lengths in
		    let new_lengths = res_lengths#inter p_lengths in
		    let remaining_vars = res_vars @ new_lengths#toList in
		    let restricted_res_poly_int_array =
		      if new_lengths#size < res_lengths#size then 
			res_poly_int_array#restrict_to_vars_2 remaining_vars
		      else
                        res_poly_int_array in
                    
		    if !dbg then
                      pr__debug [STR "restricted_res_poly_int_array ";
                                 pp_list remaining_vars; NL;
				 restricted_res_poly_int_array#toPretty; NL] ;
                    
		    let restricted_poly_int_array =
		      if new_lengths#size < p_lengths#size then 
			poly_int_array#restrict_to_vars_2 remaining_vars
		      else
                        poly_int_array in
                    
		    if !dbg then
                      pr__debug [STR "restricted_poly_int_array ";
                                 pp_list remaining_vars; NL;
				 restricted_poly_int_array#toPretty; NL] ;
                    
		    ((Some (restricted_res_poly_int_array#join restricted_poly_int_array),
                      res_vars, new_vars_with_lengths, new_lengths), all_conds)
		  end
	    | _ ->
	       ((Some poly_int_array,
                 stub#get_vars,
		 VariableCollections.set_of_list stub#get_vars_with_lengths,
                 VariableCollections.set_of_list stub#get_lengths),
		stub#get_extra_conds) in

	  let ((stub_p, stub_vs, stub_vls, _), stub_conds) =
	    List.fold_left
              invoke_one_s
              ((None, [], new VariableCollections.set_t, new VariableCollections.set_t), [])
	      stub_infos in
	  (proc_p, proc_vs, proc_vls#toList, stub_p, stub_vs, stub_vls#toList, stub_conds)
	end

    method get_stub proc_name = 
      !stub_map#get proc_name 

    method get_widening_call_poly_int_array use_widening proc_name use_new =
      
      if !dbg then
        pr__debug [STR ("get_widening_call_poly_int_array use_widening = "
                        ^ (if use_widening then "true " else "false "));
		   proc_name#toPretty;
                   STR ("use_new = " ^ (if use_new then "true " else "false ")); NL] ;
      
      let map = if use_new then !new_call_map else !call_map in
      match map#get proc_name with 
      |	Some call -> call#get_widening_poly_int_array_opt use_widening
      |	None -> None

    method get_narrowing_call_poly_int_array proc_name use_new =
      
      if !dbg then
        pr__debug [STR "get_narrowing_call_poly_int_array ";
		   proc_name#toPretty; STR ("use_new = "
                                            ^ (if use_new then "true " else "false ")); NL] ;			       
      let map = if use_new then !new_call_map else !call_map in
      match map#get proc_name with 
      |	Some call -> call#get_narrowing_poly_int_array_opt
      |	None -> None

    method are_recursive_calls_included_in_calls proc_name = 
      let call = self#get_call proc_name in
      call#are_rec_calls_included_in_calls
	    
    method reset_calls =
      if !dbg then pr__debug [STR "reset_calls"; NL] ;
      call_map := !new_call_map ;
      new_call_map := new SymbolCollections.table_t 

    method reset_recursive_calls proc_name = 
      let call = self#get_call proc_name in
      call#reset_rec_poly_int_array;

    method toPretty = 
      LBLOCK [NL; NL; 
	      STR "int_stub_map: "; NL; !stub_map#toPretty; NL; 
	      STR "lib_stub_table: "; NL; lib_stub_table#toPretty; NL;
	      STR "call_map: "; NL; !call_map#toPretty; NL;
	      STR "new_call_map: "; NL; !new_call_map#toPretty; NL]
      
  end

let int_stub_manager = new int_stub_manager_t


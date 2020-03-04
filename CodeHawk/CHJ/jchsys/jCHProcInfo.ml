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
open CHPretty
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils
open JCHVarInfo

let dbg = ref false 

class scope_t (* (orig_var: variable_t) *)
        ~(first_pc: int)
        ~(last_pc: int)
        ~(types: value_type_t list)
        ~(index: int)
        ~(vars: VariableCollections.set_t) = 
  object (self: 'a) 
    val first_pc = ref first_pc
    val last_pc = ref last_pc
    val types = ref types
    val vars = ref vars

    method get_first_pc = !first_pc
    method get_last_pc = !last_pc
    method get_types = !types 
    method get_index = index
    method get_vars = !vars
	
    method set_vars vs = vars := vs
    method set_types ts = types := ts

    method private is_in pc = 
      pc >= !first_pc && pc <= !last_pc

    method overlaps (s: 'a) = 
      index = s#get_index && 
      (self#is_in s#get_first_pc || self#is_in s#get_last_pc)

    method private union_types
                     (types1:value_type_t list)
                     (types2:value_type_t list) = 
      let add_type types vt = 
	if List.exists (fun t -> compare_value_types vt t = 0) types1 then
          types
        else
          vt :: types in
      List.fold_left add_type types1 types2

    method union (s: 'a) = 
      {< first_pc = ref (min !first_pc s#get_first_pc) ;
	 last_pc = ref (max !last_pc s#get_last_pc) ;
	 types = ref (self#union_types !types s#get_types) ;
	 vars = ref (!vars#union s#get_vars) >}

    method union_keep_vars (s: 'a) = 
      {< first_pc = ref (min !first_pc s#get_first_pc) ;
	 last_pc = ref (max !last_pc s#get_last_pc) ;
	 types = ref (self#union_types !types s#get_types) >}

    method decrease_first_pc pc = 
      if pc < !first_pc then first_pc := pc

    method increase_last_pc pc = 
      if pc > !last_pc then last_pc := pc

    (* sorted_scopes have to be sorted increasingly in the order of first_pc
     * It increases the scope of the corresponding write scope *)
    method add_to_list (sorted_scopes: 'a list) =
      let rec find_scope (prev_scope:'a option) (scopes:'a list) = 
	match scopes with 
	| scope :: rest_scopes -> 
	   if scope#get_first_pc > !first_pc then
             prev_scope
	   else
             find_scope (Some scope) rest_scopes
	| [] -> prev_scope in
      match find_scope None sorted_scopes with
      (* It's possible that there is no write before the read *)
      |	Some scope ->
         begin
	   scope#increase_last_pc !last_pc ;
	   scope#set_types (self#union_types !types scope#get_types) ;
	   scope#set_vars (!vars#union scope#get_vars)
         end
      |	_ -> 
	 let scope = List.hd sorted_scopes in
         begin
	   scope#decrease_first_pc !first_pc ;
	   scope#set_types (self#union_types !types scope#get_types) ;
	   scope#set_vars (!vars#union scope#get_vars)
         end

    method make_var_table_line (opcodes:opcodes_int) (mInfo:method_info_int) = 
      let first_pc =
        if !first_pc <= 0 then
          0
        else 
          try
	    Option.get (opcodes#next !first_pc) 
          with _ -> !first_pc in
      let last_pc = 
	if !last_pc = -1 then
          0 
	else if !last_pc < first_pc then
          first_pc 
	else
          !last_pc in 
      let name = 
	let name = mInfo#get_local_variable_name index last_pc in
	match name with 
	| "none" -> mInfo#get_local_variable_name index first_pc 
	| _ -> name in
      (first_pc, last_pc, name, JCHTypeUtils.get_compact_type !types, index)

    method toPretty = 
      LBLOCK [ STR "scope "; INT index ; STR " "; !vars#toPretty ; STR " ["; 
	       INT !first_pc; STR "; "; INT !last_pc;  
	       pretty_print_list !types value_type_to_pretty "] {" ", " "}" ;
               NL ] 
  
  end
  
module ScopeCollections = CHCollections.Make
    (struct 
      type t = scope_t
      let compare (s1: scope_t) (s2: scope_t) = 
	let n = s1#get_index - s2#get_index in
	if n = 0 then 
	  let m = s1#get_first_pc - s2#get_first_pc in
	  if m = 0 then 
	    s1#get_last_pc - s2#get_last_pc 
	  else m
	else n 
      let toPretty s = s#toPretty
    end)


class pc_analysis_results_t =
object (self: 'a)
     
  val invariants = ref []

  (* (var, untrusted_origin_set, unknown_origin_set) list *)                 
  val taint_origins = ref [] 
	
  method set_invariants (invs: relational_expr_t list) = 
    invariants := invs
    
  method get_invariants = !invariants 

  method set_taint_origins (origs: (variable_t * taint_origin_set_int) list) = 
    taint_origins := origs
    
  method get_taint_origins = !taint_origins

  method toPretty = 
    let pp_invariants = 
      let pp_rel (op, t1, t2) = 
	LBLOCK [ STR "     "; jterm_to_pretty t1; 
		 STR (" "^ (relational_op_to_string op) ^ " "); 
		 jterm_to_pretty t2; NL ] in
	LBLOCK (List.map pp_rel !invariants) in
      let pp_taints = 
	let pp_taint (v, untrusted) =
	  LBLOCK [ STR "     ";
                   v#toPretty; STR "("; untrusted#toPretty; STR ")"; NL ] in
	LBLOCK (List.map pp_taint !taint_origins) in
      LBLOCK [pp_invariants; pp_taints] 
      
end

class analysis_results_t = 
object (self: 'a)
     
  val pc_to_res = new IntCollections.table_t (* pc -> pc_analysis_results *)
                
  val return_origins = ref None
	             
  method get_pc_analysis_results = pc_to_res
                                 
  method get_return_origins = !return_origins

  method set_invariants (pc:int) (invs:relational_expr_t list) = 
    let res = 
      match pc_to_res#get pc with 
      |	Some res -> res
      |	_ -> 
	 let res = new pc_analysis_results_t in
         begin
	   pc_to_res#set pc res ;
	   res
         end in
    res#set_invariants invs 

  method set_taint_origins
           (pc:int) (origs:(variable_t * taint_origin_set_int) list) = 
    match pc_to_res#get pc with
    | Some res -> 
       res#set_taint_origins origs
    | _ -> 
       let res = new pc_analysis_results_t in
       begin
         res#set_taint_origins origs ;
         pc_to_res#set pc res
       end
       
  method set_return_origins (untrusted_origins: taint_origin_set_int) =
    return_origins := Some (untrusted_origins)

  method toPretty = 
    let pp_return_origins = 
      match !return_origins with 
      | Some (untrusted) -> LBLOCK [STR "return taint: "; untrusted#toPretty]
      | _ -> STR "" in
    LBLOCK [STR "analysis results: "; NL; pc_to_res#toPretty; pp_return_origins; NL] 
end

class jproc_info_t
    ~(proc_name: symbol_t)
    ~(proc: procedure_int)
    ~(wto: CHSCC.wto_t)          (* wto of the method *)
    (* wto_info's for all the loops, including inner loops *)
    ~(wto_infos: JCHLoopUtils.wto_info_t list)         
    ~(loop_depth: int)         (* maximum loop depth *)
    ~(pc_to_instr: int -> int)  (* instruction offset -> istruction number *) 
    ~(instr_to_pc: int -> int) =  (* instruction number -> instruction offset *)
  object (self: 'a) 
      
    val jvar_infos : jvar_info_t VariableCollections.table_t ref =
      ref (new VariableCollections.table_t)
      
    val cms = retrieve_cms proc_name#getSeqNumber
            
    val meth = (app#get_method (retrieve_cms proc_name#getSeqNumber))#get_method
             
    val mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber)
              
    val bytecode = 
      let mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber) in
      if mInfo#has_bytecode then mInfo#get_bytecode else
	raise (JCH_failure (STR "expected bytecode"))
      
    val var_to_var_to_eqs = ref None (* x -> y -> states where ASSERT x = y *)

    (* x -> y -> states where ASSERT x < y or x <= y *)                          
    val var_to_var_to_ineqs = ref None

    (* number of variables that could carry numeric info such as int, long, ...,
     * java.lang.Integer, ..., java.util.Collections, ..., java.lang.Object *)                            
    val numeric_vars = ref 0
                     
    val number_vars = ref 0 (* number of variables that have _num suffix *)

    (* obtained from the local variable table or constructed if this is not 
     * available : first instr * last instr * types * index *)                    
    val var_table = ref []
                  
    val analysis_results = new analysis_results_t
                         
    method get_analysis_results = analysis_results 
    method get_name = proc_name 
    method get_method = meth
    method get_method_info = mInfo
    method get_procedure = proc
    method get_cfg = JCHSystemUtils.get_CFG proc
    method get_wto_infos = wto_infos
    method get_wto = wto
    method get_loop_depth = loop_depth
    method get_loop_number = List.length wto_infos 
    method get_pc_to_instr = pc_to_instr
    method get_instr_to_pc = instr_to_pc
    method get_jvar_infos = !jvar_infos
    method get_jvar_info v = Option.get (!jvar_infos#get v)
    method get_bytecode = bytecode 
    method get_opcodes = bytecode#get_code
    method get_variables = proc#getScope#getVariables
    method get_var_to_var_to_eqs = Option.get !var_to_var_to_eqs 
    method get_var_to_var_to_ineqs = Option.get !var_to_var_to_ineqs 
    method get_count_numeric_vars = !numeric_vars 
    method get_count_number_vars = !number_vars
    method get_var_table = !var_table
    method get_source_origin = (app#get_class cms#class_name)#get_source_origin

    method set_var_table
             (table:(int * int * string * value_type_t list * int) list) =
      var_table := table
      
    method has_orig_var_table = 
      Option.is_some bytecode#get_local_variable_table 

    (* It makes sets of local variables that are connected via phi variables
     * Such variables will get a single line in the local variable table *) 
    method private group_local_vars
                     (aliases:JCHTransformUtils.alias_sets_t)
                     (orig_phi_to_vars: VariableCollections.set_t VariableCollections.table_t) =
      let var_to_rep = new VariableCollections.table_t in
      let rep_to_vars = new VariableCollections.table_t in
      let consts = new VariableCollections.set_t in
      let const_to_phis = new VariableCollections.table_t in

      let add_var (var:variable_t) (var_info:jvar_info_t) = 
	if var_info#is_local_var then 
	  begin
	    if (List.length var_info#get_local_indices) = 1 then
              (* The constant versions are omitted if they correspond to 
               * multiple registers *) 
	      begin
		var_to_rep#set var var ;
		rep_to_vars#set var (VariableCollections.set_of_list [var]) 
	      end
	    else
              consts#add var 
	  end in
      !jvar_infos#iter add_var ;
      
      (* Add the original SSA variables that were aliased to a constant local 
       * variable *)
      let representatives = aliases#get_representatives in
      let add_consts (orig_var:variable_t) (rep:variable_t) = 
	if JCHSystemUtils.is_register orig_var then 
	  begin
	    match !jvar_infos#get rep with 
	    | Some jvar_info -> 
	       if jvar_info#is_local_var
                  && Option.is_some jvar_info#get_constant then 
		  begin
		    var_to_rep#set orig_var orig_var ;
		    rep_to_vars#set
                      orig_var (VariableCollections.set_of_list [orig_var]) 
		  end
	    | _ -> () 
	  end in
      
      representatives#iter add_consts ;

      let add_const_to_phis
            (orig_phi: variable_t) (orig_vars: VariableCollections.set_t) = 
	if JCHSystemUtils.is_register orig_phi then 
	  match aliases#get_representative orig_phi with
	  | Some phi -> 
	      let add_const orig_var = 
		if JCHSystemUtils.is_register orig_var then 
		  match aliases#get_representative orig_var with 
		  | Some var -> 
		     begin
		       match !jvar_infos#get var with 
		       | Some jvar_info -> 
			  if jvar_info#is_local_var
                             && Option.is_some jvar_info#get_constant then 
			    begin
			      var_to_rep#set orig_var orig_var ;
			      rep_to_vars#set
                                orig_var (VariableCollections.set_of_list [orig_var]) ;
			      match const_to_phis#get orig_var with 
			      | Some set -> set#add phi
			      | _ -> const_to_phis#set
                                       orig_var (VariableCollections.set_of_list [phi])
			    end
		       | _ -> () 
		     end
		  | _ -> () in
	      orig_vars#iter add_const ;
	  | _ -> () in
      
      orig_phi_to_vars#iter add_const_to_phis ;

      let add_connection (var1:variable_t) (var2:variable_t) = 
	try  
	  let rep1 = Option.get (var_to_rep#get var1) in
	  let rep2 = Option.get (var_to_rep#get var2) in
	  if rep1#getIndex <> rep2#getIndex then 
	    let set1 = Option.get (rep_to_vars#get rep1) in
	    let set2 = Option.get (rep_to_vars#get rep2) in
            begin
	      rep_to_vars#set rep1 (set1#union set2) ;
	      set2#iter (fun v -> var_to_rep#set v rep1) ;
	      rep_to_vars#remove rep2 ;
	    end 
	with _ -> () in
      let add_connections (var:variable_t) = 
	match !jvar_infos#get var with 
	| Some jvar_info -> 
	    if jvar_info#is_phi then 
	      let is_non_const (var:variable_t) = 
		Option.is_none
                  ((Option.get (!jvar_infos#get var))#get_constant) in
	      List.iter
                (add_connection var)
                (List.filter is_non_const jvar_info#get_read_vars) 
	| _ -> 
	    begin
	      match const_to_phis#get var with 
	      |	Some phis -> phis#iter (fun phi -> add_connection phi var) 
	      |	_ -> () 
	    end in
      
      List.iter add_connections (var_to_rep#listOfKeys) ; 
      var_to_rep
	    
    method set_var_infos
             ~(chif:system_int)
             ~(dom_info:JCHDominance.dominance_info_t)
             ~(aliases:JCHTransformUtils.alias_sets_t)
             ~(extra_assert_vars:SymbolCollections.set_t  VariableCollections.table_t) =
      let cfg = JCHSystemUtils.get_CFG proc in
      let opcodes = bytecode#get_code in
      let lc_to_pc:(variable_t * int) list =
        List.map
          (fun wto_info -> (wto_info#get_var, wto_info#get_entry_pc))
          wto_infos in
      let (var_infos,
           v_to_v_to_eqs,
           v_to_v_to_ineqs,
           nvars1,
           nvars2,
           local_var_index_to_pc_to_var) = 
	make_jvar_infos
          ~chif
          ~meth
          ~proc
          ~cfg
          ~opcodes
          ~lc_to_pc
          ~wto
          ~dom_info
          ~aliases
          ~extra_assert_vars in
      begin
        jvar_infos := var_infos ;
        var_to_var_to_eqs := Some v_to_v_to_eqs ;
        var_to_var_to_ineqs := Some v_to_v_to_ineqs ;
        numeric_vars := nvars1 ;
        number_vars := nvars2 ;
        local_var_index_to_pc_to_var
      end
      
    method private make_local_variable_table
                     ~(aliases:JCHTransformUtils.alias_sets_t) 
	             ~(rvar_to_pc_to_versions:VariableCollections.set_t
                                             IntCollections.table_t
                                             VariableCollections.table_t)
	             ~(orig_phi_to_vars:VariableCollections.set_t
                                       VariableCollections.table_t) 
	             ~(local_var_index_to_pc_to_var:
                        variable_t IntCollections.table_t IntCollections.table_t) =
      let index_to_scopes = new IntCollections.table_t in
      let get_rep var = 
	match aliases#get_representative var with 
	| Some rep -> rep
	| _ -> var in 
      let var_to_rep = self#group_local_vars aliases orig_phi_to_vars in

      let index_to_rvar = new IntCollections.table_t in

      (* Note: table is not used in this function *)
      let add_rvar (v:variable_t) table = 
	let name = v#getName#getBaseName in
	if name.[0] = 'r' && name.[1] <> 'e' then 
	  begin
	    let ind = int_of_string (Str.string_after name 1) in
	    index_to_rvar#set ind v 
	  end in
      rvar_to_pc_to_versions#iter add_rvar ; 

      let add_write_var (index:int) table = 
	let add_scope (pc:int) (var:variable_t) = 
	  let jvar_info = Option.get (!jvar_infos#get var) in
	  let types = jvar_info#get_types in 
	  let vars = 
	    if Option.is_some jvar_info#get_constant then
	      let orig_var = Option.get (index_to_rvar#get index) in 
	      let table = Option.get (rvar_to_pc_to_versions#get orig_var) in 
	      match table#get pc with 
	      | Some versions -> 
		  let reps = new VariableCollections.set_t in 
		  let add_rep v = 
		    match var_to_rep#get v with 
		    | Some rep -> reps#add rep 
		    | _ -> () in
                  begin
		    versions#iter add_rep ;
		    reps
                  end
	      | _ -> VariableCollections.set_of_list [var] 
	    else
              VariableCollections.set_of_list [var] in
          let scope = new scope_t ~first_pc:pc ~last_pc:pc ~types ~index ~vars in 
	  match index_to_scopes#get index with 
	  | Some set -> set#add scope ;
	  | _ ->
             index_to_scopes#set index (ScopeCollections.set_of_list [scope]) in 

	table#iter add_scope in 
      local_var_index_to_pc_to_var#iter add_write_var ;      

      let index_to_sorted_scopes = ref [] in
      let sort_scopes (ind:int) (scopes:ScopeCollections.set_t) = 
	let sorted_scopes =
          List.sort
            (fun s1 s2 -> s1#get_first_pc - s2#get_first_pc) scopes#toList in
	index_to_sorted_scopes :=
          (ind, sorted_scopes) :: !index_to_sorted_scopes in
      index_to_scopes#iter sort_scopes ;
      
      let add_read_scope_v
            (orig:variable_t) (name:string) (pc:int) (v:variable_t) = 
	let rep = get_rep v in
	let index = int_of_string (Str.string_after name 1) in
	match !jvar_infos#get rep with 
	| Some jvar_info ->
	    begin
	      let types = jvar_info#get_types in
	      let scope =
                new scope_t
                    ~first_pc:pc
                    ~last_pc:pc
                    ~types
                    ~index
                    ~vars:(VariableCollections.set_of_list [v]) in
	      let sorted_scopes = List.assoc index !index_to_sorted_scopes in
	      scope#add_to_list sorted_scopes 
	    end
	| _ -> () in

      let add_read_var (var:variable_t) table =
	let add_read_scope
              (orig:variable_t)
              (name:string)
              (pc:int)
              (vs:VariableCollections.set_t) = 
	  vs#iter (add_read_scope_v orig name pc) in
	let name = var#getName#getBaseName in
	if name.[0] = 'r' && name.[1] != 'e' then 
	  table#iter (add_read_scope var name) in 

      rvar_to_pc_to_versions#iter add_read_var ;
      
      let new_index_to_sorted_scopes = ref [] in
      let compact (index, scopes) = 
	let scope_set = ScopeCollections.set_of_list scopes in
	let rec compact_scopes () = 
	  let rec compact_one scope = 
	    let vars = scope#get_vars in
	    let check scope' = 
	      let vars' = scope'#get_vars in
	      if scope#get_first_pc <> scope'#get_first_pc
                 && not (vars#inter vars')#isEmpty then 
		begin
		  scope_set#remove scope ;
		  scope_set#remove scope' ;
		  let new_scope = scope#union scope' in 
		  scope_set#add new_scope ;
		  compact_scopes () 
		end in
	    scope_set#iter check in
	  scope_set#iter compact_one in
	compact_scopes () ;

	let sorted_scopes =
          List.sort
            (fun s1 s2 -> s1#get_first_pc - s2#get_first_pc) scope_set#toList in
	let rec reduce_scopes (red_scopes:scope_t list) (scopes:scope_t list) = 
	  match scopes with 
	  | scope1 :: scope2 :: rest_scopes -> 
	     if scope1#get_last_pc > scope2#get_first_pc then 
	       reduce_scopes red_scopes  ((scope1#union scope2) :: rest_scopes) 
	     else
               reduce_scopes (scope1 :: red_scopes) (scope2 :: rest_scopes)
	  | [scope] -> scope :: red_scopes
	  | [] -> red_scopes in
	new_index_to_sorted_scopes :=
          (index, reduce_scopes [] sorted_scopes) :: !new_index_to_sorted_scopes in

      List.iter compact !index_to_sorted_scopes ;
      index_to_sorted_scopes := !new_index_to_sorted_scopes ;
	

      let all_scopes = List.flatten (List.map snd !index_to_sorted_scopes) in

      List.map
        (fun s -> s#make_var_table_line self#get_opcodes self#get_method_info)
        all_scopes 
  
    method make_var_table
             ~(aliases: JCHTransformUtils.alias_sets_t)
	     ~(rvar_to_pc_to_versions:VariableCollections.set_t
                                      IntCollections.table_t
                                      VariableCollections.table_t) 
	     ~(orig_phi_to_vars: VariableCollections.set_t
                                 VariableCollections.table_t) 
	     ~(local_var_index_to_pc_to_var :variable_t
                                               IntCollections.table_t
                                               IntCollections.table_t) = 
      match bytecode#get_local_variable_table with 
      | Some local_var_table -> 
	 let transform_line (first_pc, len_pc, name, vtype, index) = 
	   (first_pc, first_pc + len_pc, name, [vtype], index) in
	 let loc_var_table = List.map transform_line local_var_table in
	 var_table := loc_var_table ;
      |  _ ->  
	  var_table :=
            self#make_local_variable_table
              ~aliases
              ~rvar_to_pc_to_versions
              ~orig_phi_to_vars
              ~local_var_index_to_pc_to_var 

    (* Has to be called after set_var_infos *)
    (* Is not used yet *)

    method get_length (var:variable_t) = 
      try 
	let var_info = self#get_jvar_info var in
	let (len_opt, has_length_var) =
          (* This is not the same variable as the one in the scope of the method *)
          var_info#get_length in 
	let len = Option.get len_opt in 
	let length = List.find len#equal self#get_variables in
	if not has_length_var then 
	  begin
	    var_info#set_corresp_length length ;
	    let length_info = Option.get (!jvar_infos#get length) in
	    length_info#set_corresp_var var 
	  end ;
	Some length
      with _ -> None

    method get_variable_from_length (length:variable_t) = 
      try 
	let length_info = self#get_jvar_info length in
	let (v_opt, has_var) =
          (* This is not the same variable as the one in the scope of the method *)
          length_info#get_variable_from_length in 
	let v = Option.get v_opt in
	let var = List.find v#equal self#get_variables in
	if not has_var then 
	  begin
	    length_info#set_corresp_var var ;
	    let var_info = Option.get (!jvar_infos#get var) in
	    var_info#set_corresp_length length
	  end ;
	Some var
      with _ -> None

    method get_wto_prev_pc_to_entry_pcs = 
      let pc_to_entry_pcs = ref [] in
      let add_wto (wto:JCHLoopUtils.wto_info_t) = 
	let pc = wto#get_entry_pc in
	let state = self#get_cfg#getState wto#get_name in
	let prev_pcs =
          JCHSystemUtils.get_prev_pcs self#get_method_info self#get_cfg state in
	List.iter
          (fun prev_pc ->
            pc_to_entry_pcs := (prev_pc, pc) :: !pc_to_entry_pcs) prev_pcs  in
      begin
        List.iter add_wto wto_infos ;
        !pc_to_entry_pcs
      end
      
    method private pp_var_table_ table = 
      let pp_var_table_line (first, last, name, types, ind) = 
	LBLOCK [INT first; STR " "; INT last;  STR (" "^ name); 
		pretty_print_list types value_type_to_pretty " {" ", " "} ";
                INT ind; NL] in
      LBLOCK (List.map pp_var_table_line table) 
		 

    method toPretty =
      LBLOCK [proc_name#toPretty; NL;
	      INDENT
                (2, LBLOCK
                      [STR "procedure: "; NL;  proc#toPretty; NL; 
		       STR "wto_infos: "; NL; pp_list wto_infos; NL;
		       STR "local var table: "; NL;
                       pp_var_table bytecode#get_local_variable_table; NL; 
		       STR "constructed var table: "; NL;
                       self#pp_var_table_ !var_table; NL; 
		       STR "var infos: "; NL; !jvar_infos#toPretty; NL; 
		       STR "bytecode: "; NL; bytecode#toPretty; NL;
                       STR "states where vars are equal: ";
                       (Option.get !var_to_var_to_eqs)#toPretty; NL])]
  end

let is_handler (state_name:symbol_t) = 
  let str = state_name#getBaseName in
  if String.length str < 8 then
    false
  else
    (String.sub str 0 4 <> "loop")
    && (String.sub str ((String.length str) - 7) 7) = "handler"


(* Adds operations to add variables in the analysis before they are first used
 * or remove them from the analysis when they are not used any more *)
let add_var_ops (jproc_info:jproc_info_t) = 
  let jvar_infos = jproc_info#get_jvar_infos in
  let state_to_done_vars = make_state_to_done_num_vars jvar_infos in
  let state_to_start_vars = make_state_to_start_num_vars jvar_infos in
  let proc = jproc_info#get_procedure in
  let proc_name = proc#getName in
  let cms = retrieve_cms proc_name#getSeqNumber in
  let cfg = jproc_info#get_cfg in
  let add_operation state_name = 
    if not (state_name#getIndex = exceptional_exit_sym#getIndex
            || state_name#getIndex = method_exit_sym#getIndex) then 
      let done_vars = 
	match state_to_done_vars#get state_name with
	| Some set -> set#toList
	| None -> [] in
      let start_vars = 
	match state_to_start_vars#get state_name with
	| Some set -> set#toList 
	| None -> [] in
      let state = cfg#getState state_name in
      JCHAnalysisSetUp.add_vars_op
        ~proc ~cms ~state ~add_vars:start_vars ~remove_vars:done_vars 
  in
  List.iter add_operation cfg#getStates 

(* Adds the transformed variable to each slot
 * A variant of the variable was added in SSA but it has to be changed 
 * with the representative which was computed later *)
let set_tr_variable
      (proc_name:symbol_t)
      (proc:procedure_int)
      (aliases:JCHTransformUtils.alias_sets_t) = 
  let cms = retrieve_cms proc_name#getSeqNumber in
  let mInfo = app#get_method cms in
  let pc_stack_layouts = mInfo#get_method_stack_layout#get_pc_stack_layouts in
  let pc_to_instruction = new IntCollections.table_t in
  let _  = List.iter (fun (pc,s) -> pc_to_instruction#set pc s) pc_stack_layouts in
  let get_rep (v:variable_t) = 
    match aliases#get_representative v with 
    | Some v' -> v'
    | _ -> v in
  let set_tr_var_instr (pc:int) (stack_layout:op_stack_layout_int) = 
    let set_tr_var_slot (slot:logical_stack_slot_int) = 
      try
	slot#set_transformed_variable (get_rep slot#get_transformed_variable) 
      with
      | _ ->
         pr__debug [proc_name#toPretty; STR " has unreachable pc "; INT pc; NL] in  
    List.iter set_tr_var_slot stack_layout#get_slots in
  pc_to_instruction#iter set_tr_var_instr

let make_jproc_info
      ~(chif:system_int)
      ~(proc_name:symbol_t)
      ~(proc:procedure_int)
      ~(wto:CHSCC.wto_t)
      ~(wto_infos:JCHLoopUtils.wto_info_t list)
      ~(loop_depth:int)
      ~(dom_info:JCHDominance.dominance_info_t)
      ~(aliases:JCHTransformUtils.alias_sets_t) 
      ~(rvar_to_pc_to_versions:
          VariableCollections.set_t
          IntCollections.table_t
          VariableCollections.table_t)
      ~(orig_phi_to_vars:VariableCollections.set_t VariableCollections.table_t)
      ~(extra_assert_vars:SymbolCollections.set_t VariableCollections.table_t)
      ~(jproc_info_opt:jproc_info_t option) = 
  match jproc_info_opt with 
  | Some jproc_info -> 
      let pc_to_instr = jproc_info#get_pc_to_instr in
      let instr_to_pc = jproc_info#get_instr_to_pc in
      let new_proc_info = 
	new jproc_info_t
            ~proc_name
            ~proc
            ~wto
            ~wto_infos
            ~loop_depth
            ~pc_to_instr
            ~instr_to_pc in
      let local_var_index_to_pc_to_var =
        new_proc_info#set_var_infos
          ~chif ~dom_info ~aliases ~extra_assert_vars in
      begin
        new_proc_info#make_var_table
          ~aliases
          ~rvar_to_pc_to_versions
          ~orig_phi_to_vars
          ~local_var_index_to_pc_to_var ;
        add_var_ops new_proc_info ; 
        JCHCodeTransformers.remove_skips_code_p proc; 
        new_proc_info
      end
  | _ ->
      let (bytecode, (offset_to_instrn_array, instrn_to_offset_array)) = 
	let cms = retrieve_cms proc_name#getSeqNumber in
	let mInfo = app#get_method cms in
	if mInfo#has_bytecode then
	  let bc = mInfo#get_bytecode in
	  (bc, bc#get_code#offset_to_from_instrn_arrays)
	else
	  raise (JCH_failure
                   (LBLOCK [ STR "Expected bytecode in " ; cms#toPretty ])) in
      let pc_to_instr n = 
	try offset_to_instrn_array.(n) 
	with
        | _ -> 
	   let length = Array.length offset_to_instrn_array in
	   offset_to_instrn_array.(pred length) in
      let instr_to_pc n = instrn_to_offset_array.(n) in
      set_tr_variable proc_name proc aliases ;
      let new_proc_info = 
	new jproc_info_t
            ~proc_name
            ~proc
            ~wto
            ~wto_infos
            ~loop_depth
            ~pc_to_instr
            ~instr_to_pc in
      let local_var_index_to_pc_to_var =
        new_proc_info#set_var_infos
          ~chif ~dom_info ~aliases ~extra_assert_vars in
      begin
        new_proc_info#make_var_table
          ~aliases
          ~rvar_to_pc_to_versions
          ~orig_phi_to_vars
          ~local_var_index_to_pc_to_var ;
        new_proc_info
      end

(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet and Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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
open CHCommon
open CHLanguage
open CHNonRelationalDomainNoArrays
open CHNonRelationalDomainValues
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
open JCHStringSets


(* Suppress warnings on unused variables *)
[@@@warning "-27"]

let string_dom_name = "string_sets"

let get_arg_var (str: string) (op_args: (string * variable_t * arg_mode_t) list) =
  let has_this_string (s, _, _) = s = str in
  try
    let (_, v, _) = List.find has_this_string op_args in v
  with
  | Not_found ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "arg var ";
               STR str;
               STR " not found in ";
	       STR "JCHStringSetsDomainNoArrays.get_arg_var"]))

let get_dynamic_class_loading cname mname args =
  if cname = "java.lang.Class"  && mname = "forName" then
    Some (get_arg_var "arg0" args)
  else if (cname = "java.lang.ClassLoader"
           || cname = "java.security.SecureClassLoader"
           || cname = "java.net.URLClassLoader"
           || cname = "javax.management.loading.MLet"
           || cname = "javax.management.loading.PrivateMLet")
          && (mname = "loadClass"
              || mname = "defineClass"
              || mname = "findClass"
              || mname = "findSystemClass"
              || mname = "findLoadedClass") then
    Some (get_arg_var "arg1" args)
  else None


(* Printing utilities for debugging *)
let op_args_to_pretty op_args : pretty_t =
  let arg_mode_to_string am =
    match am with
    | READ -> "READ"
    | WRITE -> "WRITE"
    | _ -> "READ_WRITE" in
  let pp_arg (s,v,am) : pretty_t =
    LBLOCK [STR ("("^s^" , "); v#toPretty;
	     STR " , "; STR (arg_mode_to_string am);
	     STR " )"; NL] in
  pretty_print_list op_args pp_arg "" "" ""


let _operation_to_pretty op =
  LBLOCK [STR "operation "; op.op_name#toPretty; NL;
	   STR "op_args: "; NL; op_args_to_pretty op.op_args;
	   STR "end op_args"; NL]


let rec can_be_string value_type =
  match value_type with
  | TBasic Object -> true
  | TBasic _ -> false
  | TObject TClass cn -> cn#name = "java.lang.String" || cn#name = "java.lang.Object"
  | TObject TArray vt -> can_be_string vt


(* If the system is analyzed once, then the fields are unknown
 * If the system in analyzed twice, then the fields set in the first pass will
 * be used in the second pass *)
let put_field_to_strings = ref (new IntCollections.table_t)
      (* field_info index -> string_set_t used for puts *)
let get_field_to_strings = ref (new IntCollections.table_t)
      (* field_info index -> string_set_t used for gets *)
let put_field field_index string_set =
  !put_field_to_strings#set field_index string_set

let get_field field_index =
  !get_field_to_strings#get field_index

let reset_fields () =
  get_field_to_strings := !put_field_to_strings;
  put_field_to_strings := new IntCollections.table_t

class dynamic_load_call_t
        (proc_name: symbol_t)
        (pc: int)
        (arg_number: int)
        (cs: symbol_t list)
        (fail: bool)
        (s_set: string_set_t)
        (callee_opt: symbol_t option) =
  object (_: 'a)
    val callers = ref cs   (* methods that call proc_name *)
    val string_set = ref s_set
        (* all strings that could the callers could have as argument
           arg_number for their call to proc_name *)

    method get_proc_name = proc_name
    method has_dynamic_call = not (Option.is_some callee_opt)
    method get_pc = pc
    method get_arg_number = arg_number
    method get_callers = callers
    method get_callee = callee_opt
    method fail = fail
    method get_string_set = !string_set
    method add_string_set caller other_string_set =
      callers := List.filter (fun s -> not (s#equal caller)) !callers ;
      string_set := !string_set#join other_string_set
    method is_resolved = !callers = []

    method equal (a: 'a) =
      proc_name#equal a#get_proc_name &&
      pc = a#get_pc &&
      !string_set#equal a#get_string_set

    method toPretty =
      let callee_pp =
	match callee_opt with
	| Some callee -> LBLOCK [STR " calls "; callee#toPretty; STR " at "]
	| _ -> STR " has dynamic call at " in
      LBLOCK [
          STR "dynamic_loading_call ";
          proc_name#toPretty;
          callee_pp;
          INT pc;
          STR " arg ";
          INT arg_number;
          STR " ";
          !string_set#toPretty; NL;
	  if fail then STR "one caller failed to translate " else pp_list !callers;
          NL]
    method report =
      LBLOCK [
          proc_name#toPretty; STR " "; INT pc; STR " "; !string_set#toPretty; NL]

  end


let dynamic_call_table = ref (new SymbolCollections.table_t)

let methods_to_analyze : symbol_t list ref = ref []

(* arg_number is the argument number of a function for which that argument
 * is a string that is used as a class name in a dynamic load call
 * or is -1 if there is no such argument *)
let add_dynamic_call
      (proc_name:symbol_t)
      (pc:int) (arg_number:int)
      (callers:class_method_signature_int list)
      (callee_opt:symbol_t option)
      string_set =
  let add table =
    let mInfos = List.map app#get_method callers in
    let (failed, translated)  =
      List.partition (fun mi -> mi#failed_to_translate) mInfos in
    let translated_callers = List.map (fun mi -> mi#get_procname) translated in
    let string_set = if failed = [] then string_set else add_unknown string_set in
    let dynamic_load_call =
      new dynamic_load_call_t
        proc_name
        pc
        arg_number
        translated_callers
        (failed <> [])
        string_set
        callee_opt in
    begin
      methods_to_analyze := translated_callers @ !methods_to_analyze;
      table#set pc dynamic_load_call
    end in
  match !dynamic_call_table#get proc_name with
  | Some table ->
      if table#has pc then () else add table
  | None ->
     let table = new IntCollections.table_t in
     begin
       !dynamic_call_table#set proc_name table;
       add table
     end


(* Domain for constant string detection.
 * The variables of interest are the those of type string, array of
 * string, array of array of string, ...
 * For the array variables the set will represent all the possible values
 * for the entries
 * In a first pass, set_fields is true, and the system is analyzed only to
 * find an overapproximation of the string fields *)
class string_sets_domain_no_arrays_t
        set_fields (proc_name: symbol_t) (_proc: procedure_int) =
  object (self: 'a)

    val cms = retrieve_cms proc_name#getSeqNumber
    val mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber)

    inherit non_relational_domain_t

    method private getValue' v : string_set_t =
      let v_value = self#getValue v in
      match v_value#getValue with
      | EXTERNAL_VALUE v -> v
      | TOP_VAL -> top_string_set
      |	BOTTOM_VAL -> bottom_string_set
      | _ ->
	 raise
           (CHFailure
              (LBLOCK [
                   STR "String set expected. ";
                   v#toPretty;
                   STR ": ";
                   v_value#toPretty]))

    method private importValue v =
      match v#getValue with
      |	EXTERNAL_VALUE _ -> v
      |	TOP_VAL -> topNonRelationalDomainValue
      |	BOTTOM_VAL -> bottomNonRelationalDomainValue
      |	_ ->
         raise
           (JCH_failure
              (STR "JCHStringSetsDomainNoArrays.importValue expected external_value_int"))

    method private set_string' table' string_set var =
      self#setValue
        table' var (new non_relational_domain_value_t (EXTERNAL_VALUE string_set))

    method special (_cmd: string) (_args: domain_cmd_arg_t list) = {< >}

    method private analyze_invoke is_static cn_opt msig opname args =
      let table' = table#clone in
      let arg_types = msig#descriptor#arguments in
      let (wargs, rargs) =
	List.partition (fun (_,_,m) ->
            match m with READ -> false | _ -> true) args in
      let rargs' =
        if is_static then
          rargs
        else
          List.tl rargs (* remove the object *) in
      let wvars = List.map (fun (_,v,_) -> v) wargs in
      self#abstractVariables table' wvars;  (* The return variable is unknown *)
      let arg_types = List.combine rargs' arg_types in
      let can_be_array vt =
	match vt with
	| TObject (TArray _)
	| TBasic Object -> true
	| TObject (TClass cn) -> cn#name = "java.lang.Object"
	| _ -> false in
      let rwargs = List.filter (fun (_,t) -> can_be_array t) arg_types in
      let rwvars = List.map (fun ((_,v,_),_) -> v) rwargs in
      self#abstractVariables table' rwvars;
      (* These variables could be modified by the call *)

      (* Check dynamic loading *)
      let bcloc = get_bytecode_location cms#index opname#getSeqNumber in
      let instr_info = app#get_instruction bcloc in
      let find_string_set _cn var callee_opt =
	let pc = opname#getSeqNumber in
	let string_set = self#getValue' var in
	if string_set#isTop then
	  begin
	    let method_stack_layout = mInfo#get_method_stack_layout in
	    let stack_layout = method_stack_layout#get_stack_layout pc in
	    let slots = stack_layout#get_slots in
	    let rec get_slot slots =
	      match slots with
	      | slot :: rest_slots ->
		  if slot#get_variable#equal var then slot
		  else get_slot rest_slots
	      | _ ->
                 raise
                   (JCH_failure (STR "expected slot with the found argument")) in
	    let slot = get_slot slots in
	    match slot#get_sources with
	    | [i] ->
		begin
		  match mInfo#get_opcode i with
		  | OpLoad (_, j) ->
		     if j < List.length cms#method_signature#descriptor#arguments then
                        (* It is an argument *)
			let callers = mInfo#get_callers in
			add_dynamic_call
                          proc_name pc j callers callee_opt bottom_string_set;
                        (* the string_set can be resolvesd by the callers of
                           this method *)
		  | _ ->
                     (* the string_set is not known so it is set to unknown *)
                     add_dynamic_call
                       proc_name pc (-1) [] callee_opt unknown_string_set
		end
	    | _ ->
               (* the string_set is not known so it is set to unknown *)
               add_dynamic_call proc_name pc (-1) [] callee_opt unknown_string_set
	  end
	else
          (* the string_set was resolved *)
          add_dynamic_call proc_name pc (-1) [] callee_opt string_set in

      if not set_fields then
	begin
	  match cn_opt with
	  | Some cn ->
	      begin
		match get_dynamic_class_loading cn#name msig#name args with
		| Some var -> find_string_set cn var None
		| _ ->
		    begin
		      let pnames = (instr_info#get_method_target ())#get_procs in
		      let check pname =
			match !dynamic_call_table#get pname with
			| Some table ->
			    let check_call dyn_call =
			      let arg_number = dyn_call#get_arg_number in
			      if arg_number <> -1 then
				begin
				  let (_, var, _) = List.nth rargs arg_number in
				  find_string_set cn var (Some pname)
				end in
			    List.iter check_call table#listOfValues
			| _ -> () in
		      List.iter check pnames
		    end
	      end
	  | _ -> ()
	end;
      {< table = table' >}

    method !analyzeOperation
             ~(domain_name: string)
             ~(fwd_direction: bool)
             ~(operation: operation_t): 'a =
      match operation.op_name#getBaseName with
      | "i"
      | "ii" -> self#analyze_operation operation.op_name operation.op_args
      |	_ -> {< >}

    method private analyze_operation opname args =
      let bcloc = get_bytecode_location proc_name#getSeqNumber opname#getSeqNumber in
      let instr_info = app#get_instruction bcloc in
      let table' = table#clone in
      let default () = 	{< table = table' >} in
      match instr_info#get_opcode with
      |	OpStore _
      |	OpLoad _ ->
	  let src1 = get_arg_var "src1" args in
	  let dst1 = get_arg_var "dst1" args in
	  let string_set = self#getValue' src1 in
	  self#set_string' table' string_set dst1;
	  default ()
      | OpStringConst s ->
	  self#set_string' table' (mk_string_set [s]) (get_arg_var "ref" args);
	  default ()
      |	OpPutStatic (_, fsig)
      |	OpPutField (_, fsig) ->
	  if can_be_string fsig#descriptor then
	    begin
	      let index = instr_info#get_field_target#get_index in
	      let vl = get_arg_var "val" args in
	      let string_set = self#getValue' vl in
	      put_field index string_set
	    end;
	  default ()
      |	OpGetStatic (_, fsig)
      |	OpGetField (_, fsig) ->
	  if can_be_string fsig#descriptor then
	    begin
	      let index = instr_info#get_field_target#get_index in
	      match get_field index with
	      |	Some string_set ->
		  let vl = get_arg_var "val" args in
		  self#set_string' table' string_set vl
	      |	_ -> ()
	    end;
	  default ()
      |	OpArrayLoad _ ->
	  let array = get_arg_var "array" args in
	  let elem = get_arg_var "val" args in
	  let string_set = self#getValue' array in
	  self#set_string' table' string_set elem;
	  default ()
      |	OpArrayStore _ ->
	  let array = get_arg_var "array" args in
	  let elem = get_arg_var "val" args in
	  let string_set = self#getValue' elem in
	  let array_string_set = self#getValue' array in
	  self#set_string' table' (array_string_set#join string_set) array;
	  default ()
      |	OpInvokeStatic (cn, msig) ->
	  self#analyze_invoke true (Some cn) msig opname args
      |	OpInvokeVirtual (TClass cn, msig)
      |	OpInvokeSpecial (cn, msig)
      |	OpInvokeInterface (cn, msig) ->
	  self#analyze_invoke false (Some cn) msig opname args
      |	OpInvokeVirtual (_, msig) ->
	  self#analyze_invoke false None msig opname args
      |	 _ -> default ()

    method private analyzeFwd' (cmd: (code_int, cfg_int) command_t) =
      if bottom then self#mkBottom
      else
	let table' = table#clone in
	let default () =
	  {< table = table' >}
	in
	match cmd with
	| ABSTRACT_VARS l ->
	    begin
	      self#abstractVariables table' l;
	      default ()
	    end
	| ASSERT FALSE ->
	    self#mkBottom
	| ASSIGN_NUM (v, NUM_VAR w)
	| ASSIGN_SYM (v, SYM_VAR w) ->
	    let string_set = self#getValue' w in
	    self#set_string' table' string_set v;
	    default ()
	| OPERATION op ->
	   self#analyzeOperation
             ~domain_name: string_dom_name ~fwd_direction: true ~operation: op
	| _ ->
	    default ()

  method private analyzeBwd' (cmd: (code_int, cfg_int) command_t) =
    if bottom then self#mkBottom
    else
      let table' = table#clone in
      let default () =
	{< table = table' >} in
      match cmd with
      | ABSTRACT_VARS l ->
	  self#abstractVariables table' l;
	  default ()
      |	ASSIGN_NUM (x, _)
      | ASSIGN_SYM (x, _) ->
	  self#abstractVariables table' [x];
	  default ()
      | ASSERT _ -> self#analyzeFwd' cmd
      | _ ->  default ()

end

let get_constant_strings_proc set_fields system proc_name =
  let proc = system#getProcedure proc_name in
  let pc_to_invariant = new IntCollections.table_t in
  let analyzer = CHAnalysisSetup.mk_analysis_setup () in
  let op_semantics
        ~(invariant:CHAtlas.atlas_t)
        ~(stable:bool)
        ~(fwd_direction:bool)
        ~context
        ~operation =
    match operation.op_name#getBaseName with
    | "v" ->
      begin
	(if fwd_direction && stable then
	    let pc = operation.op_name#getSeqNumber in
	    let string_dom = invariant#getDomain string_dom_name in
	    pc_to_invariant#set pc string_dom);
	invariant
      end
    | "method-init"
    | "dead_vars"
    | "i"
    | "ii" ->
	if fwd_direction then
	  invariant#analyzeFwd (OPERATION operation)
	else invariant
    | _ -> invariant in
  begin
    analyzer#setOpSemantics op_semantics;
    analyzer#setStrategy
      {CHIterator.widening = (fun _ -> true, "");
       CHIterator.narrowing = (fun _ -> true) };
    let string_set_dom =
      new string_sets_domain_no_arrays_t set_fields proc_name proc in
    analyzer#addDomain string_dom_name string_set_dom;
    analyzer#analyze_procedure ~do_loop_counters:false system proc
  end

let find_dynamic_loading_names system =
  let procs = system#getProcedures in

  begin
    (* Do a first pass to find the fields *)
    List.iter (get_constant_strings_proc true system) procs;
    reset_fields ();

    (* Propagate strings within the methods. If a dynamic call is not resolved,
     * check whether the class name is an argument of the method.
     * In this case add teh callers to methods to analyze. *)
    List.iter (get_constant_strings_proc false system) procs;

    (* Analyze recursively the methods that call methods with dynamic load calls *)
    while !methods_to_analyze <> [] do
      let procs = !methods_to_analyze in
      begin
        methods_to_analyze := [];
        List.iter (get_constant_strings_proc false system) procs
      end
    done;
    let all_dynamic_calls =
      List.flatten
        (List.map (fun t -> t#listOfValues) !dynamic_call_table#listOfValues) in
    let resolved_calls =
      List.filter (fun dc -> dc#is_resolved) all_dynamic_calls in

    (* Propagate the strings found down to the method that has the dynamic load *)
    let rec work (dcs : dynamic_load_call_t list) =
      match dcs with
      | dc :: rest_dcs ->
	 begin
	   let proc_name = dc#get_proc_name in
	   let string_set = dc#get_string_set in
	   let add_string_set callee string_set =
	     match !dynamic_call_table#get callee with
	     | Some table ->
		let add new_resolved_calls dyn_call =
		  if dyn_call#is_resolved then
		    new_resolved_calls
		  else
		    begin
		      dyn_call#add_string_set proc_name string_set;
		      if dyn_call#is_resolved then dyn_call :: new_resolved_calls
		      else new_resolved_calls
		    end in
		List.fold_left add [] table#listOfValues
	     | None -> [] in
	   match dc#get_callee with
	   | Some callee ->
	      let new_resolved_calls = add_string_set callee string_set in
	      work (new_resolved_calls @ rest_dcs)
	   | None -> work rest_dcs
	 end
      | _ -> () in
    work resolved_calls;

    (* Print the results *)
    let count = ref 0 in
    let ucount = ref 0 in
    let report dc =
      let string_set = dc#get_string_set in
      if dc#has_dynamic_call && has_string string_set then
        begin
	  incr count;
	  if has_unknown string_set then incr ucount
        end in
    List.iter report all_dynamic_calls
  end

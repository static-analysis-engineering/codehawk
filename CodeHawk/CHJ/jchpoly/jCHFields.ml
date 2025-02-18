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
open CHIntervals
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
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHPreAPI

(* jchsys *)
open JCHPrintUtils

module FieldInfoCollections = CHCollections.Make (
  struct
    type t = field_info_int
    let compare f1 f2 = compare f1#get_index f2#get_index
    let toPretty f = f#toPretty
  end)

module ClassInfoCollections = CHCollections.Make (
  struct
    type t = class_info_int
    let compare c1 c2 = compare c1#get_class_name#index c2#get_class_name#index
    let toPretty c = c#toPretty
  end)

module ClassNameCollections = CHCollections.Make (
  struct
    type t = class_name_int
    let compare n1 n2 = n1#compare n2  (* Why are strings in compare and not just indices ? *)
    let toPretty n = n#toPretty
  end)


class interval_list_t (ints:interval_t list) =
  object (_: 'a)
    method ints = ints
    method equal (int_list': 'a) =
      let ints' = int_list'#ints in
      if List.length ints = List.length ints' then
	List.for_all (fun (int, int') -> int#equal int')
	  (List.combine ints ints')
      else
        false
    method toPretty = pp_list ints
  end

(* It finds initialized fields.
 * If there are branches it returns an empty set
 * It also puts in non_consts, the fields with a non constant origin *)
class collect_init_fields_t
        (not_analyzed:bool)
        (non_consts:IntCollections.set_t)
        (static:bool)
        (proc_name:symbol_t) =
object

  inherit code_walker_t as super

  val jproc_info_opt =
    if not_analyzed then
      None
    else
      Some (JCHSystem.jsystem#get_jproc_info proc_name)
  val cms = retrieve_cms proc_name#getSeqNumber
  val mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber)
  val branching = ref false
  val init_fields = new IntCollections.set_t
  method get_init_fields =
    if !branching then
      new IntCollections.set_t
    else
      init_fields

  method !walkCmd (cmd: (code_int, cfg_int) command_t) =
    match cmd with
    | CFG (_, cfg) ->
	let states = cfg#getStates in
	let has_one_pred state_name =
	  let state_name_base = state_name#getBaseName in
	  if state_name_base =
               "exceptional-exit" || state_name_base = "method-exit" then
            true
	  else
	    let state = cfg#getState state_name in
	    List.length state#getIncomingEdges < 2 in
        begin
	  (if not (List.for_all has_one_pred states) then
             branching := true);
	  super#walkCmd cmd
        end
    | OPERATION {op_name = opname; op_args = args} ->
	begin
	  match opname#getBaseName with
	  | "i"
	  | "ii" ->
	    let pc = opname#getSeqNumber in
	    let bcloc = get_bytecode_location cms#index pc in
	    let instr_info = app#get_instruction bcloc in
	      begin
		match mInfo#get_opcode pc  with
		| OpPutStatic _ ->
		   let index = instr_info#get_field_target#get_index in
                   (* add to init_fields only if collecting static init_fields *)
		   if static then init_fields#add index;
		   let var = JCHSystemUtils.get_arg_var "val" args in
		   if not_analyzed then
                     ()
		   else
		     begin
		       let jproc_info = Option.get jproc_info_opt in
		       let var_info = jproc_info#get_jvar_info var in
		       let opcodes = jproc_info#get_bytecode#get_code in
		       let has_const_orig pc =
			 match opcodes#at pc with
			 | OpIntConst _
			 | OpLongConst _
			 | OpFloatConst _
			 | OpDoubleConst _
			 | OpByteConst _
			 | OpShortConst _
			 | OpStringConst _ -> true
			 | _ -> false in
		       if List.for_all has_const_orig var_info#get_origins then
                         ()
		       else
                         non_consts#add index
		     end
		| OpPutField _  ->
		   if not static then
                     (* add to init_fields only if collecting non_static init_fields *)
                     init_fields#add instr_info#get_field_target#get_index
		| _ -> ()
	      end
	  | _ -> ()
	end
    | CODE _
    | RELATION _
    | TRANSACTION _ -> super#walkCmd cmd
    | _ -> ()
  end

(* Record the values of the integer fields.
 * The methods take valued from the get_fields and put them in the put_fields
 * The get_fields are set before the analysis, either in a previous pass or
 * to Top, etc *)
class int_field_manager_t =
  object (self: 'a)

    val first_pass = ref true

    val class_to_init_st_fields = new ClassInfoCollections.table_t
    val class_to_init_fields = new ClassInfoCollections.table_t
    val classes_with_fields = new ClassInfoCollections.set_t

    (* field info -> procs that read the field *)
    val field_to_procs = new FieldInfoCollections.table_t

     (* Field to list of intervals. *)
     (* The first is the interval for the field the rest are for the dimensions
      * of the array, in case it is an array *)
    val get_table : interval_list_t FieldInfoCollections.table_t ref =
      ref new FieldInfoCollections.table_t

    val put_table : interval_list_t FieldInfoCollections.table_t ref =
      ref new FieldInfoCollections.table_t

    (* indices of fields that have an origin in some method which is not
     * constant *)
    val non_consts = new IntCollections.set_t

    (* indices of fields in which only constants are stored *)
    val consts = new IntCollections.set_t

    method is_dt_field (cn:class_name_int) (fs:field_signature_int) =
      match fs#descriptor with
      | TObject TClass cn1 ->
	 fs#name = "in"
         && cn1#name = "java.io.InputStream" && cn#name = "java.lang.System"
      | _ -> false

    method is_const_field (fInfo:field_info_int) = consts#has fInfo#get_index

    method private initialize =
      let fInfos = JCHApplication.app#get_fields in
      let add_field_to_meth field cms =
	let mInfo = JCHApplication.app#get_method cms in
	let proc_name = mInfo#get_procname in
	match field_to_procs#get field with
	| Some set -> set#add proc_name
	| None ->
           field_to_procs#set field (SymbolCollections.set_of_list [proc_name]) in
      let add_field fInfo =
	let rmeths = fInfo#get_reading_methods in
	List.iter (add_field_to_meth fInfo) rmeths in
      List.iter add_field fInfos;

    method private mk_max_intervals (fInfo:field_info_int) =
      let vtype = fInfo#get_class_signature#field_signature#descriptor in
      let int = JCHTypeUtils.get_interval_from_type (Some vtype) in
      if (JCHTypeUtils.is_array vtype) then
	[int; JCHTypeUtils.length_interval]
      else
        [int]

    method project_out (fInfo:field_info_int) =
      let max_ints = self#mk_max_intervals fInfo in
      !put_table#set fInfo (new interval_list_t max_ints)

    (* if set_dims then the info in the int_list is taken into consideration
     * even if it is missing *)
    method private add_field_interval
                     (set_dims:bool)
                     (fInfo:field_info_int)
                     (int_list:interval_list_t) =
      let ints = int_list#ints in
      let new_ints =
	match !put_table#get fInfo with
	| Some i_list ->
	    let rec join_all new_ints old_ints =
	      match (new_ints, old_ints) with
	      | (_, []) -> new_ints
	      | ([], _) -> if set_dims then [] else old_ints
	      | (new_i :: rest_new_ints, old_i :: rest_old_ints) ->
		  (new_i#join old_i) :: (join_all rest_new_ints rest_old_ints) in
	    join_all ints i_list#ints
	| _ -> ints in
      !put_table#set fInfo (new interval_list_t new_ints);

    method put_field
             (_proc_name:symbol_t)
             (fInfo:field_info_int)
             (int:interval_t)
             (dim_ints:interval_t list)
             (set_dims:bool)
             (var: variable_t) =
      match fInfo#get_field with
      | ConcreteField _ ->
	  if fInfo#is_accessible_to_stubbed_methods then
	    begin
	      match !put_table#get fInfo with
	      |	Some _ -> ()
	      |	_ ->
		  let max_ints = self#mk_max_intervals fInfo in
		  !put_table#set fInfo (new interval_list_t max_ints)
	    end
	  else
	    begin
	      let ints =
		if JCHSystemUtils.is_number var then [int]
		else
		  if set_dims && dim_ints = [] then
		    [int; JCHTypeUtils.length_interval]
		  else
                    int :: dim_ints in
	      let int_list = new interval_list_t ints in
	      self#add_field_interval set_dims fInfo int_list;
	    end
      |	_ -> ()

    (* Makes all the fields that the proc writes unknown *)
    method set_unknown_fields (jproc_info: JCHProcInfo.jproc_info_t) =
      let set cfs =
	let fInfo =
          try
            JCHApplication.app#get_field cfs
          with
          | JCH_failure p ->
             begin
               ch_error_log#add
                 "missing field"
                 (LBLOCK [STR "set-unknown-fields: "; p]);
               raise (JCH_failure (LBLOCK [STR "set-unknown-fields: "; p]))
             end in
	let max_ints = self#mk_max_intervals fInfo in
	!put_table#set fInfo (new interval_list_t max_ints) in
      List.iter set (jproc_info#get_method_info#get_field_writes)

    (* fields are recorded in classes_with_fields. These are later used to
     * find the static fields that constant and therefore not tainted
     * record_field is called in the first pass of the poly analysis
     * So for the taint analysis to work correctly with fields, it has to
     * be called after the numeric analysis *)
    method record_field (iinfo:instruction_info_int) =
      let fInfo = iinfo#get_field_target in
      match fInfo#get_field with
      | ConcreteField _ ->
	  if !first_pass then
	    classes_with_fields#add
              (JCHTypeUtils.get_class_info fInfo#get_class_signature#class_name);
      |	_ -> ()

    (* returns an interval if the field is numerical. If the field is an array,
     * it returns an interval for the entries and intervals for the dimensions *)
    method get_field_intervals (fInfo:field_info_int) =
      match fInfo#get_field with
      | ConcreteField _ ->
	  if !first_pass then
	    begin
	      match !get_table#get fInfo with
	      | Some is -> is#ints
	      | None ->
		  let max_ints = self#mk_max_intervals fInfo in
		  !get_table#set fInfo (new interval_list_t max_ints);
		  max_ints
	    end
	  else
	    begin
	      match !get_table#get fInfo with
	      | Some is -> is#ints
	      | None -> (* The method that write were not analyzed because they were safe and large *)
		  begin
		    pr__debug [
                        STR "Analysis failed: get_table does not have ";
                        fInfo#toPretty; NL;
                        pp_list fInfo#get_writing_methods; NL];
		    raise
                      (JCHAnalysisUtils.numeric_params#analysis_failed
                         3 "programming error in poly: get_field_intervals")
		  end
	    end
      |	StubbedField fstub ->
	  if fstub#has_value then
	    begin
	      match fstub#get_value with
	      | ConstInt i -> [mkSingletonInterval (mkNumericalFromInt32 i)]
	      | ConstLong i -> [mkSingletonInterval (mkNumericalFromInt64 i)]
	      | ConstDouble f
	      | ConstFloat f ->
		  let (_,_,interval) = JCHAnalysisUtils.float_to_interval f in
		  [interval]
	      | ConstClass _
	      | ConstString _ -> self#mk_max_intervals fInfo
	    end
	  else
            self#mk_max_intervals fInfo
      | _ -> self#mk_max_intervals fInfo

    method get_all_num_fields =
      let all_fields = new FieldInfoCollections.set_t in
      begin
        all_fields#addList !put_table#listOfKeys;
        all_fields#addList !get_table#listOfKeys;
        all_fields#toList
      end

    (* It returns all the fields that are set. This is used for constructors
     * to get the initialized fields.
     * In case that the code is not in a straight line, it returns an empty set.
     * It also adds the fields that were assigned a non-constant value to
     * non-consts *)
    method private get_init_fields_m (mInfo:method_info_int) =
      match mInfo#get_implementation with
      | ConcreteMethod _m ->
          let proc_name = mInfo#get_procname in
          let (not_analyzed, proc) =
	    try
              (false, JCHSystem.jsystem#get_transformed_chif#getProcedure proc_name)
	    with _ ->
              (true, JCHSystem.jsystem#get_original_chif#getProcedure proc_name) in
	  let collector =
            new collect_init_fields_t
                not_analyzed non_consts mInfo#is_class_constructor proc_name in
          begin
	    collector#walkCode proc#getBody;
	    collector#get_init_fields
          end
      | _ -> new IntCollections.set_t

    (* Finds fields that are initialized in the class by all the analyzed
     * constructor methods *)
    method private get_init_fields_c (cInfo:class_info_int) =
      let rec get_init_fields_ms
                ~(first:bool)
                ~(init_fields:IntCollections.set_t)
                ~(mInfos:method_info_int list) =
	match mInfos with
	| mInfo :: rest_minfos ->
	    let fs = self#get_init_fields_m mInfo in
	    let new_init_fields =
	      if first then
                fs
	      else
                init_fields#inter fs in
	    get_init_fields_ms
              ~first:false
              ~init_fields:new_init_fields
              ~mInfos:rest_minfos
	| _ -> init_fields in
      let cn = cInfo#get_class_name in
      let meths =
        List.filter (fun mInfo ->
	    (mInfo#get_class_name#equal cn)
            && mInfo#has_bytecode) app#get_methods in
      let (class_constrs, rest_meths) =
	List.partition (fun mi -> mi#is_class_constructor) meths in
      let (constrs, rest_meths) =
	List.partition (fun mi -> mi#is_constructor) rest_meths in
      let init_st_fields =
	get_init_fields_ms
          ~first:true
          ~init_fields:(new IntCollections.set_t)
          ~mInfos:class_constrs in
      let init_fields =
	get_init_fields_ms
          ~first:true
          ~init_fields:(new IntCollections.set_t)
          ~mInfos:constrs in
      (* This is just to find the non constant fields *)
      let _ = get_init_fields_ms
                ~first:true
                ~init_fields:(new IntCollections.set_t)
                ~mInfos:rest_meths in
      begin
        class_to_init_st_fields#set cInfo init_st_fields;
        class_to_init_fields#set cInfo init_fields
      end

    (* Adds 0 if the field is not known to have been initialized *)
    method private initialize_fields =

      (* This is done here not in start because in the first pass some
       * info is collected that is needed for this *)
      classes_with_fields#iter self#get_init_fields_c;

      let add0 (fInfo:field_info_int) =
	match !put_table#get fInfo with
	| Some int_list ->
	   if self#is_initialized fInfo || fInfo#is_constant then
             ()
	    else
	      begin
		let is = int_list#ints in
		let i = List.hd is in
		let int0 = mkSingletonInterval numerical_zero in
		!put_table#set
                 fInfo (new interval_list_t ((i#join int0) :: (List.tl is)))
	      end
	| _ ->
	    let int0 = mkSingletonInterval numerical_zero in
	    !put_table#set fInfo (new interval_list_t [int0]) in
      List.iter add0 !get_table#listOfKeys;

      let add_unknown_field (cfs:class_field_signature_int) =
	let fInfo =
          try
            JCHApplication.app#get_field cfs
          with
          | JCH_failure p ->
             begin
               ch_error_log#add
                 "missing field"
                 (LBLOCK [STR "collect-init-fields: "; p]);
               raise (JCH_failure (LBLOCK [STR "collect-init-fields: "; p]))
             end in
	let max_ints = self#mk_max_intervals fInfo in
	!put_table#set fInfo (new interval_list_t max_ints) in

      let add_unknown_bad_method (cmsix:int) =
	let cms = retrieve_cms cmsix in
	let mInfo = app#get_method cms in
	let cfss = mInfo#get_field_writes in
	List.iter add_unknown_field cfss in
      JCHSystem.jsystem#get_not_analyzed_bad#iter add_unknown_bad_method;

      let add_unknown_good_method (cmsix:int) =  (* CHANGE to get the length of the array fields *)
	let cms = retrieve_cms cmsix in
	let mInfo = app#get_method cms in
	let cfss = mInfo#get_field_writes in
	List.iter add_unknown_field cfss in
      JCHSystem.jsystem#get_not_analyzed_good#iter add_unknown_good_method

    method private is_initialized (fInfo:field_info_int) =
      let cInfo =
        JCHTypeUtils.get_class_info fInfo#get_class_signature#class_name in
      if fInfo#is_static then
	match class_to_init_st_fields#get cInfo with
	| Some set -> set#has fInfo#get_index
	| None -> false
      else
	match class_to_init_fields#get cInfo with
	| Some set -> set#has fInfo#get_index
	| None -> false

    method private add_to_consts (fInfo:field_info_int) =
      if fInfo#is_static && not (non_consts#has fInfo#get_index) then
	consts#add fInfo#get_index

    method start =
      begin
        self#initialize;
        get_table := new FieldInfoCollections.table_t;
        put_table := new FieldInfoCollections.table_t;
        first_pass := true
      end

    method reset =
      begin
        self#initialize_fields;
        List.iter self#add_to_consts JCHApplication.app#get_fields;
        get_table := !put_table;
        put_table := new FieldInfoCollections.table_t;
        first_pass := false
      end

    method get_all_non_private_fields =
      let add_field
            res
            (fInfo:field_info_int)
            (intervals:interval_list_t) =
	if fInfo#is_private then
          res
	else
          (fInfo, intervals#ints) :: res in
      !put_table#fold add_field []

    method toPretty =
      LBLOCK [
          STR "put_field_table: "; INDENT(5, !put_table#toPretty); NL;
	  STR "get_field_table: "; INDENT(5, !get_table#toPretty); NL]

  end

let int_field_manager =
  new int_field_manager_t

let _class_to_fields =
  new ClassNameCollections.table_t (* class -> fields that are not static or constant *)

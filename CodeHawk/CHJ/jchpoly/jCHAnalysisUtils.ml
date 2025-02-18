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
open CHIntervals
open CHLanguage
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
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

let current_proc_name = ref proc_name_sym
let current_jproc_info = ref None
let set_current_proc_name proc_name =
  current_proc_name := proc_name;
  current_jproc_info := Some (JCHSystem.jsystem#get_jproc_info !current_proc_name)
let get_current_proc_name () = !current_proc_name
let get_current_jproc_info () = Option.get (!current_jproc_info)

let exit_inv = ref (None : CHAtlas.atlas_t option)
let set_exit_invariant inv = exit_inv := Some inv
let get_exit_invariant () = !exit_inv

let jch_op_semantics
      ~(invariant: atlas_t)
      ~(stable: bool)
      ~(fwd_direction: bool)
      ~context:_
      ~(operation: operation_t) =
  let setWriteVarsToTop =
    let write_vars = JCHSystemUtils.get_write_vars operation.op_args in
    if write_vars = [] then
      invariant
    else
      invariant#analyzeFwd (ABSTRACT_VARS write_vars) in
  match operation.op_name#getBaseName with
  | "loop_cond"
  | "check_loop"
  | "save_interval"
  | "v" -> invariant
  | "exit" ->
     if fwd_direction && stable then
       set_exit_invariant invariant
     else
       ();
     invariant
  | "i"
  | "ii" ->
     let mInfo = app#get_method (retrieve_cms !current_proc_name#getSeqNumber) in
     let pc = operation.op_name#getSeqNumber in
     begin
       match mInfo#get_opcode pc with
       | OpBreakpoint                           (* used for debugging only *)
       | OpIfNull _
       | OpIfNonNull _
       | OpIfCmpAEq _
       | OpIfCmpANe _       (* The 3 above are just branches *)
       | OpCheckCast _ ->   (* checks that a ref is of a certain type,
                               return same variable or throws exception. NOT SURE *)
	  invariant
       | _ -> setWriteVarsToTop
     end
  | "e" -> invariant
  | "exn-exit" -> invariant
  | "method-init" -> invariant
  | _ ->
     pr__debug [STR "unknown operation in op_semantics ";
                operation_to_pretty operation; NL;
		pp_list_str operation.op_name#getSymbol; NL];
     setWriteVarsToTop

exception JCH_num_analysis_failure of string

class numeric_run_params_t =
  object
    val analysis_level = ref 1 (* larger level -> more precise analysis *)
    val use_types = ref true   (* if true then use type intervals *)

    (* if true then use only intervals for all analysis form the beginning *)
    val system_use_intervals = ref false

    (* if true then use only intervals if system_use_intervals is true or
     * when the analysis of the proc is too long, etc. *)
    val use_intervals = ref false

    val use_loop_counters = ref true
    val use_lengths = ref true
    val use_overflow = ref true

    (* used in JCHIntervalArray;
     * 80 seemed too large: on xerces,
     * swap space went up to 21GB *)
    val interval_array_size = 50

    val max_number_rays = ref 400

    (* largest coefficient allowed in a constraint *)
    val max_poly_coefficient = ref (big_int_of_int 1000)

    (* maximum number of constraints encountered in the analysis *)
    val max_number_constraints = ref 0

    (* maximum number of constraints allowed *)
    val max_number_constraints_allowed = ref 20

    val max_number_vars_in_constrant_allowed = ref 3

    val number_joins = ref 3;

    val use_time_limits = ref false
    val st_time = ref 0.0
    val max_numeric_analysis_time = ref 500.0
    val drop_constraint_analysis_time = ref 100.0
    val time_limit = ref 0.0
    val drop_constraint_analysis_time_limit = ref 0.0

    (* 0: fine; 1: failed - continue with intervals;
     * 2: retry with intervals;
     * 3: abort - various problems;
     * 10: abort - out of time *)
    val analysis_status = ref 0

    val analysis_failure_reason = ref ""

    val max_swap = ref 1500 (* 20000 *)
    val min_swap_freed = 500 (* 10000 *)
    val swap_increase = 500
    val swap_used = ref 0
    val initial_swap = ref 0
    val create_model = ref false

    method set_analysis_level (n:int) = analysis_level := n

    method analysis_level = !analysis_level

    method set_use_types (b:bool) = use_types := b

    method use_types = !use_types

    method set_system_use_intervals (b:bool) =
      system_use_intervals := b;
      use_intervals := b
    method get_system_use_intervals = !system_use_intervals

    method set_use_intervals (b:bool) =
      begin
        use_intervals := b;
        if b then pr__debug [STR "set use_intervals to true"; NL]
      end

    method use_intervals = !use_intervals

    method set_use_lengths (b:bool) = use_lengths := b

    method use_lengths = !use_lengths

    method set_use_loop_counters (b:bool) = use_loop_counters := b

    method use_loop_counters = !use_loop_counters

    method set_use_overflow (b:bool) = use_overflow := b

    method use_overflow = !use_overflow

    method interval_array_size = interval_array_size

    method set_max_number_rays (n:int) = max_number_rays :=  n

    method max_number_rays = !max_number_rays

    method set_max_poly_coefficient (n:int) =
      max_poly_coefficient :=  big_int_of_int n

    method max_poly_coefficient = !max_poly_coefficient

    method is_good_coefficient n =
      le_big_int n !max_poly_coefficient
      && le_big_int (minus_big_int !max_poly_coefficient) n

    method record_number_constraints (n:int) =
      max_number_constraints := max n !max_number_constraints

    method max_number_constraints = !max_number_constraints

    method set_max_number_constraints_allowed (n:int) =
      max_number_constraints_allowed := n

    method max_number_constraints_allowed = !max_number_constraints_allowed

    method set_max_number_vars_in_constraint_allowed (n:int) =
      max_number_vars_in_constrant_allowed := n

    method max_number_vars_in_constraint_allowed =
      !max_number_vars_in_constrant_allowed

    method reset reset_use_intervals =
      begin
        (if reset_use_intervals then use_intervals := !system_use_intervals);
        max_number_constraints := 0
      end

    method set_number_joins (n:int) = number_joins := n

    method number_joins = !number_joins

    method start_numeric_analysis_time =
      begin
        st_time := Sys.time ();
        time_limit := !st_time +. !max_numeric_analysis_time;
        drop_constraint_analysis_time_limit :=
          !st_time +. !drop_constraint_analysis_time
      end

    method set_use_time_limits (b:bool) = use_time_limits := b

    method set_constraint_analysis_time_limit (n:int) =
      drop_constraint_analysis_time := float n

    method set_numeric_analysis_time_limit (n:int) =
      begin
        pr__debug [STR "set_numeric_analysis_time_limit "; INT n; NL];
        max_numeric_analysis_time := float n
      end

    method reached_constraint_analysis_time_limit =
      Sys.time () > !drop_constraint_analysis_time_limit

    method reached_numeric_analysis_time_limit =
      Sys.time () > !time_limit

    method check_time_limit =
      if not !use_time_limits then
        0
      else if Sys.time () > !time_limit then
	if !use_intervals then
	  begin
	    analysis_status := 10;
	    analysis_failure_reason := "reached analysis time limit";
	    10
	  end
	else
	  begin
	    analysis_status := 1;
	    analysis_failure_reason :=
              "reached analysis time limit with constraints";
	    use_intervals := true;
	    pr_debug [STR "set use_intervals to true"; NL];
	    time_limit :=
              Sys.time()
              +. !drop_constraint_analysis_time; (* give some more time *)
	    1
	  end
      else if Sys.time () > !drop_constraint_analysis_time_limit
              && not !use_intervals then
	begin
	  analysis_status := 1;
	  analysis_failure_reason := "reached constraint analysis time limit";
	  use_intervals := true;
	  pr_debug [STR "set use_intervals to true"; NL];
	  1
	end
      else
        0

    method analysis_failed (status:int) (str:string) =
      begin
        analysis_status := status;
        analysis_failure_reason := str;
        pr__debug [STR "analysis_failed "; INT status; STR (" " ^ str); NL];
        (if status = 1 then use_intervals := true);
        JCH_num_analysis_failure str
      end

    method get_analysis_status = !analysis_status

    method get_analysis_failure_reason = !analysis_failure_reason

    method reset_analysis_failure_status = analysis_status := 0

    method create_model = !create_model

    method set_create_model (b:bool) = create_model := b
  end

let numeric_params = new numeric_run_params_t

let has_untranslated_caller (proc_name:symbol_t) =
  let jproc_info = JCHSystem.jsystem#get_jproc_info proc_name in
  let method_info = jproc_info#get_method_info in
  let callers = method_info#get_callers in
  let untranslated cmsg =
    let mInfo = app#get_method cmsg in
    match mInfo#get_implementation with
    | UntranslatedConcreteMethod _ -> true
    | _ -> false in
  List.exists untranslated callers

let get_slot_interval (slot:logical_stack_slot_int) =
  match slot#get_value#to_interval with
  | Some int -> int
  | _ -> topInterval

(* It could be a collection *)
let is_collection (jproc_info: JCHProcInfo.jproc_info_t) (var:variable_t) =
  let jvar_info = jproc_info#get_jvar_info var in
  JCHTypeUtils.can_be_collection jvar_info#get_types

(* It is for sure an array *)
let is_array (jproc_info:JCHProcInfo.jproc_info_t) (var:variable_t) =
  try
    let var_info = jproc_info#get_jvar_info var in
    let types = var_info#get_types in
    List.for_all JCHTypeUtils.is_array types
  with _ -> false

let is_collection_or_array
      (jproc_info:JCHProcInfo.jproc_info_t) (var:variable_t) =
  is_collection jproc_info var || is_array jproc_info var

(* is number or wrapper or array of numbers
 * Experiment: include all arrays as we need to keep track of the
 * length of arrays in the numeric_info_t *)
let is_numeric (jproc_info:JCHProcInfo.jproc_info_t) (var:variable_t) =
  try
    let var_info = jproc_info#get_jvar_info var in
    var_info#is_numeric || is_array jproc_info var
  with _ -> false

let float_to_interval (f:float) =
  let big_int_of_float (f:float) =
    let s = string_of_float f in
    let s' =
      try
        List.hd (Str.split (Str.regexp_string ".") s)
      with
      | _ ->
         raise
           (JCH_failure
              (LBLOCK [ STR "JCHAnalysisUtils:float_to_interval: ";
                        STR s ]))  in
    big_int_of_string s' in
  let max = new numerical_t (big_int_of_float (ceil f)) in
  let min = new numerical_t (big_int_of_float (floor f)) in
  (min, max, mkInterval min max)

let get_length_vars
      (jproc_info:JCHProcInfo.jproc_info_t) (vars:variable_t list) =
  let vars_with_lengths = ref [] in
  let lengths = ref [] in
  let length_to_var = new VariableCollections.table_t in
  let add_var var =
    try
      let len = Option.get (jproc_info#get_length var) in
      begin
        lengths := len :: !lengths;
        vars_with_lengths := var :: !vars_with_lengths;
        length_to_var#set len var
      end
    with _ -> () in
  begin
    List.iter add_var vars;
    (List.rev !lengths , List.rev !vars_with_lengths, length_to_var)
  end

let include_length_vars
      (jproc_info:JCHProcInfo.jproc_info_t) (vars:variable_t list) =
  let lengths = ref [] in
  let add_var var =
    try
      lengths := (Option.get (jproc_info#get_length var)) :: !lengths
    with _ -> () in
  begin
    List.iter add_var vars;
    vars @ (List.rev !lengths)
  end

let include_all_length_vars
      (jproc_info:JCHProcInfo.jproc_info_t)
      (vars:variable_t list)
      (vs:variable_t list)
      (length_to_array: variable_t VariableCollections.table_t) =
  let v_arrays = length_to_array#listOfValues in
  let lengths = ref [] in
  let lengths_not_included = ref [] in
  let pairs = List.combine vars vs in
  let missing_length_indices = ref [] in
  let length_index = ref (List.length vars) in
  let add_var (var, v) =
    if List.mem v v_arrays then
      match jproc_info#get_length var with
      | Some len -> lengths := len :: !lengths
      | _ ->
         begin
	   lengths_not_included :=
             (JCHSystemUtils.make_length var) :: !lengths_not_included;
	   missing_length_indices := !length_index :: !missing_length_indices;
	   incr length_index
         end in
  begin
    List.iter add_var pairs;
    (vars @ (List.rev !lengths), !lengths_not_included, !missing_length_indices)
  end

(* CHIntervals.div is not integer division *)
let integer_div (int1:interval_t) (int2:interval_t) =
  if int1#isBottom || int2#isBottom then
    bottomInterval
  else if int2#contains numerical_zero then
    topInterval
  else
    begin
      let (a1, b1) = (int1#getMin, int1#getMax) in
      let (a2, b2) = (int2#getMin, int2#getMax) in
      let l = [
          a1#div_floor a2; a1#div_floor b2; b1#div_floor a2; b1#div_floor b2] in
      let min = CHBounds.min_in_bounds l in
      let max = CHBounds.max_in_bounds l in
      if max#lt min then
        bottomInterval
      else
        new interval_t min max
    end

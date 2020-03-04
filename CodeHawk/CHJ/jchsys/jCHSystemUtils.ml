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

(* jchpre *)
open JCHApplication
open JCHIFSystem
open JCHPreAPI

(* jchsys *)
open JCHGlobals
open JCHPrintUtils

module F = CHOnlineCodeSet.LanguageFactory   

let is_number v = 
  match v#getType with
  | NUM_LOOP_COUNTER_TYPE
  | NUM_TMP_VAR_TYPE
  | NUM_VAR_TYPE -> true
  | _ -> false

let is_not_number v = 
  not (is_number v)

let is_constant (v: variable_t) = 
  let name_str = v#getName#getBaseName in
  name_str.[0] == 'c' 

let is_loop_counter (v: variable_t) = 
  let name_str = v#getName#getBaseName in
  name_str.[0] == 'l' && name_str.[1] == 'c'

let is_exception (v: variable_t) = 
  v#getIndex = exception_var_index

let is_not_exception (v: variable_t) = 
  v#getIndex <> exception_var_index 

let is_return (v: variable_t) = 
  let index = v#getIndex in
  index = num_return_var#getIndex
  || index = sym_return_var#getIndex 

let is_not_exception_or_return (v: variable_t) = 
  let index = v#getIndex in
  index <> exception_var_index
  && index <> num_return_var_index
  && index <> sym_return_var_index

let is_temp (v: variable_t) = 
  let name_str_0 = v#getName#getBaseName.[0] in
  name_str_0 == 't' || name_str_0 = '$'

let is_register (v: variable_t) = 
  let name_str = v#getName#getBaseName in
  name_str.[0] = 'r' && not (is_return v)

let is_length (v: variable_t) = 
  v#getName#getBaseName = "length"

let is_stack (v: variable_t) = 
  let name_str = v#getName#getBaseName in
  name_str.[0] = 's'

(* makes a length variable for a variable or field of type array *)
let make_length array = 
  let name = array#getName in
  let length_name =
    new symbol_t
        ~atts:(["v"; name#getBaseName] @ name#getAttributes)
        ~seqnr:name#getSeqNumber "length" in
  new variable_t
      length_name
      ~register:array#isRegister
      ~path:array#getPath NUM_VAR_TYPE 

(* Returns -1 if it is not a register *)
let get_register_index (v: variable_t) = 
  let name = v#getName#getBaseName in
  if name.[0] = 'r' && name.[1] <> 'e' then 
    int_of_string (Str.string_after name 1)
  else -1

(* Returns the list of internal variables corresponding to the 
 * procedure arguments in the signature order *)
let get_signature_vars (procedure: procedure_int) =
  let bindings = procedure#getBindings in
  let get_internal_var (s,_,_) = 
    try
      let (_, v) = List.find  (fun (s', v') -> s#equal s') bindings in
      v 
    with
    | Not_found ->
       raise (JCH_failure
                (LBLOCK [ STR "internal var " ; s#toPretty ; STR " not found in " ;
			  STR "JCHSystemUtils.get_signature_vars" ])) in
  List.map get_internal_var procedure#getSignature 

(* Returns the list of WRITE or READ_WRITE vars in the signature *)
let get_signature_write_vars (procedure: procedure_int) =  
  let internal_vars = get_signature_vars procedure in
  let pairs = List.combine internal_vars procedure#getSignature in 
  let isWrite (v, (_,_,m)) = match m with READ -> false | _ -> true in
  let write_vars = List.filter isWrite pairs in
  List.map fst write_vars 

(* Returns the list of READ or READ_WRITE vars in the signature *)
let get_signature_read_vars  (procedure: procedure_int) =
  let internal_vars = get_signature_vars procedure in
  let pairs = List.combine internal_vars procedure#getSignature in 
  let isRead (v, (_,_,m)) = match m with WRITE -> false | _ -> true in
  let read_vars = List.filter isRead pairs in
  List.map fst read_vars 

let get_return_var (procedure: procedure_int) = 
  let internal_vars = get_signature_vars procedure in
  let pairs = List.combine internal_vars procedure#getSignature in 
  let is_return_p (_, (sym,_,_)) = sym#getIndex = return_sym_index in
  match List.filter is_return_p pairs with 
  | (v,_) :: _ -> Some v
  | [] -> None 

let get_num_return_var (procedure: procedure_int) = 
  match get_return_var procedure with 
  | Some v -> 
      if is_number v then Some v
      else None
  | None -> None 

(* Appends init_comds and final_cmds to code_int *)
let add_cmds
      ~(cms:class_method_signature_int)
      ~(init_cmds:(code_int, cfg_int) command_t list)
      ~(final_cmds:(code_int, cfg_int) command_t list)
      ~(code:code_int):code_int = 
  let new_cmds = ref final_cmds in
  for i = code#length-1 downto 0 do
    new_cmds := (code#getCmdAt i) :: (!new_cmds) 
  done ;
  new_cmds := List.append init_cmds  !new_cmds ;
  chif_system#make_code cms (!new_cmds)
  
(* It assumes that there is only one CFG for each procedure at the top level *)
let get_CFG (procedure:procedure_int) = 
  let rec get_CFG_code code = 
    match code#getCmdAt 0 with
    | RELATION cd -> 
	get_CFG_code cd
    | CFG (_, cfg) -> cfg
    | cmd -> 
	let _ = pr__debug [STR "getCFG "; command_to_pretty 0 cmd; NL] in
	raise (JCH_failure (STR "getCFG expected CODE [CFG cfg; ...] ")) in
  get_CFG_code procedure#getBody

(* Returns the variable corresponding to the given string in the arg list *)
let get_arg_var (str: string) (op_args:(string * variable_t * arg_mode_t) list) =
  let has_this_string (s, _, _) = s = str in
  try
    let (_, v, _) = List.find has_this_string op_args in v
  with
  | Not_found ->
     raise
       (JCH_failure
          (LBLOCK [ STR "op arg with this string " ; STR str ;
		    STR " not found in JCHSystemUtils.get_arg_var" ]))

let get_arg_var_opt
      (str:string) (op_args:(string * variable_t * arg_mode_t) list) =
  let has_this_string (s, _, _) = s = str in
  try 
    let (_, v, _) = List.find has_this_string op_args in 
    Some v
  with _ -> None 

(* A few methods for variables and arguments *)
let is_read_tr (s,v,m) = 
  match m with 
  | WRITE -> false
  | _ -> true

let get_read_vars (args:('a * 'b * arg_mode_t) list):'b list = 
  let read_args = List.filter is_read_tr args in
  List.map (fun (_,v,_) -> v) read_args

let is_just_read_tr (s,v,m) = 
  match m with 
  | READ -> true
  | _ -> false

let get_just_read_vars (args:('a * 'b * arg_mode_t) list):'b list = 
  let read_args = List.filter is_just_read_tr args in
  List.map (fun (_,v,_) -> v) read_args
    
let is_write_tr (s,v,m) = 
  match m with 
  | READ -> false
  | _ -> true

let get_write_vars (args:('a * 'b * arg_mode_t) list):'b list = 
  let write_args = List.filter is_write_tr args in
  List.map (fun (_,v,_) -> v) write_args

let is_just_write_tr (s,v,m) = 
  match m with 
  | WRITE -> true
  | _ -> false

let get_just_write_vars (args:('a * 'b * arg_mode_t) list):'b list = 
  let write_args = List.filter is_just_write_tr args in
  List.map (fun (_,v,_) -> v) write_args
    

let get_bytecode (proc_name:symbol_t) = 
  let mInfo = app#get_method (retrieve_cms proc_name#getSeqNumber) in
  if mInfo#has_bytecode then Some (mInfo#get_bytecode) else None

let copy_procedure (procedure:procedure_int) = 
  let body: code_int = procedure#getBody in
  let new_body = body#clone ~renaming: (fun v -> v) () in
  let new_scope = F.mkScope () in
  new_scope#addVariables procedure#getScope#getVariables ;
  F.mkProcedure 
    procedure#getName 
    ~signature: procedure#getSignature 
    ~bindings: procedure#getBindings 
    ~scope: new_scope
    ~body: new_body

    
let copy_system (system:system_int) = 
  let new_system = F.mkSystem (system#getName) in
  let add_proc proc_name = 
    let procedure = system#getProcedure proc_name in
    new_system#addProcedure (copy_procedure procedure) in
  List.iter add_proc system#getProcedures ;
  new_system

	
let get_first_and_last_in_state
      (method_info:method_info_int) (state : state_int) = 
  let last_seen = ref (-1) in 
  let lowest = ref None in
  let rec walkCode code : unit = 
    for i = 0 to code#length - 1 do
      walkCmd (code#getCmdAt i)
    done
  and walkCmd cmd : unit = 
    match cmd with 
    | CODE (s, code) -> 
	if s#getBaseName = "enter_state" then () 
	else walkCode code 
    | OPERATION op -> 
	begin
	  match op.op_name#getBaseName with 
	  | "i"
	  | "ii"
	  | "v" -> 
	      let pc = op.op_name#getSeqNumber in
	      begin		
		let record () = 
		  last_seen := pc ;
		  (match !lowest with 
		  | Some low_pc -> if pc < low_pc then lowest := Some pc
		  | None -> lowest := Some pc ) in
		match method_info#get_opcode pc with 
		| OpMonitorEnter -> 
		    record ()
		| OpMonitorExit -> 
		    record () 
		| OpIfEq _
		| OpIfNe _
		| OpIfLt _
		| OpIfGe _
		| OpIfGt _
		| OpIfLe _
		| OpIfNull _
		| OpIfNonNull _
		| OpIfCmpEq _
		| OpIfCmpNe _
		| OpIfCmpLt _
		| OpIfCmpGe _
		| OpIfCmpGt _
		| OpIfCmpLe _ 
		| OpIfCmpAEq _
		| OpIfCmpANe _ 
		| OpCmpL -> 
		  last_seen := pc
		| _ -> record ()
	      end
	  | _ -> () 
	end
    | _ -> () 
  in
  walkCode state#getCode ;
  (!lowest, !last_seen)

let get_prev_pcs (method_info:method_info_int) (cfg:cfg_int) (state:state_int) = 
  let prev_pcs = ref [] in
  let visited = new SymbolCollections.set_t in
  let rec get_prev_pc state_name = 
    let state = cfg#getState state_name in
    visited#add state#getLabel ;
    let (_, last) = get_first_and_last_in_state method_info state in
    if last = -1 then 
      begin
	let prevs =
          List.filter (fun s -> not (visited#has s)) state#getIncomingEdges in
	List.iter get_prev_pc prevs 
      end
    else prev_pcs := last :: !prev_pcs in
  List.iter get_prev_pc state#getIncomingEdges ;
  !prev_pcs
  


(* Timing reporting *)	    
let last_time = ref 0.

let start_timing () = 
  last_time := Sys.time () 

let add_timing name = 
  let current_time = Sys.time () in
  let time_elapsed = current_time -. !last_time in
  last_time := current_time ;
  pr_debug [STR "_____________________________"; NL; NL;
	      STR "Finished "; STR name; NL; NL;
	      STR "time_elapsed: "; STR (string_of_float time_elapsed); NL] ; 
  if is_dbg_on () then Gc.print_stat stdout ;
  pr_debug [STR "__________________________________________________________________________"; NL; NL]


exception JCH_outoftime of string

let st_total_time = ref 0.0
let start_total_time () = 
  st_total_time := Sys.time () 
let get_total_time () = 
  Sys.time () -. !st_total_time 

let st_time = ref 0.0
let start_time () = 
  st_time := Sys.time ()
let get_time () = 
  Sys.time () -. !st_time

let sym_to_pc sym = 
  let get_num_str str = 
    let first = Str.search_forward (Str.regexp "[0-9]") str 0 in
    let last = 
      try 
	Str.search_forward (Str.regexp "[a-zA-Z_.-]") str first 
      with 
      | _ -> String.length str in
    String.sub str first (last-first) in
  let num_str = get_num_str sym#getBaseName in
  int_of_string num_str

let profiling_size = 10
let total_times = Array.make profiling_size 0.
let start_times = Array.make profiling_size 0.
let start_profiling_time i = 
  start_times.(i) <- Sys.time ()
      
let stop_profiling_time i = 
  total_times.(i) <- total_times.(i) +. ((Sys.time ()) -. start_times.(i))

let report_profiling_times () = 
  pr__debug [STR "total times: "; NL] ;
  for i = 0 to profiling_size - 1 do
    pr__debug [INT i; STR " "; STR (string_of_float total_times.(i)); NL] ; 
    total_times.(i) <- 0.
  done 

let report_profiling_times_no_reset () = 
  pr__debug [STR "total times: "; NL] ;
  for i = 0 to profiling_size - 1 do
    pr__debug [INT i; STR " "; STR (string_of_float total_times.(i)); NL] ; 
  done 

let is_not_jdk_method proc_name = true

let print_warning_message pp = 
  pr__debug [STR "WARNING: "; pp; NL] 

let print_exception_message pp = 
 pr__debug [STR "EXCEPTION RAISED: "; pp; NL] 

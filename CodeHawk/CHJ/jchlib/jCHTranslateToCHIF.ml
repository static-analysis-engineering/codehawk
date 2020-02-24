(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet
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
open JCHJTerm


module F = CHOnlineCodeSet.LanguageFactory
module H = Hashtbl

let is_system_exit (cn:class_name_int) (msig:method_signature_int) =
  cn#name = "java.lang.System" && msig#name = "exit"
  
let command_pretty_printer = ref CHLanguage.command_to_pretty
let set_command_pretty_printer p = command_pretty_printer := p
let current_cms_index = ref 0
let set_current_method cms = 
  let cms_index = cms#index in
  begin
    F.set_command_pretty_printer (!command_pretty_printer cms_index) ;
    current_cms_index := cms_index
  end

class cmd_list_t (l: (code_int, cfg_int) command_t list) =
object (self: _)

  val mutable cmds = l

  method toPretty = pretty_print_list l (command_to_pretty !current_cms_index) "{" ";" "}"

  method cmd_list = cmds

  method reverse_cmds = cmds <- List.rev cmds

end

let pc_label (pc: int) = "pc=" ^ (string_of_int pc)

let then_symbol pc = new symbol_t ~atts:["then"] (pc_label pc) 
let else_symbol pc = new symbol_t ~atts:["else"] (pc_label pc) 

let initialization_node = "method-initialization"
let normal_exit_node = "normal-exit"
let exceptional_exit_node = "exceptional-exit"
let method_exit_node = "method-exit"

let get_invariant_op_symbol (pc:int) = new symbol_t ~seqnr:pc "v" 

let makeBytecodeOperation
      ?(atts=[]) (pc:int)
      ?(inverted=false)
      (op_args: (string * variable_t * arg_mode_t) list) =
  let s = if inverted then "ii" else "i" in
  let op_name = new symbol_t ~atts ~seqnr:pc s in
  (* let op_args = List.filter (fun (s,_,_) -> not (s = "throw")) op_args in  *)
  OPERATION { op_name = op_name ; op_args = op_args }

let makeExnBytecodeOperation (pc:int) (op_args: (string * variable_t * arg_mode_t) list) =
  let op_name = new symbol_t ~seqnr:pc "e" in
  OPERATION { op_name = op_name ; op_args = op_args }

let node_pool = new StringCollections.table_t
let get_node_symbol s =
  match node_pool#get s with
      Some sym -> sym
    | _ ->
      let sym = new symbol_t s in
      let _ = node_pool#set s sym in
      sym

class bc_graph_t =
object (self: _)
  
  val nodes = new StringCollections.table_t
  val out_n = new StringCollections.table_t
  val in_n = new StringCollections.table_t

  method private probe (n: string) =
    if nodes#has n then
      ()
    else
      begin
	nodes#set n (new cmd_list_t []);
	out_n#set n (new StringCollections.set_t);
	in_n#set n (new StringCollections.set_t)
      end

  method add_node (n: string) (c: (code_int, cfg_int) command_t list) =
    self#probe n;
    self#set_cmd n c

  method get_cmds (n: string) =
    match nodes#get n with
      | Some c -> c
      | None -> raise (JCH_failure (STR "Inconsistency #3 in bytecode graph"))
	
  method set_cmd (n: string) (new_c: (code_int, cfg_int) command_t list) =
    self#probe n;
    match nodes#get n with
      | Some _ -> nodes#set n (new cmd_list_t new_c)
      | None -> raise (JCH_failure (STR "Inconsistency #4 in bytecode graph"))
	
  method get_out_edges (src: string) =
    match out_n#get src with
      | Some s -> s
      | None -> raise (JCH_failure (STR "Inconsistency #1 in bytecode graph"))

  method get_in_edges (tgt: string) =
    match in_n#get tgt with
      | Some s -> s
      | None -> raise (JCH_failure (STR "Inconsistency #2 in bytecode graph"))
	
  method remove_edge (src: string) (tgt: string) =
    match (in_n#get tgt, out_n#get src) with
      | (Some i, Some o) ->
	begin
	  i#remove src;
	  o#remove tgt
	end
      | (_, _) -> ()

  method add_edge (src: string) (tgt: string) =
    self#probe src;
    self#probe tgt;
    (self#get_out_edges src)#add tgt;
    (self#get_in_edges tgt)#add src

  method private compress (entry: string) (exit: string) =
    let seen = new StringCollections.set_t in
    let rec visit s =
      if seen#has s then
	()
      else if s = entry then
	begin
	  seen#add s;
	  let out = self#get_out_edges s in	
	  out#iter (fun s -> visit s)
	end
      else if  (s = exit) || (s = exceptional_exit_node) || (s = normal_exit_node) then
	()
      else    
	let out = (self#get_out_edges s)#clone in
	begin
	  seen#add s;
	  (match (self#get_in_edges s)#singleton with
	    | Some i when (self#get_out_edges i)#size = 1 ->
	      begin
		self#set_cmd i ((self#get_cmds s)#cmd_list @ (self#get_cmds i)#cmd_list);
		self#remove_edge i s;
		let nexts = self#get_out_edges s in
		nexts#iter (fun n ->
		  self#add_edge i n;
		  self#remove_edge s n;
		);
		in_n#remove s;
		out_n#remove s;
		nodes#remove s;
	      end
	    | _ -> ()
	  );
	  out#iter (fun s -> visit s)
	end
    in
    begin
      visit entry;
      nodes#iter (fun _ c -> c#reverse_cmds)
    end
  
  method to_cfg (entry: string) (exit: string): cfg_int =
    let _ = self#compress entry exit in
    let states = (new StringCollections.table_t) in
    let _ = nodes#iter (fun label code -> 
      let in_edges = self#get_in_edges label in
      let out_edges = self#get_out_edges label in
      let state = F.mkState (get_node_symbol label) (F.mkCode code#cmd_list) in
      let _ = out_edges#iter (fun o -> state#addOutgoingEdge (get_node_symbol o)) in
      let _ = in_edges#iter (fun i -> state#addIncomingEdge (get_node_symbol i)) in
      states#set label state
    ) in
    let (entry_state, exit_state) = 
      match (states#get entry, states#get exit) with
	| (Some entry_s, Some exit_s) -> (entry_s, exit_s)
	| (Some _, None) -> raise (JCH_failure (STR "Inconsistency #5 in bytecode graph (no exit)"))
	| (None, Some _) -> 
	      raise (JCH_failure (STR "Inconsistency #5 in bytecode graph (no entry)"))
	| (_, _) -> raise (JCH_failure (STR "Inconsistency #5 in bytecode graph"))
    in
    let cfg = F.mkCFG entry_state exit_state in
    let _ = states#iter (fun _ s -> cfg#addState s) in
    cfg
    
  method to_pretty =
    let ns = nodes#listOfKeys in
    let bc = List.fold_left (fun acc n ->
      (LBLOCK [STR n; STR ":"; NL; (self#get_cmds n)#toPretty; STR " -> ";
	       (self#get_out_edges n)#toPretty; NL]
      ) :: acc) [] ns
    in
    INDENT (2, LBLOCK bc)

end

(* start info gathering for taint analysis, etc *)

(* used in reporting of failed translations *)
let current_proc = ref (new symbol_t "current_method")     
let translation_failed = new SymbolCollections.set_t

(* used in the taint analysis *)

let is_float_type (t: java_basic_type_t) =
  match t with
    | Float | Double -> true
    | _ -> false

let is_void (t: java_basic_type_t) =
  match t with
    | Void -> true
    | _ -> false
      
let translate_java_basic_type (t: java_basic_type_t) =
  match t with
    | Void -> raise (JCH_failure (STR "translate_java_basic_type: void"))
    | Object -> SYM_VAR_TYPE
    | _ -> NUM_VAR_TYPE

let translate_value_type (t: value_type_t) =
  match t with
    | TBasic b -> translate_java_basic_type b
    | TObject TClass cl -> 
	SYM_VAR_TYPE
    | TObject TArray _ -> 
	SYM_VAR_TYPE

let scope = ref (F.mkScope ())

let variable_pool = new SymbolCollections.table_t

let graph = ref (new bc_graph_t)

let opcodes_to_translate: int Queue.t = Queue.create()

let translated_opcodes = ref (new IntCollections.set_t)

let ch_type_to_suffix t =
  match t with
    | SYM_VAR_TYPE -> "sym"
    | NUM_VAR_TYPE -> "num"
    | _ ->  raise (JCH_failure (STR "Unsupported CH type"))
      
let add_variable (name: symbol_t) (t: variable_type_t) : variable_t =
  match (variable_pool)#get name with
    | Some v -> v
    | None -> let v = (!scope)#mkVariable name t in 
	      let _ = (variable_pool)#set name v in
	      v

let make_variable s t =
  let suffix = ch_type_to_suffix t in
  let name = new symbol_t ~atts:[suffix] s in
  add_variable name t
  
let make_stack_variable level pc t =
  let suffix = ch_type_to_suffix t in
  let name = new symbol_t ~atts:[string_of_int pc; suffix] ("s" ^ (string_of_int level)) in
  add_variable name t
		
let make_register_variable n t =
  let suffix = ch_type_to_suffix t in
  let name =   new symbol_t ~atts:[suffix] ("r" ^ (string_of_int n)) in
  add_variable name t 

let get_register_variable n ty =
  make_register_variable n (translate_value_type ty)

let make_field_variable (cn:class_name_int) (fs:field_signature_int) =
  let t = translate_value_type fs#descriptor in
  let suffix = ch_type_to_suffix t in
  let name = cn#name ^ "." ^ fs#name ^ "_field" in
  let name = new symbol_t ~atts:[suffix] name in
  add_variable name t
		
let size_of_java_basic_type (t: java_basic_type_t) =
  match t with
    | Void -> raise (JCH_failure (STR "size_of_java_basic_type: void"))
    | Long | Double -> 2
    | _ -> 1

let size_of_value_type (t: value_type_t) = 
  match t with
    | TBasic b -> size_of_java_basic_type b
    | TObject _ -> 1


let pc_label_then (pc: int) = (pc_label pc) ^ "-then"
let pc_label_else (pc: int) = (pc_label pc) ^ "-else"
let pc_label_case (pc: int) (cst: numerical_t) = (pc_label pc) ^ "-case-" ^ cst#toString
let pc_label_default_case (pc: int) = (pc_label pc) ^ "-default-case"
let pc_label_default_case_low (pc: int) = (pc_label pc) ^ "-default-case-low"
let pc_label_default_case_high(pc: int) = (pc_label pc) ^ "-default-case-high"
let handler_pc_label (pc: int) = (pc_label pc) ^ "-handler"
let return_no_exc_pc_label (pc: int) = (pc_label pc) ^ "-no-exc"
let return_exc_pc_label (pc:int) = (pc_label pc) ^ "-exc"
let exc_handler_pc_label (pc:int) (h:int) = (pc_label pc) ^ "-handler=" ^ (string_of_int h)

type stack_level_t =
  | A of int list                                       (* list of source pc's *)
  | I of java_basic_type_t list * int list             (* source types, source pc's *)
  | TOP

let stack_level_to_ch_type (l: stack_level_t) =
  match l with
    | A _ -> SYM_VAR_TYPE
    | I _ -> NUM_VAR_TYPE
    | TOP -> raise (JCH_failure (STR "stack_level_to_ch_type: TOP"))

let change_stack_level_source (l: stack_level_t) pc = 
  match l with 
  | A _ -> A [pc]
  | I (vts, _) -> I (vts, [pc])
  | TOP -> TOP

let java_basic_type_to_stack t pc =
  match t with
    | Void -> raise (JCH_failure (STR "java_basic_type_to_stack: void"))
    | Double | Long -> [I  ([t],[pc]); TOP]
    | Object -> [A [pc]]
    | _ -> [I ([t],[pc])]

let value_type_to_stack t pc =
  match t with
    | TBasic b -> java_basic_type_to_stack b pc
    | TObject _ -> [A [ pc]]

let var_assign tgt src t =
  if t = NUM_VAR_TYPE then
    ASSIGN_NUM (tgt, NUM_VAR src) 
  else
    ASSIGN_SYM (tgt, SYM_VAR src) 

class destination_info_t = 
  object (self: 'a) 
    val tgt_to_srcs = new VariableCollections.table_t (* tgt -> srcs in stack copies *)
    val destinations : IntCollections.set_t VariableCollections.table_t =
      new VariableCollections.table_t (* variable -> pcs where it is popped off the stack *) 

    method add_destination pc vars = 
      let set_dest var = 
	match destinations#get var with 
	| Some set -> set#add pc
	| _ -> destinations#set var (IntCollections.set_of_list [pc]) in
      List.iter set_dest vars 
				
    method add_copy tgt src = 
      match tgt_to_srcs#get tgt with 
      |	Some set -> set#add src
      |	_ -> tgt_to_srcs#set tgt (VariableCollections.set_of_list [src])
				
    method private add_destinations dests vars = 
      let vars_with_changed_destinations = new VariableCollections.set_t in
      let set_dests var = 
	match destinations#get var with 
	| Some set -> 
	    if not (dests#subset set) then 
	      begin
		set#addSet dests ;
		vars_with_changed_destinations#add var
	      end
	| _ -> 
	    destinations#set var (dests#clone) ;
	    vars_with_changed_destinations#add var in
      if not dests#isEmpty then List.iter set_dests vars ;
      vars_with_changed_destinations 
				
    method get_all_destinations = 
      let init_destinations = destinations#clone in
      let add_dest var dests =  
	let work_set = VariableCollections.set_of_list [var] in
	while not work_set#isEmpty do
	  let v = Option.get work_set#choose in
	  work_set#remove v ;
	  match tgt_to_srcs#get v with 
	  | Some set -> 
	      let vars_with_changed_destinations = self#add_destinations dests set#toList in
	      work_set#addSet vars_with_changed_destinations
	  | None -> () 
	done in
(*
	let rec add_srcs v = 
	  match tgt_to_srcs#get v with 
	  | Some set -> 
	      let vars_with_changed_destinations = self#add_destinations dests set#toList in
	      vars_with_changed_destinations#iter add_srcs 
	  | None -> () in
	add_srcs var in
*)
      init_destinations#iter add_dest ;
      let remove_large var dests = 
	if dests#size > 10 then 
	  destinations#set var (new IntCollections.set_t) in
      destinations#iter remove_large ;
      destinations 
				
  end

let destination_info = ref (new destination_info_t) 
let set_destination pc vars = !destination_info#add_destination pc vars 
let get_all_destinations () = !destination_info#get_all_destinations

class op_stack_t =
object (self: 'a)

  val stack = []  

  method get_contents = stack

  method merge (other:'a) (pc_label:string):'a =
    let otherStack = other#get_contents in
    let join_sources l1 l2 =
      List.fold_left (fun a s -> if List.mem s a then a else s::a) l1 l2 in
    let join_types l1 l2 = 
      List.fold_left (fun a t -> if List.mem t a then a else t::a) l1 l2 in
    let rec aux s1 s2  =
      match (s1, s2) with
      | ([],[]) -> []
      | ((A src1):: tl1, (A src2) :: tl2) -> 
	(A (join_sources src1 src2)) :: (aux tl1 tl2)
      | ((I (ty1,src1)) :: tl1, (I (ty2,src2))::tl2) -> 
	(I (join_types ty1 ty2, join_sources src1 src2)) :: (aux tl1 tl2)
      | (TOP :: tl1, TOP :: tl2) -> TOP :: (aux tl1 tl2)
      | _ -> 
	raise (JCH_failure 
		 (LBLOCK [ STR "Error in merging stacks " ; self#toPretty ; 
			   STR " and " ; other#toPretty ])) in
    let newContents = aux stack otherStack in
    {< stack = newContents >}

  method top = match stack with
    | [] -> raise (JCH_failure (STR ("Empty operand stack #1")))
    | t :: _ -> t

  method push (level: stack_level_t) =
    {< stack = level :: stack >}

  method pushx (levels: stack_level_t list) =
    {< stack = (List.rev levels) @ stack >}

  method popx (n: int) =
    let rec p k l =
      if k = 0 then
	l
      else
	match l with
	  | [] -> raise (JCH_failure (STR ("Empty operand stack #2")))
	  | _ :: l' -> p (k - 1) l'
    in
    {< stack = p n stack >}
    
  method pop = self#popx 1

  method height = List.length stack

  method copy ~(src: int) ~(tgt: int): (code_int, cfg_int) command_t list =
    let abstract_var (var:variable_t) =
      OPERATION { op_name = new symbol_t "dead_vars" ; 
		  op_args = [ ("var", var, READ) ]} in
    let (_, code) = List.fold_left (fun (n, c) l ->
      match l with
	| A _ -> 
	  let tgt_var = make_stack_variable n tgt SYM_VAR_TYPE in
	  let src_var = make_stack_variable n src SYM_VAR_TYPE in
	  let _ = !destination_info#add_copy tgt_var src_var in 
	  (n - 1, (abstract_var src_var) :: (var_assign tgt_var src_var SYM_VAR_TYPE) :: c)
	| I _-> 
	  let tgt_var = make_stack_variable n tgt NUM_VAR_TYPE in
	  let src_var = make_stack_variable n src NUM_VAR_TYPE in
	  let _ = !destination_info#add_copy tgt_var src_var in 
	  (n - 1, (abstract_var src_var) :: (var_assign tgt_var src_var NUM_VAR_TYPE) :: c)
	| TOP -> (n - 1, c)
    ) (self#height, []) stack in
    List.rev code

  method toPretty = pretty_print_list stack 
    (fun l -> match l with 
      | A src -> LBLOCK [ STR "A" ; pretty_print_list src (fun i -> INT i) "[" ";" "]"]
      | I (t,src) -> 
	LBLOCK [ STR "I(" ; 
		 pretty_print_list t (fun ty -> java_basic_type_to_pretty ty) "[" ";" "]" ; 
		 STR ", " ; 
		 pretty_print_list src (fun i -> INT i) "[" ";" "]" ; STR ")" ] 
      | TOP -> STR "TOP") "[" "; " "]"
    
end
  
class stack_table_t =
object (self: _)

  val table: op_stack_t StringCollections.table_t = new StringCollections.table_t

  method set l s =
    match table#get l with
      | Some v -> 
	(try 
	  table#set l (v#merge s l)
	with
	  JCH_failure p ->
	    ch_error_log#add "stack-merge failure" (LBLOCK [ STR l ; STR ": " ; p ]))
      | None -> table#set l s

  method get l = 
    match table#get l with
      | None -> raise (JCH_failure (LBLOCK [STR "Unknown stack at "; STR l]))
      | Some s -> s

  method get_all = table#listOfPairs

  method exists_at l =
    match table#get l with
      | None -> false
      | Some _ -> true
    
end

let stack_table = ref (new stack_table_t)

let exception_handler_table: exception_handler_int list ref = ref []

let exception_var = ref (make_variable "exception" SYM_VAR_TYPE)

let exnExitOperation =
  OPERATION { op_name = new symbol_t "exn-exit" ; 
	      op_args = [ ("throw", !exception_var, READ) ] }

class exn_info_t  className getCode getCatchInfo:exn_info_int =
object
  method get_exception = className
  method get_code = getCode 
  method get_catch_info = getCatchInfo
end

let make_exn_info className getCode getCatchInfo = 
  new exn_info_t className getCode getCatchInfo

let defaultExnInfo = 
  let throwable = make_cn "java.lang.Throwable" in
  make_exn_info throwable (fun _ _ -> []) (fun _ -> MayCatch) 

let defaultExnInfoFn (m:method_int) = 
  let noExns = (fun (_:int) -> []) in
  let defaultExn = (fun (_:int) -> [ defaultExnInfo ]) in
  if m#is_concrete then
    match m#get_implementation with
      Bytecode bc ->
	begin
	  match bc#get_exception_table with
	    [] -> noExns
	  | _ -> defaultExn
	end
    | _ -> noExns
  else
    noExns

let initializationOperation =
  OPERATION { op_name = new symbol_t "method-init" ; op_args = [] }

let simplifier = ref (new JCHSimplify.simplifier_t (F.mkSystem (new symbol_t "?")))

let transformer = ref (new JCHTransform.transformer_t (F.mkSystem (new symbol_t "?")))

let arg_label_store = Hashtbl.create 53
let get_arg_label_symbol i =
  try
    H.find arg_label_store i
  with
      Not_found ->
	let sym = new symbol_t ~atts:[string_of_int i] "arg" in
	begin
	  H.add arg_label_store i sym;
	  sym
	end

let code_label (pc: int) = new symbol_t ~atts:[string_of_int pc] "pc" 
let code_label_no_exc (pc:int) = new symbol_t ~atts:[string_of_int pc] "pc-no-exc"
let code_label_exc (pc:int) (exn:int) = 
  new symbol_t ~atts:[string_of_int pc ; string_of_int exn ] "pc-exc"

let get_stack (pc: int) = 
  (!stack_table)#get (pc_label pc)

let set_stack (pc: int) (s: op_stack_t) =
  (!stack_table)#set (pc_label pc) s
  
let ch_formal_param (n: int) = get_arg_label_symbol n

let return_symbol = new symbol_t "return"
let throw_symbol  = new symbol_t "throw"
let opNegSymbol = new symbol_t "OpNeg"


class logical_stack_slot_t 
  (level:int) 
  (variable:variable_t) 
  (is_double:bool) 
  (vtypes: value_type_t list) 
  (sources: int list) 
  (destinations: IntCollections.set_t VariableCollections.table_t) 
  (is_symbolic:bool) 
  (bytecode_size: int):logical_stack_slot_int =
object (self)

  val mutable taint = TAINT_UNKNOWN
  val mutable value = None

  val destinations = 
    match destinations#get variable with 
    | Some set -> set#toList
    | None -> [-1]

  val mutable types = vtypes
  val mutable transformed_var : variable_t option = None 

  method set_type ts = types <- ts
  method set_taint t = taint <- t
  method set_value v = value <- Some v

  method get_variable = variable
  method set_transformed_variable tr_var = 
    transformed_var <- Some tr_var
  method get_transformed_variable = 
    Option.get transformed_var

  method get_level = level
  method get_taint = taint
  method get_type = types
  method get_sources = sources
  method get_destinations = destinations
  method get_value = match value with Some v -> v | _ ->
    raise (JCH_failure (LBLOCK [ STR "Stack slot does not have a value" ]))

  method is_double_slot = is_double
  method is_numeric  = not is_symbolic
  method is_symbolic = is_symbolic
  method has_value = match value with Some _ -> true | _ -> false

  method to_stack_slot_data = {
      ss_srcs = self#get_sources ;
      ss_dsts = self#get_destinations ;
      ss_level = self#get_level ;
      ss_types = self#get_type ;
      ss_value = match value with Some v -> v | _ -> top_jterm_range }

  method toPretty =
    let pTypes = CHPrettyUtil.fixed_length_pretty 
      (pretty_print_list self#get_type (fun ty -> value_type_to_pretty ty) "[" ";" "]") 9 in
    let pSources = CHPrettyUtil.fixed_length_pretty
      (pretty_print_list self#get_sources (fun s -> INT s) "[" ";" "]") 9 in
    let pDestination = CHPrettyUtil.fixed_length_pretty 
      (pretty_print_list destinations (fun s -> INT s) "[" ";" "]") 9 in
    let pVariable = CHPrettyUtil.fixed_length_pretty (variable#toPretty) 12 in
    let pValue = match value with Some v -> 
      LBLOCK [ STR " value: " ; v#toPretty ] | _ -> STR "" in
    let pTrVariable = match transformed_var with Some var -> 
      LBLOCK [STR " ("; var#toPretty; STR ") "] |_ -> STR " " in

    LBLOCK [ CHPrettyUtil.fixed_length_pretty ~alignment:StrRight (INT level) 3 ; 
	     STR (if is_double then " D " else " S ") ; 
	     pSources ; STR " "; pDestination ; STR "  " ; pVariable ; pTrVariable; 
	     pTypes ; pValue ]
end


class stack_layout_t 
  (stack:op_stack_t) 
  (pc:int) 
  (destinations: IntCollections.set_t VariableCollections.table_t) 
  (bytecode_size: int):op_stack_layout_int =
object (self)
  val slots = 
    let table = new IntCollections.table_t in
    let contents = stack#get_contents in
    let isDoubleSlot = ref false in
    let (_,slots) = List.fold_left (fun (n, acc) l ->
      match l with
      | A sources -> 
	let var = make_stack_variable n pc SYM_VAR_TYPE in
	let slot = new logical_stack_slot_t n var false 
	  [TBasic Object] sources destinations true bytecode_size in
	(n - 1, slot :: acc)
      | I (types,sources) ->
	let var = make_stack_variable n pc NUM_VAR_TYPE in
	let vtypes = List.map (fun jbt -> TBasic jbt) types in
	let slot = new logical_stack_slot_t n var !isDoubleSlot vtypes sources 
	  destinations false bytecode_size in
	let _ = isDoubleSlot := false in
	(n - 1, slot :: acc)
      | TOP -> begin isDoubleSlot := true ; (n - 1, acc) end 
    ) (List.length contents, []) contents in
    let _ = List.iter (fun s -> table#set s#get_level s) slots in
    table

  method get_size = slots#size

  method get_slots = slots#listOfValues 

  method get_top_slots (n:int) =
    if n > self#get_size then
      raise (JCH_failure
               (LBLOCK [ STR "Requested top slots: " ; INT n ; 
			 STR " (available: " ; INT self#get_size ; STR ")" ;
                         NL ; self#toPretty ]))
    else
      let slotlst = 
	List.sort (fun (i1,_) (i2,_) -> Pervasives.compare i2 i1) slots#listOfPairs in
      let rec aux l i result =
	if i = 0 then 
	  result
	else
	  aux (List.tl l) (i-1) ((List.hd l)::result) in
      List.map snd (List.rev (aux slotlst n []))

  method get_top_slot =
    let topIndex = 
      match slots#listOfKeys with
      | [] -> raise (JCH_failure (LBLOCK [ STR "get_top_slot: Stack is empty"]))
      | l -> List.hd (List.sort (fun i1 i2 -> Pervasives.compare i2 i1) l) in
    self#get_slot topIndex

  method get_levels = 
    if slots#size = 0 then 0 else
      let topSlot = self#get_top_slot in
      if topSlot#is_double_slot then (topSlot#get_level + 1) else topSlot#get_level

  method get_slot (level:int) =
    match slots#get level with
    | Some s -> s
    | _ -> raise (JCH_failure (LBLOCK [ 
      STR "Stack layout at pc = " ; INT pc ; STR " does not have level " ; 
      INT level ; STR " (" ; INT self#get_size ; STR " levels found)" ]))

  method get_slot_for_variable (v:variable_t) =
    try
      List.find (fun s -> s#get_variable#equal v) slots#listOfValues
    with
    | Not_found ->
      raise (JCH_failure
               (LBLOCK [ STR "No logical stack slot found for " ; v#toPretty ]))

  method has_slot_for_variable (v:variable_t) =
    List.exists (fun s -> s#get_variable#equal v) slots#listOfValues

  method has_slot (level:int) = slots#has level

  method toPretty = 
    let p = ref [] in
    let _ = slots#iter (fun _ s -> p := (LBLOCK [ s#toPretty ; NL]) :: !p) in
    LBLOCK !p

end

class method_stack_layout_t 
  (stack_layouts:(int * stack_layout_t) list)
  (local_var_table: (int * int * string * value_type_t * int) list option) : method_stack_layout_int =
object

  val layouts = 
    let table = new IntCollections.table_t in
    let _ = List.iter (fun (pc,layout) -> table#set pc layout) stack_layouts in
    table
  val mutable local_variable_table =
    match local_var_table with 
    | Some table -> 
       Some (List.map (fun (s,l,n,t,i) -> (s,l,n,[t],i)) table)
    | _ -> None 

  method set_local_variable_table table = 
    local_variable_table <- Some table 

  method get_stack_layout (pc:int) = 
    match layouts#get pc with
      Some layout -> layout
    | _ -> raise (JCH_failure (LBLOCK [ STR "No stack layout found at pc = " ; INT pc ]))

  method get_stack_layouts = layouts#listOfValues

  method get_local_variable_table = local_variable_table
      
  method has_stack_layout (pc:int) = layouts#has pc

  method get_pc_stack_layouts = layouts#listOfPairs

  method toPretty = 
    let p = ref [] in
    let _ = layouts#iter (fun pc layout -> 
      p := (LBLOCK [ NL ; STR "pc = " ; INT pc ; NL ; 
		     INDENT (3, layout#toPretty ) ]) :: !p) in
    let local_var_table_p = 
      match local_variable_table with 
      | Some list -> 
	  let pp_var_table_line (start, len, name, vt, ind) = 
	    LBLOCK [INT start; STR " "; INT len; STR (" "^ name ^ " "); 
		     pretty_print_list vt value_type_to_pretty "{" ", " "} "; 
		     INT ind; NL] in
	  LBLOCK (List.map pp_var_table_line list) 
      | None -> (STR "") in
    LBLOCK [LBLOCK (List.rev !p); NL; STR "local_var_table: "; 
	    NL; local_var_table_p; NL] 

end


let translate_arg_bindings 
    (pc: int) 
    (pc': int) 
    (has_this: bool) 
    (stack: op_stack_t) 
    (signature: method_signature_int)=
  let rec loop s a n h l =
    if n < 0 then
      (l, s)
    else
      match s#top with
      | I _ ->
	let stack_var = make_stack_variable h pc NUM_VAR_TYPE in
 	set_destination pc [stack_var] ;
	loop s#pop (a - 1) (n - 1) (h - 1) ((ch_formal_param a, stack_var) :: l)
      | A _  -> 
	let stack_var = make_stack_variable h pc SYM_VAR_TYPE in
	set_destination pc [stack_var] ;
	loop s#pop (a - 1) (n - 1) (h - 1) ((ch_formal_param a, stack_var) :: l)
      | TOP -> 
	let stack_var = make_stack_variable (h - 1) pc NUM_VAR_TYPE in
	set_destination pc [stack_var] ;
	loop (s#popx 2) (a - 1) (n - 1) (h - 2) ((ch_formal_param a, stack_var) :: l)
  in
  let descriptor = signature#descriptor in
  let nargs = if has_this then 
      List.length descriptor#arguments
    else
      List.length descriptor#arguments - 1
  in
  try
  let (arg_bindings', inv_stack) = loop stack nargs nargs stack#height [] in
  let arg_bindings = (throw_symbol, !exception_var) :: arg_bindings' in
    match descriptor#return_value with	  
    | None | Some (TBasic Void) -> (arg_bindings, inv_stack, inv_stack)
    | Some t -> 
      let ch_type = translate_value_type t in
      let stack_var = make_stack_variable (inv_stack#height + 1) pc' ch_type in
      ((return_symbol, stack_var) :: 
	  arg_bindings, inv_stack, inv_stack#pushx (value_type_to_stack t pc))
  with
    JCH_failure p ->
      begin
	ch_error_log#add "stack corruption"
	  (LBLOCK [ STR "arg bindings: " ; signature#toPretty ; STR "; pc = " ; INT pc ; 
		    STR ": " ; p ; NL ;
		    INDENT (3, stack#toPretty) ]) ;
	raise (JCH_failure (LBLOCK [ STR "arg bindings: " ; 
				     signature#toPretty ; STR ": " ; p ]))
      end

let get_exception_handlers pc =
  List.fold_left (fun a h ->
      if h#h_start <= pc && pc < h#h_end then h#handler :: a else a) [] (!exception_handler_table)

let get_exception_handler_infos pc = 
  List.rev
    (List.fold_left (fun a h -> if h#h_start <= pc && pc < h#h_end then h::a else a) 
       [] (!exception_handler_table))
		  
let translate_opcode 
    ~(exn_infos:exn_info_int list)
    ~(java_method:method_int)
    ~(pc:int) 
    ~(normal_exit: string) 
    ~(exceptional_exit: string) 
    ~(code: opcodes_int) 
    ~(bytecode: bytecode_int) =
  let opcode = code#at pc in 
  if (!translated_opcodes)#has pc then
    ()
  else if opcode = OpInvalid then
    ()
  else if not((!stack_table)#exists_at (pc_label pc)) then
    chlog#add "dead code"  
      (LBLOCK [ java_method#get_class_method_signature#toPretty ; STR " ; pc="; INT pc ])
  else
    let next_pc () =
      let rec loop i =
	if i = code#length then
	  raise (JCH_failure (STR "Inconsistent bytecode #1"))
	else if i > code#length then
	  begin
	    ch_error_log#add "inconsistent bytecode" (LBLOCK [ STR "Next pc is " ; INT i ]) ;
	    raise (JCH_failure (LBLOCK [ STR "Next pc is " ; INT i ]))
	  end
	else if (code#at i) = OpInvalid then
	  loop (i + 1)
	else
 	  let _ = Queue.add i opcodes_to_translate in
	  i
      in
      loop (pc + 1)
    in
    let add_exn_to_cfg (pc:int) (pc':int) (args:op_arg_t list) commands =
      let handlers = get_exception_handler_infos pc in
      (* let args = List.filter (fun (s,_,m) -> s = "throw" || m = READ) args in
         let exnOp = makeExnBytecodeOperation pc args in *)
      let noExnNode = return_no_exc_pc_label pc in
      let thisNode = pc_label pc in
      let nextNode = pc_label pc' in
      let make_exn_node exnId hNode code = 
	let exnNode = (pc_label pc) ^ "-to-" ^ hNode ^ "-for-" ^ (string_of_int exnId) in
	begin
	  let code = CODE (code_label_exc pc exnId, F.mkCode code) in
	  (!graph)#add_node exnNode [ code ] ;
	  (!graph)#add_edge thisNode exnNode ;
	  (!graph)#add_edge exnNode hNode
	end in
      begin
	let noExnCode = CODE (code_label_no_exc pc, F.mkCode commands) in
	(!graph)#add_node noExnNode [ noExnCode ] ;
	(!graph)#add_edge thisNode noExnNode ;
	(!graph)#add_edge noExnNode nextNode ;
	List.iter (fun exnInfo ->
	  let caught = ref false in
	  let exnId = exnInfo#get_exception#index in
	  begin
	    List.iter (fun handler ->
	      if !caught then () else
	      begin
		match handler#catch_type with
		  None ->
		    begin
		      make_exn_node exnId (handler_pc_label handler#handler) 
		        (exnInfo#get_code !scope !exception_var) ;
		      caught := true
		    end
		| Some cn ->
		  match exnInfo#get_catch_info cn with
		    WillCatch ->
		      begin
			make_exn_node exnId (handler_pc_label handler#handler) 
			  (exnInfo#get_code !scope !exception_var) ;
			caught := true
		      end
		  | MayCatch ->
		    make_exn_node exnId (handler_pc_label handler#handler) 
		      (exnInfo#get_code !scope !exception_var)
		  | _ -> ()
	      end ) handlers ;
	    if !caught then () else
	      make_exn_node exnId exceptional_exit (exnInfo#get_code !scope !exception_var)
	  end) exn_infos
      end in
    let translate_invoke_operation opcode signature =
      let stack = get_stack pc in
      let pc' = next_pc () in	
      let has_this = match opcode with OpInvokeStatic _ | OpInvokeDynamic _ -> false | _ -> true in  
      let (bindings, inv_stack, stack') = 
	translate_arg_bindings pc pc' has_this stack signature in
      let op_args =
	(List.map (fun (p, v) -> (String.concat "" p#getSymbol, v, 
				  match p#getSymbol with
				  | "return" :: _ | "throw" :: _ -> WRITE 
				  | _ -> READ)) bindings) in
      let _ = set_stack pc' stack' in
      let op = makeBytecodeOperation pc op_args in 
      let _ = add_exn_to_cfg pc pc' op_args (op :: (inv_stack#copy pc pc')) in
      [  ]
	  
    in
    let cmds =  (* A list of  CHIF instructions followed by the bytecode operation followed by the ASSIGNs that copy the stack *)
      match opcode with
	(* Local variable manipulations *)
	| OpLoad (t, n) ->
	  let stack = get_stack pc in
	  let stack' = stack#pushx (java_basic_type_to_stack t pc) in	  
	  let ch_type = translate_java_basic_type t in
	  let pc' = next_pc () in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable (stack#height + 1) pc' ch_type in
	  let reg = make_register_variable n ch_type in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var, READ) ; ("src1", reg, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (var_assign stack_var reg ch_type) :: op :: (stack#copy pc pc')
	| OpStore (t, n) ->
	  let stack = get_stack pc in
	  let t_size = size_of_java_basic_type t in
	  let stack' = stack#popx t_size in	  
	  let ch_type = translate_java_basic_type t in
	  let pc' = next_pc () in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable (stack#height - t_size + 1) pc ch_type in
	  let _ = set_destination pc [stack_var] in
	  let reg = make_register_variable n ch_type in
	  let op_args = [ ("dst1", reg, READ) ; ("src1", stack_var, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  (var_assign reg stack_var ch_type) :: op :: (stack'#copy pc pc')
	| OpIInc (r, c) ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let _ = set_stack pc' stack in
	  let reg = make_register_variable r NUM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("src_dst", reg, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (INCREMENT (reg, mkNumerical c)) :: op :: (stack#copy pc pc')

	(* Stack permutation *)
	| OpPop ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack_var = 
	    let t = stack#top in
	    let ch_type = stack_level_to_ch_type t in
	    let stack_var = make_stack_variable stack#height pc ch_type in
	    begin
	      set_destination pc [stack_var] ;
	      stack_var
	    end in
	  let stack' = stack#pop in
	  let _ = set_stack pc' stack' in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("src", stack_var, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (stack'#copy pc pc')
	| OpPop2 ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let _ = 
	    match stack#get_contents with
	    | TOP :: TOP :: _
	    | _ :: TOP :: _ -> ch_error_log#add "stack corruption" (LBLOCK [ stack#toPretty]) 
	    | TOP :: t :: _-> 
		let ch_type = stack_level_to_ch_type t in
		let stack_var = make_stack_variable (stack#height - 1) pc ch_type in
		set_destination pc [stack_var]
	    | t1 :: t2 :: _-> 
		let ch_type = stack_level_to_ch_type t1 in
		let stack_var1 = make_stack_variable stack#height pc ch_type in
		let ch_type = stack_level_to_ch_type t2 in
		let stack_var2 = make_stack_variable (stack#height - 1) pc ch_type in
		set_destination pc [stack_var1; stack_var2] 
	    | _ -> () in
	  let stack' = stack#popx 2 in 
	  let _ = set_stack pc' stack' in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op = makeBytecodeOperation pc [] in
	  op :: (stack'#copy pc pc')
	| OpDup ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let t = stack#top in
	  let ch_type = stack_level_to_ch_type t in
	  let stack' = stack#push (change_stack_level_source t pc) in
	  let _ = set_stack pc' stack' in
	  let stack_var_1 = make_stack_variable stack#height pc ch_type in
	  let stack_var_2 = make_stack_variable stack'#height pc' ch_type in
	  set_destination pc [stack_var_1] ;
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var_2, READ) ; ("src1", stack_var_1, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (var_assign stack_var_2 stack_var_1 ch_type) :: op :: (stack#copy pc pc')
	| OpDupX1 ->
	  let stack_1 = get_stack pc in
	  let pc' = next_pc () in
	  let t_1 = stack_1#top in
	  let ch_type_1 = stack_level_to_ch_type t_1 in
	  let stack_var_1 = make_stack_variable stack_1#height pc ch_type_1 in
	  let stack_2 = stack_1#pop in
	  let t_2 = stack_2#top in
	  let ch_type_2 = stack_level_to_ch_type t_2 in
	  let stack_var_2 = make_stack_variable stack_2#height pc ch_type_2 in
	  set_destination pc [stack_var_1; stack_var_2] ;
	  let inv_stack = stack_2#pop in
	  let stack' = inv_stack#pushx [change_stack_level_source t_1 pc; t_2 ; t_1] in
	  let _ = set_stack pc' stack' in
	  let stack_var_1' = make_stack_variable stack'#height pc' ch_type_1 in
	  let stack_var_2' = make_stack_variable (stack'#height - 1) pc' ch_type_2 in
	  let stack_var_3' = make_stack_variable (stack'#height - 2) pc' ch_type_1 in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var_1', READ) ;
			  ("src1", stack_var_1 , READ) ;
			  ("dst2", stack_var_2', READ) ;
			  ("src2", stack_var_2 , READ) ;
			  ("dst3", stack_var_3', READ) ;
			  ("src3", stack_var_1 , READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  [var_assign stack_var_1' stack_var_1 ch_type_1;
	   var_assign stack_var_2' stack_var_2 ch_type_2;
	   var_assign stack_var_3' stack_var_1 ch_type_1;
	   op 
	  ] @ (inv_stack#copy pc pc')
	| OpDupX2 ->
	  let stack_1 = get_stack pc in
	  let pc' = next_pc () in
	  let t_1 = stack_1#top in
	  let ch_type_1 = stack_level_to_ch_type t_1 in
	  let stack_var_1 = make_stack_variable stack_1#height pc ch_type_1 in
	  let stack_2 = stack_1#pop in
	  if stack_2#top = TOP then
	    let stack_2' = stack_2#pop in
	    let t_2 = stack_2'#top in
	    let ch_type_2 = stack_level_to_ch_type t_2 in
	    let stack_var_2 = make_stack_variable stack_2'#height pc ch_type_2 in
	    set_destination pc [stack_var_1; stack_var_2]  ;
	    let inv_stack = stack_2'#pop in
	    let stack' = inv_stack#pushx [change_stack_level_source t_1 pc; t_2; TOP; t_1] in
	    let _ = set_stack pc' stack' in
	    let stack_var_1' = make_stack_variable stack'#height pc' ch_type_1 in
	    let stack_var_2' = make_stack_variable (stack'#height - 2) pc' ch_type_2 in
	    let stack_var_3' = make_stack_variable (stack'#height - 3) pc' ch_type_1 in
	    let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	    let op_args = [ ("dst1", stack_var_1', READ) ;
			    ("src1", stack_var_1 , READ) ;
			    ("dst2", stack_var_2', READ) ;
			    ("src2", stack_var_2 , READ) ;
			    ("dst3", stack_var_3', READ) ;
			    ("src3", stack_var_1 , READ)  ] in
	    let op = makeBytecodeOperation pc op_args in
	    [var_assign stack_var_1' stack_var_1 ch_type_1;
	     var_assign stack_var_2' stack_var_2 ch_type_2;
	     var_assign stack_var_3' stack_var_1 ch_type_1;
	     op
	    ] @ (inv_stack#copy pc pc')
	  else
	    let t_2 = stack_2#top in
	    let ch_type_2 = stack_level_to_ch_type t_2 in
	    let stack_var_2 = make_stack_variable stack_2#height pc ch_type_2 in
	    let stack_3 = stack_2#pop in
	    let t_3 = stack_3#top in
	    let ch_type_3 = stack_level_to_ch_type t_3 in
	    let stack_var_3 = make_stack_variable stack_3#height pc ch_type_3 in
	    set_destination pc [stack_var_1; stack_var_2; stack_var_3]  ;
	    let inv_stack = stack_3#pop in
	    let stack' = inv_stack#pushx [change_stack_level_source t_1 pc; t_3; t_2; t_1] in
	    let _ = set_stack pc' stack' in
	    let stack_var_1' = make_stack_variable stack'#height pc' ch_type_1 in
	    let stack_var_2' = make_stack_variable (stack'#height - 1) pc' ch_type_2 in
	    let stack_var_3' = make_stack_variable (stack'#height - 2) pc' ch_type_3 in
	    let stack_var_4' = make_stack_variable (stack'#height - 3) pc' ch_type_1 in
	    let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	    let op_args = [ ("dst1", stack_var_1', READ) ;
			    ("src1", stack_var_1 , READ) ;
			    ("dst2", stack_var_2', READ) ;
			    ("src2", stack_var_2 , READ) ;
			    ("dst3", stack_var_3', READ) ;
			    ("src3", stack_var_3 , READ) ;
			    ("dst4", stack_var_4', READ) ;
			    ("src4", stack_var_1 , READ) ] in
	    let op = makeBytecodeOperation pc op_args in
	    [var_assign stack_var_1' stack_var_1 ch_type_1;
	     var_assign stack_var_2' stack_var_2 ch_type_2;
	     var_assign stack_var_3' stack_var_3 ch_type_3;
	     var_assign stack_var_4' stack_var_1 ch_type_1;
	     op
	    ] @ (inv_stack#copy pc pc')
	| OpDup2 ->
	  let stack_1 = get_stack pc in
	  let pc' = next_pc () in
	  let t_1 = stack_1#top in
	  if t_1 = TOP then
	    let stack = stack_1#pop in
	    let t = stack#top in
	    let ch_type = stack_level_to_ch_type t in
	    let stack_var = make_stack_variable stack#height pc ch_type in	    
	    set_destination pc [stack_var]  ;
	    let inv_stack = stack#pop in
	    let stack' = inv_stack#pushx [t; TOP; change_stack_level_source t pc; TOP] in
	    let _ = set_stack pc' stack' in
	    let stack_var_1' = make_stack_variable (stack'#height - 1) pc' ch_type in
	    let stack_var_2' = make_stack_variable (stack'#height - 3) pc' ch_type in
	    let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	    let op_args = [ ("dst1", stack_var_1', READ) ;
			    ("src1", stack_var   , READ) ;
			    ("dst2", stack_var_2', READ) ;
			    ("src2", stack_var   , READ) ] in
	    let op = makeBytecodeOperation pc op_args in
	    [var_assign stack_var_1' stack_var ch_type;
	     var_assign stack_var_2' stack_var ch_type;
	     op
	    ] @ (inv_stack#copy pc pc')
	  else
	    let ch_type_1 = stack_level_to_ch_type t_1 in
	    let stack_var_1 = make_stack_variable stack_1#height pc ch_type_1 in	    
	    let stack_2 = stack_1#pop in
	    let t_2 = stack_2#top in
	    let ch_type_2 = stack_level_to_ch_type t_2 in
	    let stack_var_2 = make_stack_variable stack_2#height pc ch_type_2 in
	    set_destination pc [stack_var_1; stack_var_2]  ;
	    let inv_stack = stack_2#pop in
	    let stack' = inv_stack#pushx [t_2; t_1; change_stack_level_source t_2 pc ; change_stack_level_source t_1 pc] in
	    let _ = set_stack pc' stack' in
	    let stack_var_1' = make_stack_variable stack'#height pc' ch_type_1 in
	    let stack_var_2' = make_stack_variable (stack'#height - 1) pc' ch_type_2 in
	    let stack_var_3' = make_stack_variable (stack'#height - 2) pc' ch_type_1 in
	    let stack_var_4' = make_stack_variable (stack'#height - 3) pc' ch_type_2 in
	    let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	    let op_args = [ ("dst1", stack_var_1', READ) ;
			    ("src1", stack_var_1 , READ) ;
			    ("dst2", stack_var_2', READ) ;
			    ("src2", stack_var_2 , READ) ;
			    ("dst3", stack_var_3', READ) ;
			    ("src3", stack_var_1 , READ) ;
			    ("dst4", stack_var_4', READ) ;
			    ("src4", stack_var_2 , READ) ] in
	    let op = makeBytecodeOperation pc op_args in
	    [var_assign stack_var_1' stack_var_1 ch_type_1;
	     var_assign stack_var_2' stack_var_2 ch_type_2;
	     var_assign stack_var_3' stack_var_1 ch_type_1;
	     var_assign stack_var_4' stack_var_2 ch_type_2;
	     op
	    ] @ (inv_stack#copy pc pc')
	| OpDup2X1 ->
	  let stack_1 = get_stack pc in
	  let pc' = next_pc () in
	  let t_1 = stack_1#top in
	  if t_1 = TOP then
	    let stack_1' = stack_1#pop in
	    let t_1' = stack_1'#top in
	    let ch_type_1 = stack_level_to_ch_type t_1' in
	    let stack_var_1 = make_stack_variable stack_1'#height pc ch_type_1 in
	    let stack_2 = stack_1'#pop in
	    let t_2 = stack_2#top in
	    let ch_type_2 = stack_level_to_ch_type t_2 in
	    let stack_var_2 = make_stack_variable stack_2#height pc ch_type_2 in
	    set_destination pc [stack_var_1; stack_var_2]  ;
	    let inv_stack = stack_2#pop in
	    let stack' = inv_stack#pushx [change_stack_level_source t_1' pc; TOP; t_2; t_1'; TOP] in
	    let _ = set_stack pc' stack' in
	    let stack_var_1' = make_stack_variable (stack'#height - 1) pc' ch_type_1 in
	    let stack_var_2' = make_stack_variable (stack'#height - 2) pc' ch_type_2 in
	    let stack_var_3' = make_stack_variable (stack'#height - 4) pc' ch_type_1 in
	    let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	    let op_args = [ ("dst1", stack_var_1', READ) ;
			    ("src1", stack_var_1 , READ) ;
			    ("dst2", stack_var_2', READ) ;
			    ("src2", stack_var_2 , READ) ;
			    ("dst3", stack_var_3', READ) ;
			    ("src3", stack_var_1 , READ) ] in
	    let op = makeBytecodeOperation pc op_args in
	    [var_assign stack_var_1' stack_var_1 ch_type_1;
	     var_assign stack_var_2' stack_var_2 ch_type_2;
	     var_assign stack_var_3' stack_var_1 ch_type_1;
	     op
	    ] @ (inv_stack#copy pc pc')	    
	  else
	    let ch_type_1 = stack_level_to_ch_type t_1 in
	    let stack_var_1 = make_stack_variable stack_1#height pc ch_type_1 in	    
	    let stack_2 = stack_1#pop in
	    let t_2 = stack_2#top in
	    let ch_type_2 = stack_level_to_ch_type t_2 in
	    let stack_var_2 = make_stack_variable stack_2#height pc ch_type_2 in
	    let stack_3 = stack_2#pop in
	    let t_3 = stack_3#top in
	    let ch_type_3 = stack_level_to_ch_type t_3 in
	    let stack_var_3 = make_stack_variable stack_3#height pc ch_type_3 in
	    set_destination pc [stack_var_1; stack_var_2; stack_var_3]  ;
	    let inv_stack = stack_3#pop in
	    let stack' = inv_stack#pushx [change_stack_level_source t_2 pc; change_stack_level_source t_1 pc; t_3; t_2; t_1] in
	    let _ = set_stack pc' stack' in
	    let stack_var_1' = make_stack_variable stack'#height pc' ch_type_1 in
	    let stack_var_2' = make_stack_variable (stack'#height - 1) pc' ch_type_2 in
	    let stack_var_3' = make_stack_variable (stack'#height - 2) pc' ch_type_3 in
	    let stack_var_4' = make_stack_variable (stack'#height - 3) pc' ch_type_1 in
	    let stack_var_5' = make_stack_variable (stack'#height - 4) pc' ch_type_2 in
	    let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	    let op_args = [ ("dst1", stack_var_1', READ) ;
			    ("src1", stack_var_1 , READ) ;
			    ("dst2", stack_var_2', READ) ;
			    ("src2", stack_var_2 , READ) ;
			    ("dst3", stack_var_3', READ) ;
			    ("src3", stack_var_3 , READ) ;
			    ("dst4", stack_var_4', READ) ;
			    ("src4", stack_var_1 , READ) ;
			    ("dst5", stack_var_5', READ) ;
			    ("src5", stack_var_2 , READ) ] in
	    let op = makeBytecodeOperation pc op_args in
	    [var_assign stack_var_1' stack_var_1 ch_type_1;
	     var_assign stack_var_2' stack_var_2 ch_type_2;
	     var_assign stack_var_3' stack_var_3 ch_type_3;
	     var_assign stack_var_4' stack_var_1 ch_type_1;
	     var_assign stack_var_5' stack_var_2 ch_type_2;
	     op
	    ] @ (inv_stack#copy pc pc')	    
	| OpDup2X2 ->
	  let stack_1 = get_stack pc in
	  let pc' = next_pc () in
	  let t_1 = stack_1#top in
	  if t_1 = TOP then (* Forms 2 & 4 *)
	    let stack_1' = stack_1#pop in
	    let t_1' = stack_1'#top in
	    let ch_type_1 = stack_level_to_ch_type t_1' in
	    let stack_var_1 = make_stack_variable stack_1'#height pc ch_type_1 in	    
	    let stack_2 = stack_1#pop in
	    let t_2 = stack_2#top in
	    if t_2 = TOP then (* Form 4*)
	      let stack_2' = stack_2#pop in
	      let t_2' = stack_2'#top in
	      let ch_type_2 = stack_level_to_ch_type t_2' in
	      let stack_var_2 = make_stack_variable stack_2'#height pc ch_type_2 in	    
	      set_destination pc [stack_var_1; stack_var_2]  ;
	      let inv_stack = stack_2'#pop in
	      let stack' = inv_stack#pushx [change_stack_level_source t_1' pc; TOP; t_2'; TOP; t_1'; TOP] in
	      let _ = set_stack pc' stack' in
	      let stack_var_1' = make_stack_variable (stack'#height - 1) pc' ch_type_1 in
	      let stack_var_2' = make_stack_variable (stack'#height - 3) pc' ch_type_2 in
	      let stack_var_3' = make_stack_variable (stack'#height - 5) pc' ch_type_1 in
	      let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	      let op_args = [ ("dst1", stack_var_1', READ) ;
			      ("src1", stack_var_1 , READ) ;
			      ("dst2", stack_var_2', READ) ;
			      ("src2", stack_var_2 , READ) ;
			      ("dst3", stack_var_3', READ) ;
			      ("src3", stack_var_1 , READ) ] in
	      let op = makeBytecodeOperation pc op_args in
	      [var_assign stack_var_1' stack_var_1 ch_type_1;
	       var_assign stack_var_2' stack_var_2 ch_type_2;
	       var_assign stack_var_3' stack_var_1 ch_type_1;
	       op
	      ] @ (inv_stack#copy pc pc')	      	      	      
	    else (* Form 2 *)
(********)
	      let stack_2' = stack_2#pop in
	      let t_2' = stack_2'#top in
(********)
	      let ch_type_2 = stack_level_to_ch_type t_2' in
	      let stack_var_2 = make_stack_variable stack_2'#height pc ch_type_2 in	    
	      let stack_3 = stack_2'#pop in
	      let t_3 = stack_3#top in
	      let ch_type_3 = stack_level_to_ch_type t_3 in
	      let stack_var_3 = make_stack_variable stack_3#height pc ch_type_3 in	    
	      set_destination pc [stack_var_1; stack_var_2; stack_var_3]  ;
	      let inv_stack = stack_3#pop in
	      let stack' = inv_stack#pushx [change_stack_level_source t_1' pc; TOP; t_3; t_2'; t_1'; TOP] in
(*******
	      let ch_type_2 = stack_level_to_ch_type t_2 in
	      let stack_var_2 = make_stack_variable stack_2#height pc ch_type_2 in	    
	      let stack_3 = stack_2#pop in
	      let t_3 = stack_3#top in
	      let ch_type_3 = stack_level_to_ch_type t_3 in
	      let stack_var_3 = make_stack_variable stack_3#height pc ch_type_3 in	    
	      let inv_stack = stack_3#pop in
	      let stack' = inv_stack#pushx [change_stack_level_source t_1' pc; TOP; t_3; t_2; t_1'; TOP] in
********)
	      let _ = set_stack pc' stack' in
	      let stack_var_1' = make_stack_variable (stack'#height - 1) pc' ch_type_1 in
	      let stack_var_2' = make_stack_variable (stack'#height - 2) pc' ch_type_2 in
	      let stack_var_3' = make_stack_variable (stack'#height - 3) pc' ch_type_3 in
	      let stack_var_4' = make_stack_variable (stack'#height - 5) pc' ch_type_1 in
	      let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	      let op_args = [ ("dst1", stack_var_1', READ) ;
			      ("src1", stack_var_1 , READ) ;
			      ("dst2", stack_var_2', READ) ;
			      ("src2", stack_var_2 , READ) ;
			      ("dst3", stack_var_3', READ) ;
			      ("src3", stack_var_3 , READ) ;
			      ("dst4", stack_var_4', READ) ;
			      ("src4", stack_var_1 , READ) ] in
	      let op = makeBytecodeOperation pc op_args in
	      [var_assign stack_var_1' stack_var_1 ch_type_1;
	       var_assign stack_var_2' stack_var_2 ch_type_2;
	       var_assign stack_var_3' stack_var_3 ch_type_3;
	       var_assign stack_var_4' stack_var_1 ch_type_1;
	       op
	      ] @ (inv_stack#copy pc pc')	      	      
	  else (* Forms 1 & 3 *)
	    let ch_type_1 = stack_level_to_ch_type t_1 in
	    let stack_var_1 = make_stack_variable stack_1#height pc ch_type_1 in	    
	    let stack_2 = stack_1#pop in
	    let t_2 = stack_2#top in
	    let ch_type_2 = stack_level_to_ch_type t_2 in
	    let stack_var_2 = make_stack_variable stack_2#height pc ch_type_2 in
	    let stack_3 = stack_2#pop in
	    let t_3 = stack_3#top in
	    if t_3 = TOP then (* Form 3 *)
	      let stack_3' = stack_3#pop in
	      let t_3' = stack_3'#top in
	      let ch_type_3 = stack_level_to_ch_type t_3' in
	      let stack_var_3 = make_stack_variable stack_3'#height pc ch_type_3 in
	      set_destination pc [stack_var_1; stack_var_2; stack_var_3]  ;
	      let inv_stack = stack_3'#pop in
	      let stack' = inv_stack#pushx [change_stack_level_source t_2 pc; change_stack_level_source t_1 pc; t_3'; TOP; t_2; t_1] in
	      let _ = set_stack pc' stack' in
	      let stack_var_1' = make_stack_variable stack'#height pc' ch_type_1 in
	      let stack_var_2' = make_stack_variable (stack'#height - 1) pc' ch_type_2 in
	      let stack_var_3' = make_stack_variable (stack'#height - 3) pc' ch_type_3 in
	      let stack_var_4' = make_stack_variable (stack'#height - 4) pc' ch_type_1 in
	      let stack_var_5' = make_stack_variable (stack'#height - 5) pc' ch_type_2 in
	      let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	      let op_args = [ ("dst1", stack_var_1', READ) ;
			      ("src1", stack_var_1 , READ) ;
			      ("dst2", stack_var_2', READ) ;
			      ("src2", stack_var_2 , READ) ;
			      ("dst3", stack_var_3', READ) ;
			      ("src3", stack_var_3 , READ) ;
			      ("dst4", stack_var_4', READ) ;
			      ("src4", stack_var_1 , READ) ;
			      ("dst5", stack_var_5', READ) ;
			      ("src5", stack_var_2 , READ) ] in
	      let op = makeBytecodeOperation pc op_args in
	      [var_assign stack_var_1' stack_var_1 ch_type_1;
	       var_assign stack_var_2' stack_var_2 ch_type_2;
	       var_assign stack_var_3' stack_var_3 ch_type_3;
	       var_assign stack_var_4' stack_var_1 ch_type_1;
	       var_assign stack_var_5' stack_var_2 ch_type_2;
	       op
	      ] @ (inv_stack#copy pc pc')	      
	    else (* Form 1 *)
	      let ch_type_3 = stack_level_to_ch_type t_3 in
	      let stack_var_3 = make_stack_variable stack_3#height pc ch_type_3 in	    
	      let stack_4 = stack_3#pop in
	      let t_4 = stack_4#top in
	      let ch_type_4 = stack_level_to_ch_type t_4 in
	      let stack_var_4 = make_stack_variable stack_4#height pc ch_type_4 in
	      set_destination pc [stack_var_1; stack_var_2; stack_var_3; stack_var_4]  ;
	      let inv_stack = stack_4#pop in
	      let stack' = inv_stack#pushx [change_stack_level_source t_2 pc; change_stack_level_source t_1 pc; t_4; t_3; t_2; t_1] in
	      let _ = set_stack pc' stack' in
	      let stack_var_1' = make_stack_variable stack'#height pc' ch_type_1 in
	      let stack_var_2' = make_stack_variable (stack'#height - 1) pc' ch_type_2 in
	      let stack_var_3' = make_stack_variable (stack'#height - 2) pc' ch_type_3 in
	      let stack_var_4' = make_stack_variable (stack'#height - 3) pc' ch_type_4 in
	      let stack_var_5' = make_stack_variable (stack'#height - 4) pc' ch_type_1 in
	      let stack_var_6' = make_stack_variable (stack'#height - 5) pc' ch_type_2 in
	      let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	      let op_args = [ ("dst1", stack_var_1', READ) ;
			      ("src1", stack_var_1 , READ) ;
			      ("dst2", stack_var_2', READ) ;
			      ("src2", stack_var_2 , READ) ;
			      ("dst3", stack_var_3', READ) ;
			      ("src3", stack_var_3 , READ) ;
			      ("dst4", stack_var_4', READ) ;
			      ("src4", stack_var_4 , READ) ;
			      ("dst5", stack_var_5', READ) ;
			      ("src5", stack_var_1 , READ) ;
			      ("dst6", stack_var_6', READ) ;
			      ("src6", stack_var_2 , READ) ] in
	      let op = makeBytecodeOperation pc op_args in
	      [var_assign stack_var_1' stack_var_1 ch_type_1;
	       var_assign stack_var_2' stack_var_2 ch_type_2;
	       var_assign stack_var_3' stack_var_3 ch_type_3;
	       var_assign stack_var_4' stack_var_4 ch_type_4;
	       var_assign stack_var_5' stack_var_1 ch_type_1;
	       var_assign stack_var_6' stack_var_2 ch_type_2;
	       op
	      ] @ (inv_stack#copy pc pc')
	| OpSwap ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let t_1 = stack#top in
	  let ch_type_1 = stack_level_to_ch_type t_1 in
	  let stack_2 = stack#pop in
	  let t_2 = stack_2#top in
	  let ch_type_2 = stack_level_to_ch_type t_2 in
	  let stack_var_1 = make_stack_variable stack#height pc ch_type_1 in
	  let stack_var_2' = make_stack_variable (stack#height - 1) pc' ch_type_1 in
	  let stack_var_2 = make_stack_variable (stack#height - 1) pc ch_type_2 in
	  let stack_var_1' = make_stack_variable stack#height pc' ch_type_2 in
	  let inv_stack = stack_2#pop in
	  let stack' = inv_stack#pushx [t_1 ; t_2] in
	  let _ = set_stack pc' stack' in
	  let _ = !destination_info#add_copy stack_var_1' stack_var_2 in
	  let _ = !destination_info#add_copy stack_var_2' stack_var_1 in

	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var_1', READ) ;
			  ("src1", stack_var_2 , READ) ;
			  ("dst2", stack_var_2', READ) ;
			  ("src2", stack_var_1 , READ) ] in
	  let op = makeBytecodeOperation pc op_args in 
	  [var_assign stack_var_1' stack_var_2 ch_type_2;
	   var_assign stack_var_2' stack_var_1 ch_type_1;
	   op ] @ (inv_stack#copy pc pc')
	  
	(* Constant loading *)
	| OpAConstNull ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#push (A [pc]) in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable stack'#height pc' SYM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [("ref", stack_var, WRITE)] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (stack#copy pc pc')
	| OpIntConst n ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#push (I ([Int],[pc])) in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable stack'#height pc' NUM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (ASSIGN_NUM (stack_var, NUM (mkNumericalFromInt32 n))) :: op :: (stack#copy pc pc')
	| OpLongConst n ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#pushx [I ([Long],[pc]); TOP] in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable (stack'#height - 1) pc' NUM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (ASSIGN_NUM (stack_var, NUM (mkNumericalFromInt64 n))) :: op :: (stack#copy pc pc')
	| OpFloatConst _
	| OpDoubleConst _ ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#pushx (match opcode with 
	      OpFloatConst _ -> [I ([Float],[pc])] | _ -> [I ([Double],[pc]); TOP]) in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable (stack#height + 1) pc' NUM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var, WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (stack#copy pc pc')
	| OpByteConst n
	| OpShortConst n ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#push (match opcode with 
	      OpByteConst _ -> I ([Byte],[pc]) | _ -> I ([Short],[pc])) in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable stack'#height pc' NUM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (ASSIGN_NUM (stack_var, NUM (mkNumerical n))) :: op :: (stack#copy pc pc')	  
	| OpStringConst s ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#push (A [pc]) in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable stack'#height pc' SYM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("ref", stack_var, WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (stack#copy pc pc') 
	| OpClassConst o ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#push (A [pc]) in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable stack'#height pc' SYM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [("ref", stack_var, WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (stack#copy pc pc')	  

	(* Arithmetic *)
	| OpAdd t
	| OpSub t
	| OpMult t
	| OpDiv t
	| OpRem t ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let size = size_of_java_basic_type t in
	  let inv_stack = stack#popx (2 * size) in
	  let stack' = inv_stack#pushx (java_basic_type_to_stack t pc) in
	  let _ = set_stack pc' stack' in
	  let stack_var' = make_stack_variable (stack'#height - size + 1) pc' NUM_VAR_TYPE in
	  let operation (v1, v2) =
	    match opcode with
	      | OpAdd _ -> PLUS (v1, v2)
	      | OpSub _ -> MINUS (v1, v2)
	      | OpMult _ -> MULT (v1, v2)
	      | OpDiv _ -> DIV (v1, v2)
	      | _ -> raise (JCH_failure (STR "Unreachable"))
	  in
	  let stack_var_1 = 
	    make_stack_variable (stack#height - 2 * size + 1) pc NUM_VAR_TYPE in
	  let stack_var_2 = 
	    make_stack_variable (stack#height - size + 1) pc NUM_VAR_TYPE in
	  let _ = set_destination pc [stack_var_1; stack_var_2] in
	  let (c,op_args) = 
	    if (is_float_type t) || (match opcode with OpRem _ -> true | _ -> false) then
	      (SKIP, [ ("throw", !exception_var, WRITE) ; ("dst1", stack_var', WRITE) ;
		       ("src1_1", stack_var_1, READ) ; ("src1_2", stack_var_2, READ) ])
	    else
	      (ASSIGN_NUM (stack_var', operation (stack_var_1, stack_var_2)),
	       [ ("throw", !exception_var, WRITE) ; ("dst1", stack_var', READ) ;
		 ("src1_1", stack_var_1, READ) ; ("src1_2", stack_var_2, READ) ])
	  in
	  let op_args_e = List.filter (fun (name,_,_) -> not (name = "dst1")) op_args in
	  let op = makeBytecodeOperation pc op_args in
	  begin
	    match opcode with
	      OpDiv _ | OpRem _ ->
		begin
		  add_exn_to_cfg pc pc' op_args_e (c :: op :: (inv_stack#copy pc pc')) ;
		  []
		end
	    | _ ->
	      begin
		(!graph)#add_edge (pc_label pc) (pc_label pc') ;
		c :: op :: (inv_stack#copy pc pc')
	      end
	  end
	| OpNeg t ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let size = size_of_java_basic_type t in
	  let inv_stack = stack#popx size in
	  let _ = set_stack pc' stack in
	  let stack_var' = make_stack_variable (stack#height - size + 1) pc' NUM_VAR_TYPE in
	  let stack_var = make_stack_variable (stack#height - size + 1) pc NUM_VAR_TYPE in
	  let _ = set_destination pc [stack_var] in
	  let (c,op_args) = 
	    if is_float_type t then
	      (SKIP, [ ("dst1", stack_var', WRITE)  ; ("src1", stack_var, READ) ])
	    else
	      let _ = (!scope)#startTransaction in
	      let tmp = (!scope)#requestNumTmpVariable in
	      let _ = (!scope)#endTransaction in
	      (TRANSACTION (opNegSymbol,
			    F.mkCode [ASSIGN_NUM (tmp, NUM numerical_zero);
				      ASSIGN_NUM (stack_var', MINUS (tmp, stack_var))],
			    None),
	       [ ("dst1", stack_var', READ) ; ("src1", stack_var, READ) ])
	  in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op = makeBytecodeOperation pc op_args in
	  c :: op :: (inv_stack#copy pc pc')
	    
	(* Logic *)
	(* XXX Bit-level operations are currently not modeled *)
	| OpIShl
	| OpLShl
	| OpIShr
	| OpLShr
	| OpIUShr
	| OpLUShr
	| OpIAnd
	| OpLAnd
	| OpIOr
	| OpLOr
	| OpIXor
	| OpLXor ->
	  let (operands_size, operand2_size, size, tgt_levels) = match opcode with
	    | OpIShl | OpIShr | OpIUShr | OpIAnd | OpIOr | OpIXor -> 
	      (2, 1, 1, [I ([Int],[pc])])
	    | OpLShl | OpLShr | OpLUShr -> (3, 1, 2, [I ([Long],[pc]); TOP])
	    | OpLAnd | OpLOr  | OpLXor  -> (4, 2, 2, [I ([Long],[pc]); TOP])
	    | _ -> raise (JCH_failure (STR "Internal error in translate_opcode"))
	  in
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#popx operands_size in
	  let stack' = inv_stack#pushx tgt_levels in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable (stack'#height - size + 1) pc' NUM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let stack_var_1 = 
	    make_stack_variable (stack#height - operands_size + 1) pc NUM_VAR_TYPE in
	  let stack_var_2 = 
	    make_stack_variable (stack#height - operand2_size + 1) pc NUM_VAR_TYPE in
	  let _ = set_destination pc [stack_var_1; stack_var_2] in
	  let op_args = 
	    [ ("dst1", stack_var, WRITE) ; 
	      ("src1_1", stack_var_1, READ) ; ("src1_2", stack_var_2, READ)] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: inv_stack#copy pc pc'
	    
	(* Conversion *)
	(* XXX Arithmetic overflows/underflows and wrap-arounds are currently not modeled *)
	| OpI2L -> 
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#popx 1 in
	  let stack' = inv_stack#pushx [I ([Long],[pc]); TOP] in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable stack#height pc NUM_VAR_TYPE in
	  let stack_var' = make_stack_variable (stack'#height - 1) pc' NUM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let _ = set_destination pc [stack_var] in
	  let op_args = [ ("dst1", stack_var', WRITE) ; ("src1", stack_var , READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (inv_stack#copy pc pc') 
(*
	  let op_args = [ ("dst1", stack_var', READ) ; ("src1", stack_var , READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (var_assign stack_var' stack_var NUM_VAR_TYPE) :: op :: (inv_stack#copy pc pc') 
*)
	| OpL2I
	| OpI2B
	| OpI2C
	| OpI2S ->
	  let src_size = match opcode with
	    | OpL2I -> 2
	    | _ -> 1
	  in
	  let tgtType = match opcode with 
	      OpL2I -> Int | OpI2B -> Byte | OpI2C -> Char | OpI2S -> Short
	    | _ -> raise (JCH_failure (STR "Internal error translate_opcode")) in
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#popx src_size in
	  let stack' = inv_stack#pushx [I ([tgtType],[pc])] in
	  let _ = set_stack pc' stack' in
	  let stack_var = make_stack_variable (stack#height - src_size + 1) pc NUM_VAR_TYPE in
	  let stack_var' = make_stack_variable stack'#height pc' NUM_VAR_TYPE in
	  let _ = set_destination pc [stack_var] in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var', WRITE) ; ("src1", stack_var , READ) ] in
	  let op = makeBytecodeOperation pc op_args in
(*	  (var_assign stack_var' stack_var NUM_VAR_TYPE) :: op :: (inv_stack#copy pc pc')  *)
	  op :: (inv_stack#copy pc pc')  

	(* XXX Floating-point operations are currently not modeled *)
	| OpI2F
	| OpI2D
	| OpL2F
	| OpL2D
	| OpF2I
	| OpF2L
	| OpF2D
	| OpD2I
	| OpD2L
	| OpD2F ->
	  let tgtType = match opcode with
	    | OpI2F | OpL2F | OpD2F -> Float
	    | OpI2D | OpL2D | OpF2D -> Double
	    | OpF2I | OpD2I -> Int
	    | OpF2L | OpD2L -> Long 
	    | _ -> raise (JCH_failure (STR "Internal error in translate_opcode")) in
	  let src_size = match opcode with
	    | OpL2F | OpL2D | OpD2I | OpD2L | OpD2F -> 2
	    | _ -> 1
	  in
	  let (tgt_size, tgt_levels) = match opcode with
	    | OpI2D | OpL2D | OpF2L | OpF2D | OpD2L -> (2, [I ([tgtType],[pc]) ; TOP])
	    | _ -> (1, [I ([tgtType],[pc])])
	  in
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#popx src_size in
	  let stack' = inv_stack#pushx tgt_levels in
	  let _ = set_stack pc' stack' in 
	  let stack_var = make_stack_variable (stack#height - src_size + 1) pc NUM_VAR_TYPE in
	  let stack_var' = make_stack_variable (stack'#height - tgt_size + 1) pc' NUM_VAR_TYPE in
	  let _ = set_destination pc [stack_var] in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var', WRITE) ; ("src1", stack_var, READ)] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (inv_stack#copy pc pc')

	(* Comparison *)
	| OpCmpL ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#popx 4 in
	  let stack' = inv_stack#push (I ([Int],[pc])) in
	  let _ = set_stack pc' stack' in
	  let stack_var_1 = make_stack_variable (inv_stack#height + 1) pc NUM_VAR_TYPE in
	  let stack_var_2 = make_stack_variable (inv_stack#height + 3) pc NUM_VAR_TYPE in
	  let stack_var' = make_stack_variable stack'#height pc' NUM_VAR_TYPE in
	  let _ = set_destination pc [stack_var_1; stack_var_2] in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var', READ) ;
			  ("src1", stack_var_1, READ) ;
			  ("src2", stack_var_2, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (TRANSACTION (new symbol_t ~atts:["OpCmpL"] (pc_label pc),
			F.mkCode [
			  BRANCH [
			    F.mkCode [
			      ASSERT (GT (stack_var_1, stack_var_2));			      
			      ASSIGN_NUM (stack_var', NUM numerical_one)
			    ];
			    F.mkCode [
			      ASSERT (EQ (stack_var_1, stack_var_2));			      
			      ASSIGN_NUM (stack_var', NUM numerical_zero)
			    ];
			    F.mkCode [
			      ASSERT (LT (stack_var_1, stack_var_2));			      
			      ASSIGN_NUM (stack_var', NUM numerical_one#neg)
			    ]
			  ]
			],
			None)
	  ) :: op:: (inv_stack#copy pc pc')
	| OpCmpFL
	| OpCmpFG
	| OpCmpDL
	| OpCmpDG ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let size = match opcode with
	    | OpCmpFL | OpCmpFG -> 1
	    | _ -> 2
	  in
	  let inv_stack = stack#popx (2 * size) in
	  let stack_var_1 = make_stack_variable (inv_stack#height + 1) pc NUM_VAR_TYPE in
	  let stack_var_2 = make_stack_variable (inv_stack#height + size + 1) pc NUM_VAR_TYPE in
	  let _ = set_destination pc [stack_var_1; stack_var_2] in
	  let stack' = inv_stack#push (I ([Int],[pc])) in
	  let _ = set_stack pc' stack' in 
	  let stack_var = make_stack_variable stack'#height pc' NUM_VAR_TYPE in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op_args = [ ("dst1", stack_var, WRITE) ; ("src1", stack_var_1, READ) ; 
			  ("src2", stack_var_2, READ)] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (inv_stack#copy pc pc')
	  
	(* Conditional jump *)
	| OpIfEq offset
	| OpIfNe offset
	| OpIfLt offset
	| OpIfGe offset
	| OpIfGt offset
	| OpIfLe offset 
	| OpIfCmpEq offset
	| OpIfCmpNe offset
	| OpIfCmpLt offset
	| OpIfCmpGe offset
	| OpIfCmpGt offset
	| OpIfCmpLe offset ->
	  let is_binop =
	    match opcode with
	      | OpIfEq _ | OpIfNe _ | OpIfLt _ | OpIfGe _ | OpIfGt _ | OpIfLe _ -> false
	      | _ -> true
	  in
	  let stack = get_stack pc in
	  let stack' = if is_binop then
	      stack#popx 2
	    else
	      stack#pop
	  in
	  let pc_then = pc + offset in
 	  let _ = if pc_then >= code#length then
	      begin
		ch_error_log#add "inconsistent bytecode" 
		  (LBLOCK [ STR "at pc = " ; INT pc ; STR " pc-then is " ; INT pc_then]) ;
		raise (JCH_failure (LBLOCK [ STR "Inconsistent bytecode; pc_then = " ; INT pc_then ]))
	      end
	    else
	      Queue.add pc_then opcodes_to_translate in	  
	  let pc_else = next_pc () in
	  let _ = set_stack pc_then stack' in
	  let _ = set_stack pc_else stack' in
	  let condition v1 v2 =
	    match opcode with 
	      | OpIfEq _ | OpIfCmpEq _ -> EQ (v1, v2)
	      | OpIfNe _ | OpIfCmpNe _ -> NEQ (v1, v2)
	      | OpIfLt _ | OpIfCmpLt _ -> LT (v1, v2)
	      | OpIfGe _ | OpIfCmpGe _ -> GEQ (v1, v2)
	      | OpIfGt _ | OpIfCmpGt _ -> GT (v1, v2)
	      | OpIfLe _ | OpIfCmpLe _ -> LEQ (v1, v2)
	      | _ -> raise (JCH_failure (STR "Unreachable"))
	  in
	  let (test_then, test_else,op_args) =
	    if is_binop then
	      let stack_var_1 = make_stack_variable (stack#height - 1) pc NUM_VAR_TYPE in
	      let stack_var_2 = make_stack_variable stack#height pc NUM_VAR_TYPE in
	      let _ = set_destination pc [stack_var_1; stack_var_2] in
	      let op_args = [ ("src1", stack_var_1, READ) ; ("src2", stack_var_2, READ) ] in
	      (ASSERT (condition stack_var_1 stack_var_2),
	       ASSERT (negate_bool_exp (condition stack_var_1 stack_var_2)), op_args
	      )
	    else
	      let stack_var = make_stack_variable stack#height pc NUM_VAR_TYPE in	 
	      let _ = set_destination pc [stack_var] in
	      let _ = (!scope)#startTransaction in
	      let tmp = (!scope)#requestNumTmpVariable in
	      let _ = (!scope)#endTransaction in
	      let op_args = [ ("src1", stack_var, READ) ] in
	      (TRANSACTION  (then_symbol pc,
			    F.mkCode [ASSIGN_NUM (tmp, NUM numerical_zero);
				      ASSERT (condition stack_var tmp)],
			    None),
	       TRANSACTION (else_symbol pc,
			    F.mkCode [ASSIGN_NUM (tmp, NUM numerical_zero);
				      ASSERT (negate_bool_exp (condition stack_var tmp))],
			    None), 
	       op_args
	      )
	  in
	  let op = makeBytecodeOperation pc op_args in
	  let inverted_op = makeBytecodeOperation pc ~inverted:true op_args in
	  let _ = 
	    begin
	      (!graph)#add_node (pc_label_then pc) (op :: test_then :: (List.rev (stack'#copy pc pc_then)));
	      (!graph)#add_node (pc_label_else pc) 
		(inverted_op :: test_else :: (List.rev (stack'#copy pc pc_else)));
	      (!graph)#add_edge (pc_label pc) (pc_label_then pc);
	      (!graph)#add_edge (pc_label pc) (pc_label_else pc);
	      (!graph)#add_edge (pc_label_then pc) (pc_label pc_then);
	      (!graph)#add_edge (pc_label_else pc) (pc_label pc_else)
	    end
	  in
	  [SKIP]
	| OpIfNull offset
	| OpIfNonNull offset 
	| OpIfCmpAEq offset
	| OpIfCmpANe offset ->
	  let is_binop =
	    match opcode with
	      | OpIfNull _ | OpIfNonNull _ -> false
	      | _ -> true
	  in
	  let stack = get_stack pc in
	  let stack' = if is_binop then
	      stack#popx 2
	    else
	      stack#pop
	  in
	  let pc_then = pc + offset in
 	  let _ = if pc_then >= code#length then
	      begin
		ch_error_log#add "inconsistent bytecode" 
		  (LBLOCK [ STR "at pc = " ; INT pc ; STR " pc-then is " ; INT pc_then]) ;
		raise (JCH_failure (LBLOCK [ STR "Inconsistent bytecode; pc_then = " ; INT pc_then ]))
	      end
	    else
	      Queue.add pc_then opcodes_to_translate in	  
	  let pc_else = next_pc () in
	  let _ = set_stack pc_then stack' in
	  let _ = set_stack pc_else stack' in
	  let (test_then, test_else) =
	    if is_binop then
	      let stack_var_1 = make_stack_variable (stack#height - 1) pc SYM_VAR_TYPE in
	      let stack_var_2 = make_stack_variable stack#height pc SYM_VAR_TYPE in
	      let _ = set_destination pc [stack_var_1; stack_var_2] in
	      let op_args = [ ("src1", stack_var_1, READ) ; ("src2", stack_var_2, READ) ] in
	      let op = makeBytecodeOperation pc op_args in
	      let inverted_op = makeBytecodeOperation pc ~inverted:true op_args in
	      (op, inverted_op)
	    else
	      let stack_var = make_stack_variable stack#height pc SYM_VAR_TYPE in
	      let _ = set_destination pc [stack_var] in
	      let op_args = [ ("src1", stack_var, READ) ] in
	      let op = makeBytecodeOperation pc op_args in
	      let inverted_op = makeBytecodeOperation pc ~inverted:true op_args in
	      (op,inverted_op)
	  in
	  let _ = 
	    begin
	      (!graph)#add_node (pc_label_then pc) (test_then :: (List.rev (stack'#copy pc pc_then)));
	      (!graph)#add_node (pc_label_else pc) (test_else :: (List.rev (stack'#copy pc pc_else)));
	      (!graph)#add_edge (pc_label pc) (pc_label_then pc);
	      (!graph)#add_edge (pc_label pc) (pc_label_else pc);
	      (!graph)#add_edge (pc_label_then pc) (pc_label pc_then);
	      (!graph)#add_edge (pc_label_else pc) (pc_label pc_else)
	    end
	  in
	  [SKIP]
	  

	(* Unconditional jump *)
	| OpGoto offset ->
	  let stack = get_stack pc in
	  let pc' = pc + offset in
	  (* cases have been encountered where pc + offset is greater than max-int and
	     apparently expected to wrap around (judging from javap output            *)
	  let pc' = if pc' > 2147483647 then pc' - 2147483648 else pc' in
 	  let _ = if pc' >= code#length then
	      begin
		ch_error_log#add "inconsistent bytecode" 
		  (LBLOCK [ STR "at pc = " ; INT pc ; STR " goto target is " ; INT pc']) ;
		raise (JCH_failure (LBLOCK [ STR "Inconsistent bytecode; pc' = " ; INT pc' ]))
	      end
	    else
	      Queue.add pc' opcodes_to_translate in
	  let _ = set_stack pc' stack in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op = makeBytecodeOperation pc [] in
	  op :: stack#copy pc pc'
	| OpJsr _ 
	| OpRet _ -> 
	  raise (JCH_failure (LBLOCK [STR "Subroutines not supported at pc="; INT pc]))
	| OpTableSwitch (default, low, high, table) ->
	  let stack = get_stack pc in
	  let stack' = stack#pop in
	  let index = make_stack_variable stack#height pc NUM_VAR_TYPE in
	  let _ = set_destination pc [index] in
	  let _ = (!scope)#startTransaction in
	  let tmp = (!scope)#requestNumTmpVariable in
	  let _ = (!scope)#endTransaction in
	  let base = mkNumericalFromInt32 low in
	  let branch_to pc' code_label cond cst label =
 	    (if pc' >= code#length then
		begin
		  ch_error_log#add "inconsistent bytecode" 
		    (LBLOCK [ STR "at pc = " ; INT pc ; 
			      STR " table switch branch target is " ; INT pc']) ;
		  raise (JCH_failure (LBLOCK [ STR "Inconsistent bytecode;  pc' = " ; 
					       INT pc' ]))
		end
	     else
		Queue.add pc' opcodes_to_translate) ; 
	    set_stack pc' stack';
	    (!graph)#add_node label [
	      TRANSACTION (new symbol_t ~atts:[cst#toString] code_label,
			   F.mkCode ((ASSIGN_NUM (tmp, NUM (base#add cst)))
				     :: (ASSERT (cond (index, tmp)))
				     :: (stack'#copy pc pc')),
			   None
	      )
	    ];
	    (!graph)#add_edge (pc_label pc) label;
	    (!graph)#add_edge label (pc_label pc')
	  in
	  let _ =
	    begin
	      Array.iteri 
		(fun i tgt_offset -> 
		  let cst = mkNumerical i in
		  branch_to (pc + tgt_offset) "case" 
		    (fun (x, y) -> EQ (x, y)) cst (pc_label_case pc cst)) table;
	      branch_to (pc + default) "default-low" 
		(fun (x, y) -> LT (x, y)) base (pc_label_default_case_low pc);
	      branch_to (pc + default) "default-high" 
		(fun (x, y) -> GT (x, y)) (mkNumericalFromInt32 high) (pc_label_default_case_high pc)
	    end
	  in
	  [makeBytecodeOperation pc []]
	| OpLookupSwitch (default, match_pairs) ->
	  let stack = get_stack pc in
	  let stack' = stack#pop in
	  let index = make_stack_variable stack#height pc NUM_VAR_TYPE in
	  let _ = set_destination pc [index] in
	  let _ = (!scope)#startTransaction in
	  let tmp = (!scope)#requestNumTmpVariable in
	  let _ = (!scope)#endTransaction in
	  let branch_to pc' code_label cond cst label =
 	    (if pc' >= code#length then
		begin
		  ch_error_log#add "inconsistent bytecode" 
		    (LBLOCK [ STR "at pc = " ; INT pc ; 
			      STR " lookup switch branch target is " ; INT pc']) ;
		  raise (JCH_failure (LBLOCK [ STR "Inconsistent bytecode; pc' = " ; 
					       INT pc' ]))
		end
	     else
		Queue.add pc' opcodes_to_translate) ; 
	    set_stack pc' stack';
	    (!graph)#add_node label [
	      TRANSACTION (new symbol_t ~atts:[cst#toString] code_label,
			   F.mkCode ((ASSIGN_NUM (tmp, NUM cst))
				     :: (ASSERT (cond (index, tmp)))
				     :: (stack'#copy pc pc')),
			   None
	      )
	    ];
	    (!graph)#add_edge (pc_label pc) label;
	    (!graph)#add_edge label (pc_label pc')
	  in
	  let _ = List.iter (fun (i, tgt_offset) -> 
	    let cst = mkNumericalFromInt32 i in
	    branch_to (pc + tgt_offset) "case" (fun (x, y) -> EQ (x, y)) cst (pc_label_case pc cst)) match_pairs
	  in
	  let default_code cst =
	    TRANSACTION (new symbol_t ~atts:[cst#toString] "default",
			 F.mkCode [ASSIGN_NUM (tmp, NUM cst);
				   ASSERT (NEQ (index, tmp))
				  ],
			 None
	    )
	  in
	  let pc_default = pc + default in
	  let _ =
	    begin
 	      (if pc_default >= code#length then
		  begin
		    ch_error_log#add "inconsistent bytecode" 
		      (LBLOCK [ STR "at pc = " ; INT pc ; 
				STR " lookup default target is " ; INT pc_default]) ;
		    raise (JCH_failure (LBLOCK [ STR "Inconsistent bytecode; pc' = " ;
						 INT pc_default ]))
		  end
			else
	      Queue.add pc_default opcodes_to_translate);
	      set_stack pc_default stack';
	      (!graph)#add_node (pc_label_default_case pc) 
		      (List.rev_append
                         (List.map (fun (cst, _) ->
                              default_code (mkNumericalFromInt32 cst)) match_pairs)
                         (List.rev (stack'#copy pc pc_default)));
	      (!graph)#add_edge (pc_label pc) (pc_label_default_case pc);
	      (!graph)#add_edge (pc_label_default_case pc) (pc_label pc_default)
	    end
	  in
	  [makeBytecodeOperation pc []]
	  	    
	(* Heap and static field manipulations *)
	| OpNew class_name ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#push (A [pc])in
	  let _ = set_stack pc' stack' in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let returnvar = make_stack_variable stack'#height pc' SYM_VAR_TYPE in
	  let op_args = [ ("ref", returnvar, WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (stack#copy pc pc')
	| OpNewArray t ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#pop in
	  let stack' = inv_stack#push (A [pc]) in
	  let _ = set_stack pc' stack' in
	  let arrayvar = make_stack_variable stack'#height pc' SYM_VAR_TYPE in
	  let lengthvar = make_stack_variable stack#height pc NUM_VAR_TYPE in
	  let _ = set_destination pc [lengthvar] in
	  let op_args = [ ("throw", !exception_var, WRITE) ;
			  ("length", lengthvar, READ) ; ("ref", arrayvar, WRITE) ] in
	  let op    = makeBytecodeOperation pc op_args in
	  begin
	    add_exn_to_cfg pc pc' op_args (op :: (inv_stack#copy pc pc')) ;
	    [ ]
	  end
	| OpAMultiNewArray (t, n) ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#popx n in
	  let stack' = inv_stack#push (A [pc]) in
	  let _ = set_stack pc' stack' in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let rec dims d h l =
	    if d = 0 then
	      l
	    else
	      begin
		let dimvar = make_stack_variable (stack#height - h) pc NUM_VAR_TYPE in
		let _ = set_destination pc [dimvar] in
		dims (d - 1) (h + 1) (("dim" ^ (string_of_int d), dimvar, READ) :: l)
	      end
	  in
	  let arrayvar = make_stack_variable stack'#height pc' SYM_VAR_TYPE in
	  let op_args = ("ref", arrayvar, WRITE) :: (dims n 0 []) in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (inv_stack#copy pc pc')
	| OpCheckCast t ->
	  let stack = get_stack pc in
	  let inv_stack = stack#pop in
	  let pc' = next_pc () in
	  let _ = set_stack pc' stack in
	  let stack_var  = make_stack_variable stack#height pc SYM_VAR_TYPE in
	  let stack_var' = make_stack_variable stack#height pc' SYM_VAR_TYPE in
	  let _ = set_destination pc [stack_var] in
	  let op_args = [ ("throw", !exception_var, WRITE) ; ("src1", stack_var, READ) ;
                          ("dst1", stack_var',WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  begin
	    add_exn_to_cfg pc pc' op_args (op :: (inv_stack#copy pc pc')) ;
	    [ ] 
	  end
	| OpInstanceOf t ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#pop in
	  let stack' = inv_stack#push (I ([Int],[pc])) in
	  let _ = set_stack pc' stack' in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let refvar = make_stack_variable stack#height pc SYM_VAR_TYPE in
	  let valvar = make_stack_variable stack'#height pc' NUM_VAR_TYPE in
	  let _ = set_destination pc [refvar] in
	  let op_args = [ ("ref", refvar, READ) ; ("val", valvar, WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (inv_stack#copy pc pc')	  
	| OpGetStatic (class_name, field_signature) ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let t = field_signature#descriptor in
	  let stack' = stack#pushx (value_type_to_stack t pc) in
	  let _ = set_stack pc' stack' in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let returnvar = make_stack_variable (stack#height + 1) pc' (translate_value_type t) in
	  let op_args = [ ("val", returnvar, WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  op :: (stack#copy pc pc')
	| OpGetField (class_name, field_signature) ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let t = field_signature#descriptor in
	  let inv_stack = stack#pop in
	  let stack' = inv_stack#pushx (value_type_to_stack t pc) in
	  let _ = set_stack pc' stack' in
	  let refvar = make_stack_variable stack#height pc SYM_VAR_TYPE in
	  let valvar = make_stack_variable (inv_stack#height + 1) pc' (translate_value_type t) in
	  let _ = set_destination pc [refvar] in
	  let op_args = [ ("throw", !exception_var, WRITE) ;
			  ("ref", refvar, READ) ; ("val", valvar, WRITE) ] in
	  let op    = makeBytecodeOperation pc op_args in
	  begin
	    add_exn_to_cfg pc pc' op_args (op :: (inv_stack#copy pc pc')) ;
	    [ ] 
	  end
	| OpPutStatic (class_name, field_signature) ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let t = field_signature#descriptor in
	  let stack' = stack#popx (size_of_value_type t) in
	  let _ = set_stack pc' stack' in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let valvar = make_stack_variable (stack'#height + 1) pc (translate_value_type t) in
	  let _ = set_destination pc [valvar] in
	  let op_args = [ ("val", valvar, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  (op :: (stack'#copy pc pc'))
	| OpPutField (class_name, field_signature) ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let t = field_signature#descriptor in
	  let stack' = (stack#popx (size_of_value_type t))#pop in
	  let _ = set_stack pc' stack' in
	  let refvar = make_stack_variable (stack'#height + 1) pc SYM_VAR_TYPE in
	  let valvar = make_stack_variable (stack'#height + 2) pc (translate_value_type t) in
	  let _ = set_destination pc [refvar] in
	  let _ = set_destination pc [valvar] in
	  let op_args = [ ("throw",!exception_var, WRITE)  ; 
			  ("ref", refvar, READ) ; ("val", valvar, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  begin
	    add_exn_to_cfg pc pc' op_args (op :: (stack'#copy pc pc')) ;
	    [ ] 
	  end
	| OpArrayLength ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#pop in
	  let stack' = inv_stack#push (I ([Int],[pc])) in
	  let _ = set_stack pc' stack' in
	  let refvar = make_stack_variable stack#height pc SYM_VAR_TYPE in
	  let valvar = make_stack_variable stack'#height pc' NUM_VAR_TYPE in
	  let _ = set_destination pc [refvar] in
	  let op_args = [ ("throw",!exception_var,WRITE) ; ("ref", refvar, READ) ; ("val", valvar, WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  begin
	    add_exn_to_cfg pc pc' op_args (op :: (inv_stack#copy pc pc')) ;
	    [ ] 
	  end
	| OpArrayLoad t -> 
	  let ch_type = translate_java_basic_type t in
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let inv_stack = stack#popx 2 in
	  let stack' = inv_stack#pushx (java_basic_type_to_stack t pc) in
	  let _ = set_stack pc' stack' in
	  let array_ref = make_stack_variable (stack#height - 1) pc SYM_VAR_TYPE in
	  let index = make_stack_variable stack#height pc NUM_VAR_TYPE in
	  let element = make_stack_variable (inv_stack#height + 1) pc' ch_type in
	  let _ = set_destination pc [array_ref; index] in
	  let op_args = [ ("throw",!exception_var, WRITE) ;
			  ("array", array_ref, READ); ("index", index, READ) ; ("val", element, WRITE) ] in
	  let op = makeBytecodeOperation pc op_args in
	  begin
	    add_exn_to_cfg pc pc' op_args (op :: (inv_stack#copy pc pc')) ;
	    [ ] 
	  end
	| OpArrayStore t ->
	  let ch_type = translate_java_basic_type t in
	  let size = size_of_java_basic_type t in
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#popx (2 + size) in
	  let _ = set_stack pc' stack' in
	  let array_ref = make_stack_variable (stack'#height + 1) pc SYM_VAR_TYPE in
	  let index = make_stack_variable (stack'#height + 2) pc NUM_VAR_TYPE in
	  let element = make_stack_variable (stack'#height + 3) pc ch_type in
	  let _ = set_destination pc [array_ref; index; element] in
	  let op_args = [ ("throw",!exception_var,WRITE) ;
			  ("array", array_ref, READ); ("index", index, READ); ("val", element, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  begin
	    add_exn_to_cfg pc pc' op_args (op :: (stack'#copy pc pc')) ;
	    [  ] 
	  end
	(* Method invocation and return *)
	| OpInvokeStatic (_, signature) 
	| OpInvokeSpecial (_, signature) 
	| OpInvokeInterface (_, signature)
	| OpInvokeVirtual (_, signature)
        | OpInvokeDynamic (_,signature) ->
	   translate_invoke_operation opcode signature
	| OpReturn t ->
	  let stack = get_stack pc in
	  let _ = (!graph)#add_edge (pc_label pc) normal_exit in
	  if is_void t then
	    [ makeBytecodeOperation pc [] ]
	  else
	    let ch_type = translate_java_basic_type t in
	    let size = size_of_java_basic_type t in
	    let ret_var = make_variable "return" ch_type in
	    let stack_var = make_stack_variable (stack#height - size + 1) pc ch_type in
	    let op_args = [ ("dst1", ret_var, READ) ; ("src1", stack_var, READ) ] in
	    let _ = set_destination pc [stack_var] in
	    let op = makeBytecodeOperation pc op_args in
	    [var_assign ret_var stack_var ch_type; op]
	      
	(* Exceptions and threads *)
	| OpThrow ->
	  (* XXX We assume that any exception handler in scope may be executed or not.
	   * XXX This is an imprecise modeling that must be modified once the engine is 
	   * XXX upgraded to handle compound structures. *)
	  let stack = get_stack pc in
	  let handler_pcs = List.map handler_pc_label (get_exception_handlers pc) in
	  let _ = List.iter 
	    (fun pc' -> (!graph)#add_edge (pc_label pc) pc') (exceptional_exit :: handler_pcs) in
	  let stack_var = make_stack_variable stack#height pc SYM_VAR_TYPE in
	  set_destination pc [stack_var] ;
	  let op = makeBytecodeOperation pc  [] in
	  [var_assign (!exception_var) stack_var SYM_VAR_TYPE ; op ]
	| OpMonitorEnter ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#pop in
	  let refvar = make_stack_variable stack#height pc SYM_VAR_TYPE in
	  let op_args = [ ("throw",!exception_var,WRITE) ; ("ref", refvar, READ) ] in
	  let op    = makeBytecodeOperation pc op_args in
	  begin
	    set_stack pc' stack';
	    set_destination pc [refvar] ;
	    add_exn_to_cfg pc pc' op_args (op :: (stack'#copy pc pc')) ;
	    [ ]
	  end
	| OpMonitorExit ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let stack' = stack#pop in
	  let refvar = make_stack_variable stack#height pc SYM_VAR_TYPE in
	  let op_args = [ ("throw",!exception_var,WRITE) ; ("ref", refvar, READ) ] in
	  let op = makeBytecodeOperation pc op_args in
	  begin
	    set_stack pc' stack' ;
	    set_destination pc [refvar] ;
	    add_exn_to_cfg pc pc' op_args (op :: (stack'#copy pc pc')) ;
	    [  ]
	  end
	(* Other *)
	| OpNop ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let _ = set_stack pc' stack in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op = makeBytecodeOperation pc [] in
	  op :: (stack#copy pc pc')
	| OpBreakpoint ->
	  let stack = get_stack pc in
	  let pc' = next_pc () in
	  let _ = set_stack pc' stack in
	  let _ = (!graph)#add_edge (pc_label pc) (pc_label pc') in
	  let op = makeBytecodeOperation pc [] in
	  op :: (stack#copy pc pc')
	| OpInvalid -> 
	  raise (JCH_failure (STR "Inconsistent bytecode #2"))
	 
     in
	  let invariant_op =
	    let op_name = get_invariant_op_symbol pc in
	    OPERATION { op_name = op_name ; op_args = []} in
	  let cmds = invariant_op :: cmds in   
	  let c = CODE (code_label pc, F.mkCode cmds) in
	  (!graph)#add_node (pc_label pc) [c]
	    

let translate_bytecode 
    ?(exn_infos_fn=(fun _ -> [ defaultExnInfo ]))
    ?(initialization_cmd=SKIP)
    (java_method: method_int) : CHOnlineCodeSet.code_t =
  match java_method#get_implementation with
  | Native -> 
    begin
      F.mkCode [SKIP]
    end
  | Bytecode bc ->      
    let code = bc#get_code in
    let handler_stack = (new op_stack_t)#push (A [-1]) in
    let _ = 
      try
	begin
					(* Initializing opcode translation queue *)
	  Queue.clear opcodes_to_translate;
	  translated_opcodes := new IntCollections.set_t;
					(* Scanning exception handlers *)
	  exception_handler_table := bc#get_exception_table;
	  List.iter (fun h ->
	    begin
	      (!graph)#add_node (handler_pc_label h#handler)
		[var_assign (make_stack_variable handler_stack#height h#handler SYM_VAR_TYPE) 
		    (!exception_var) SYM_VAR_TYPE];
	      (!graph)#add_edge (handler_pc_label h#handler) (pc_label h#handler);
	      (if h#handler >= code#length then
		  begin
		    ch_error_log#add "inconsistent bytecode" 
		      (LBLOCK [ STR " handler pc is " ; INT h#handler]) ;
		    raise (JCH_failure (LBLOCK [ STR "Inconsistent bytecode; handler = " ; INT h#handler ]))
		  end
	       else
		  Queue.add h#handler opcodes_to_translate) ; 
	      (!stack_table)#set (pc_label h#handler) handler_stack
	    end
	  ) (!exception_handler_table);
					(* Initial opcode *)
	  (!stack_table)#set (pc_label 0) (new op_stack_t);
	  Queue.add 0 opcodes_to_translate;
					(* Translation loop *)
	  while not(Queue.is_empty opcodes_to_translate) do
	    let i = Queue.take opcodes_to_translate in
	    translate_opcode 
              ~exn_infos:(exn_infos_fn i)
	      ~java_method:java_method
	      ~normal_exit:normal_exit_node 
	      ~exceptional_exit:exceptional_exit_node 
	      ~pc:i 
	      ~code:code 
	      ~bytecode:bc;
	    (!translated_opcodes)#add i
	  done;
	  (!graph)#add_node exceptional_exit_node [exnExitOperation];
	  (!graph)#add_node initialization_node [initializationOperation ; initialization_cmd ];
	  (!graph)#add_node normal_exit_node [SKIP];
	  (!graph)#add_node method_exit_node [SKIP];
	  (!graph)#add_edge exceptional_exit_node method_exit_node;
	  (!graph)#add_edge normal_exit_node method_exit_node;
	  (!graph)#add_edge initialization_node (pc_label 0)
	end
      with JCH_failure p ->
	begin
	  ch_error_log#add "failure in translate_bytecode"
	    (LBLOCK [ STR "Failure in translate_bytecode"]) ;
	  raise (JCH_failure (LBLOCK [ STR "Failure in translate_bytecode: " ; p ]))
	end

    in
    let cfg = (!graph)#to_cfg initialization_node method_exit_node in
    F.mkCode [CFG (new symbol_t java_method#get_signature#name, cfg)]
				
let procname_symbol_store = H.create 53
let get_procname_symbol (cms:class_method_signature_int) =
  try
    H.find procname_symbol_store cms#index
  with
      Not_found ->
	let index = cms#index in
	let sym = new symbol_t ~seqnr:index "procname" in
	begin
	  H.add procname_symbol_store index sym ;
	  sym
	end
      
let translate_method
    ~(proc_filter: procedure_int -> bool)
    ~(simplify: bool)
    ~(transform: bool)
    ~(java_method: method_int)
    ~(code_set: system_int)
    ?(exn_infos_fn=(fun _ -> [ defaultExnInfo ]))
    ?(initialization_cmd=SKIP)
    ()
    =
  let _ = 
    begin
      variable_pool#removeList variable_pool#listOfKeys ;
      scope := F.mkScope ();
      exception_var := make_variable "exception" SYM_VAR_TYPE;
      graph := new bc_graph_t;
      stack_table := new stack_table_t ;
      destination_info := new destination_info_t ;
      set_current_method java_method#get_class_method_signature
    end
  in
  let descriptor = java_method#get_signature#descriptor in
  let (ret_param, ret_binding) = match descriptor#return_value with
    | None | Some (TBasic Void) -> ([], [])
    | Some t -> let ch_t = translate_value_type t in
		let s = return_symbol in
		([(s, ch_t, WRITE)], [(s, make_variable "return" ch_t)])
  in
  let (exception_param, exception_binding) =
    let s = throw_symbol in
    ([(s, SYM_VAR_TYPE, WRITE)], [(s, !exception_var)])
  in
  let (start_param, start_reg, this_param, this_binding) =
    if java_method#is_static then
      (0, 0, [], [])
    else
      let s = ch_formal_param 0 in
      (1, 1, [(s, SYM_VAR_TYPE, READ)], [(s, make_register_variable 0 SYM_VAR_TYPE)])
  in
  let translate_param n_p n_r t =
    let ch_t = translate_value_type t in
    let s = ch_formal_param n_p in
    ((s, ch_t, READ), (s, make_register_variable n_r ch_t))
  in
  let (_, _, params, bindings) = List.fold_left (fun (n_p, n_r, l_p, l_r) t ->
    let (p, r) = translate_param n_p n_r t in
    (n_p + 1, n_r + (size_of_value_type t), p :: l_p, r :: l_r))
    (start_param, start_reg, [], []) descriptor#arguments
  in
  let ch_signature = ret_param @ exception_param @ this_param @ (List.rev params) in
  let ch_bindings = this_binding @ ret_binding @ exception_binding @ (List.rev bindings) in
  let ch_name = get_procname_symbol java_method#get_class_method_signature in
  let body = translate_bytecode ~exn_infos_fn ~initialization_cmd java_method in 
  let proc = F.mkProcedure ch_name ~signature:ch_signature 
    ~bindings:ch_bindings ~scope:!scope ~body:body in
  let _ = if simplify then (!simplifier)#simplify_procedure proc else () in
  let _ = if transform then (!transformer)#transform_procedure proc else () in
  if proc_filter proc then
    code_set#addProcedure proc
  else
    ()

let get_method_stack_layout (code_set:system_int) (java_method:method_int) = 
  let _ = translate_method 
    ~proc_filter:(fun _ -> true)
    ~simplify:false
    ~transform:false
    ~java_method
    ~code_set
    () in
  let stack_layouts = !stack_table#get_all in 
  let destinations = get_all_destinations () in
  let (local_var_table, bytecode_size) = 
    match java_method#get_implementation with
    | Bytecode bc -> (bc#get_local_variable_table, bc#get_code#length)
    | _ -> (None, -1) in

  let stack_layouts = List.map (fun (strPc,layout) -> 
    let strPc = string_suffix strPc 3 in
    let pc = 
      try
	int_of_string strPc 
      with
	Failure _ -> 
	  raise (JCH_failure (LBLOCK [ STR "int-of-string failure in get_method_stack_layout: " ; STR strPc ])) in
    (pc, new stack_layout_t layout pc destinations bytecode_size)) stack_layouts in
  new method_stack_layout_t stack_layouts local_var_table 
    
let translate_class
    ~(java_class: java_class_or_interface_int)
    ~(code_set: system_int)
    ?(proc_filter = fun p -> true)
    ?(simplify = false)
    ?(transform = false)
    ()
    =
  let methods = java_class#get_concrete_methods in
  let _ = simplifier := new JCHSimplify.simplifier_t code_set in
  let _ = transformer := new JCHTransform.transformer_t code_set in
  List.iter 
    (fun m -> 
      try 
	translate_method 
	  ~proc_filter:proc_filter 
	  ~simplify:simplify 
	  ~transform:transform 
	  ~java_method:m
	  ~code_set:code_set ()
      with
	JCH_failure p ->
	  begin
	    let _ = translation_failed#add !current_proc in
	    let msg = LBLOCK [ STR "type        : JCH_failure " ; p ; NL ;
			       STR "class       : " ; STR java_class#get_name#name ; NL ;
			       STR "method      : " ; STR m#get_signature#name ; NL ] in
	    let _ = pr_debug [STR "translation failed "; NL; msg; NL] in 
	    ch_error_log#add "JCHTranslateToCHIF.translate_class" msg 
	  end ) methods
    
let make_code_set s =
  F.mkSystem s 
    

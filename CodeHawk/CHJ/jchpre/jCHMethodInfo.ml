(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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
open CHPretty
open CHLanguage
open CHOnlineCodeSet
open CHUtils

(* chutil *)
open CHPrettyUtil
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHTranslateToCHIF

(* jchpre *)
open JCHBytecodeLocation
open JCHPreAPI
open JCHStackLayout
open JCHSystemSettings


module ClassMethodSignatureCollections = CHCollections.Make (
  struct
    type t = class_method_signature_int
    let compare cms1 cms2 = cms1#compare cms2
    let toPretty cms = cms#toPretty
  end)

module ClassFieldSignatureCollections = CHCollections.Make (
  struct
    type t = class_field_signature_int
    let compare cfs1 cfs2 = cfs1#compare cfs2
    let toPretty cfs = cfs#toPretty
  end)

module BytecodeLocationCollections = CHCollections.Make (
  struct
    type t = bytecode_location_int
    let compare loc1 loc2 = loc1#compare loc2
    let toPretty loc = loc#toPretty
  end)

let analysis_type_to_string t =
  match t with
  | TypeAnalysis -> "type-analysis"
  | TaintAnalysis -> "taint-analysis"
  | NumericAnalysis -> "numeric-analysis"
    
let analysis_type_of_string s =
  match s with
  | "type-analysis" -> TypeAnalysis
  | "taint-analysis" -> TaintAnalysis
  | "numeric-analysis" -> NumericAnalysis
  | _ -> raise (JCH_failure (LBLOCK [ STR s ; STR " is not a valid analysis type" ]))


class handler_block_t 
  (h:exception_handler_int) 
  (block:(int * opcode_t) list)
  (basic_blocks:(int * int) list):handler_block_int =
object (self)
  
  method get_start_pc = h#handler

  method get_end_pc = List.hd (List.rev self#get_pcs)

  method get_pcs = List.map (fun (pc,_) -> pc) block

  method get_handled_type =
    match h#catch_type with
    | Some e -> e
    | _ ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "Handler at ";
                 INT h#handler;
		 STR " does not have a handled type"]))
      
  method get_basic_blocks = 
    let start_block = 
      try 
	List.find (fun (s,e) -> s =  self#get_start_pc) basic_blocks
      with 
	Not_found ->
	  raise (JCH_failure 
		   (LBLOCK [ STR "error in get_basic_blocks: " ; 
			     INT h#handler ])) in
    start_block :: (List.filter (fun (s,e) -> 
      not (s = self#get_start_pc)) basic_blocks)
      
  method has_handled_type = 
    match h#catch_type with Some _ -> true | _ -> false
    
  method is_finally_block = not self#has_handled_type
    
  method is_empty = match block with 
  | [ i ] -> true 
  | [ i1 ; (_,i2) ] when (match i2 with OpGoto _ -> true | _ -> false) -> true
  |_ -> false
    
  method has_return_instruction = 
    List.exists (fun (_, opc) -> 
      match opc with OpReturn _ -> true | _ -> false) block
      
  method has_throw_instruction =
    List.exists (fun (_, opc) -> 
      match opc with OpThrow -> true | _ -> false) block
      
  method code_to_pretty  =
    let p = ref [] in
    let _ = List.iter (fun (pc,opcode) ->
      p := (LBLOCK [ fixed_length_pretty ~alignment:StrRight (INT pc) 4 ; 
		     STR " " ; opcode_to_pretty opcode ; NL ]) :: !p) block in
    LBLOCK (List.rev !p)
      
  method toPretty = pretty_print_list block (fun (i,_) -> INT i) "[" "; " "]"
end
  
  
class exception_handlers_t 
  (table:exception_handler_int list):exception_handlers_int =
object (self)
  val handlers = new IntCollections.table_t

  method set_handler_block 
    (pc:int) 
    (block:(int * opcode_t) list) 
    (basic_blocks: (int * int) list) = 
    let handler = 
      try
	List.find (fun h -> h#handler = pc) table
      with
	Not_found -> 
	  raise (JCH_failure 
		   (LBLOCK [ STR "set_handler_block: No handler found at pc = " ; 
			     INT pc ])) in
    handlers#set pc (new handler_block_t handler block basic_blocks)
      
  method get_handler_block (pc:int) = 
    match handlers#get pc with Some b -> b | _ ->
      raise (JCH_failure 
	       (LBLOCK [ STR "No handler block found at pc = " ; INT pc ]))
	
  method get_handler_blocks = handlers#listOfValues
    
  method get_exn_handlers (pc:int) =
    let handlers = List.filter (fun h -> 
      h#h_start <= pc && pc <= h#h_end && 
	match h#catch_type with Some _ -> true | _ -> false) table in
    List.map (fun h -> (h#handler, Option.get h#catch_type))
      (List.sort (fun h1 h2 -> Stdlib.compare h1#handler h2#handler) handlers)
      
  method get_finally_handler (pc:int) =
    try
      let h = List.find 
	(fun h -> 
	  h#h_start <= pc && pc <= h#h_end && 
	    match h#catch_type with None -> true | _ -> false)
	table in
      h#handler
    with
      Not_found ->
	raise (JCH_failure 
		 (LBLOCK [ STR "No finally handler found at pc = " ; INT pc ]))

  method get_exceptions_caught = List.map snd self#get_all_exn_handlers
	  
  method get_all_exn_handlers =
    List.map (fun h -> (h#handler, Option.get h#catch_type))
      (List.filter (fun h -> 
	match h#catch_type with Some _ -> true | _ -> false) table)
      
  method get_all_finally_handlers =
    let s = new IntCollections.set_t in
    let _ = List.iter (fun h -> s#add h#handler)
      (List.filter (fun h -> 
	match h#catch_type with None -> true | _ -> false) table) in
    s#toList
      
  method get_all_handler_pcs =
    let s = new IntCollections.set_t in
    let _ = List.iter (fun h -> s#add h#handler) table in
    s#toList
      
  method has_finally_handler (pc:int) =
    List.exists (fun h -> 
      h#h_start <= pc && pc <= h#h_end && 
	match h#catch_type with None -> true | _ -> false)
      table
      
  method code_to_pretty =
    let p = ref [] in
    let _ = handlers#iter (fun _ h -> 
      p := (LBLOCK [ h#code_to_pretty ; NL ]) :: !p) in
    LBLOCK [ pretty_print_list table (fun h ->
      LBLOCK [ h#toPretty ; NL ]) "" "" "" ; NL ; LBLOCK !p ; NL ]
      
      
  method toPretty = 
    LBLOCK [ STR "Exception handlers"; NL ; 
	     pretty_print_list table (fun h -> 
	       LBLOCK [ h#toPretty ; NL ]) "" "" "" ; NL ; 
	     handlers#toPretty ; NL ]
      
      
end
  
	
class method_info_t (info_type:method_info_type_t):method_info_int =
object (self:'a)
  val mutable method_info_type = info_type
  val mutable argument_assumptions = []
  val callees = new ClassMethodSignatureCollections.set_t
  val callers = new ClassMethodSignatureCollections.set_t
  val field_writes = new ClassFieldSignatureCollections.set_t
  val field_reads  = new ClassFieldSignatureCollections.set_t
  val exception_handlers = 
    let table = match info_type with
      | ConcreteMethod m ->
	 begin
	   match m#get_implementation with 
	     Bytecode bc -> bc#get_exception_table
	   | _ -> []
	 end
      | _ -> [] in
    new exception_handlers_t table
  val mutable stack_layout = None
  val mutable num_variables = (-1)
  val mutable dynamically_dispatched = false
  val mutable called_by_reflection = false
  val mutable indirectly_called = false
  val mutable main_method = false
  val mutable analysis_exclusions = []
    
  method set_analysis_exclusions l = 
    analysis_exclusions <- l

  method add_argument_assumption x = 
    argument_assumptions <- x :: argument_assumptions

  method get_argument_assumptions = 
    argument_assumptions 

  method has_argument_assumptions = 
    match argument_assumptions with [] -> false | _ -> true
    
  (* to be refined later for different types of analysis *)
  method need_not_be_analyzed = 
    match analysis_exclusions with [] -> false | _ -> true
    
  method get_analysis_exclusions = analysis_exclusions
    
  method add_callee (cms:class_method_signature_int) = callees#add cms

  method add_caller (cms:class_method_signature_int) = callers#add cms

  method add_field_read (cfs:class_field_signature_int) = field_reads#add cfs

  method add_field_write (cfs:class_field_signature_int) = field_writes#add cfs

  method set_translation_failure = match method_info_type with
    ConcreteMethod m -> 
      method_info_type <- UntranslatedConcreteMethod m
  | _ ->
    raise (JCH_failure
	     (LBLOCK [ self#toPretty ; STR " is not a concrete method" ; 
		       STR "; it cannot fail to translate" ]))
      
  method set_num_variables (num:int) = num_variables <- num
    
  method set_dynamically_dispatched = dynamically_dispatched <- true
  method is_dynamically_dispatched  = dynamically_dispatched
    
  method set_called_by_reflection = called_by_reflection <- true
  method is_called_by_reflection  = called_by_reflection
    
  method set_indirectly_called = indirectly_called <- true
  method is_indirectly_called  = indirectly_called
    
  method set_main_method = main_method <- true
  method is_main_method  = main_method
    
  method get_class_method_signature = match method_info_type with
  | ConcreteMethod m 
  | NativeMethod m
  | AbstractMethod m
  | ExcludedMethod (m,_)
  | UntranslatedConcreteMethod m -> m#get_class_method_signature
  | Stub x -> x#get_cms
  | InterfaceInheritedMethod cms
  | MissingMethod cms -> cms
    
  method get_generic_signature = match method_info_type with
  | ConcreteMethod m
  | NativeMethod m
  | AbstractMethod m
  | ExcludedMethod (m,_)
  | UntranslatedConcreteMethod m ->
    begin
      match m#generic_signature with Some s -> s | _ ->
	raise (JCH_failure 
		 (LBLOCK [ self#toPretty ; 
			   STR " does not have a generic signature" ]))
    end
  | _ -> raise (JCH_failure 
		  (LBLOCK [ self#toPretty ; 
			    STR " does not have a generic signature" ]))
    
  method has_generic_signature = 
    match method_info_type with
    | ConcreteMethod m
    | NativeMethod m
    | AbstractMethod m
    | ExcludedMethod (m,_)
    | UntranslatedConcreteMethod m ->
      begin match m#generic_signature with Some s -> true | _ -> false end
    | _ -> false
    
  method get_class_name = self#get_class_method_signature#class_name
    
  method get_method_name = self#get_class_method_signature#name
    
  method get_index = self#get_class_method_signature#index
    
  method get_procname = make_procname self#get_class_method_signature#index
    
  method get_implementation = method_info_type
    
  method get_method =
    match method_info_type with 
    | ConcreteMethod m | NativeMethod m -> m 
    | _ ->
       raise
         (JCH_failure (LBLOCK [ STR "Method " ; self#toPretty ; NL ;
				STR " does not have a concrete method " ]))

  method get_stub =
    match method_info_type with
    | Stub s -> s
    | _ ->
       raise
         (JCH_failure (LBLOCK [ STR "Method " ; self#toPretty ; NL ;
                                STR " is not a stubbed method " ]))
      
  method get_bytecode = match method_info_type with
  | ConcreteMethod m | UntranslatedConcreteMethod m ->
    begin
      match m#get_implementation with Bytecode bc -> bc | _ ->
	raise (JCH_failure (STR "Internal error in JCHMethodInfo.get_bytecode"))
    end
  | _ ->
    raise (JCH_failure
	     (LBLOCK [ STR "Method " ; self#get_class_method_signature#toPretty ;
		       STR " does not have bytecode" ]))
      
  method get_line_number (pc:int) = 
    match self#get_bytecode#get_source_line_number pc with
      Some line -> line
    | _ -> raise (JCH_failure 
		    (LBLOCK [ STR "No line number available for pc = " ; 
			      INT pc ]))
      
  method get_line_number_table = 
    match self#get_bytecode#get_line_number_table with
      Some table -> table
    | _ -> raise (JCH_failure 
		    (LBLOCK [ STR "No line number table available for " ; 
			      self#get_class_method_signature#toPretty ]))

  method get_register_variable (index:int) (ty:value_type_t) =
    get_register_variable index ty
      
  method get_local_variable_table =
    match self#get_bytecode#get_local_variable_table with
      Some table -> table
    | _ -> raise (JCH_failure 
		    (LBLOCK [ STR "No local variable table available for " ;
			      self#get_class_method_signature#toPretty ]))
      
  method get_local_variable_name (index:int) (pc:int) =
    match self#get_bytecode#get_local_variable_table with
    | Some table ->
      begin
	try
	  let (_,_,name,_,_ ) = 
	    List.find (fun (low,len,_,_,nreg) -> nreg = index && 
		(pc >= low) && (pc <= low+len)) table in
	  name
	with
	  Not_found -> "none"
      end
    | _ -> "none"
      
  method get_varname_mapping (pc:int) =
    if self#has_local_variable_table then
      (fun i -> if self#has_local_variable_name i pc then
	  self#get_local_variable_name i pc 
	else
	  default_varname_mapping i)
    else
      default_varname_mapping

  method get_argname_mapping = 
    if self#has_local_variable_table then
      (fun i -> if self#has_local_variable_name i 0 then
	  self#get_local_variable_name i 0
	else 
	  default_argname_mapping i)
    else
      default_argname_mapping
      
  method get_local_variable_type_table =
    match self#get_bytecode#get_local_variable_type_table with
      Some table -> table
    | _ -> raise (JCH_failure 
		    (LBLOCK [ STR "No local variable type table available for " ;
			      self#get_class_method_signature#toPretty ]))
      
  method get_local_variable_type (n:int) (pc:int) =
    match self#get_bytecode#get_local_variable_table with
      Some table ->
	begin
	  try
	    let (_,_,_,ty,_) =
	      List.find (fun (low,len,_,_,nreg) -> n = nreg && 
		  (pc >= low) && (pc <= low+len)) table in
	    ty
	  with
	    _ ->
            raise (JCH_failure
                     (LBLOCK [ STR "No type found in local variable table for " ;
			       STR "reg: " ; INT n ; STR " at pc = " ; INT pc ; 
			       STR " in " ; self#get_class_method_signature#toPretty ]))
	end
    | _ ->
       raise (JCH_failure
                (LBLOCK [ STR "No type found in local variable table for " ;
			  STR "reg: " ; INT n ; STR " at pc = " ; INT pc ; 
			  STR " in " ; self#get_class_method_signature#toPretty ]))
      
  method get_previous_bytecode_offset (pc:int) =
    match self#get_bytecode#get_code#previous pc with Some i -> i | _ ->
      raise (JCH_failure (LBLOCK [ STR "No previous bytecode instruction for pc = " ; INT pc ]))
	
  method get_next_bytecode_offset (pc:int) =
    match self#get_bytecode#get_code#next pc with Some i -> i | _ ->
      raise (JCH_failure (LBLOCK [ STR "No next bytecode instruction for pc = " ; INT pc ]))
	
  method get_virtual_calls =
    if self#has_bytecode then
      let s = new ClassMethodSignatureCollections.set_t in
      begin
	Array.iter (fun opc ->	match opc with
	  OpInvokeVirtual (TClass cn, ms) -> s#add (make_cms cn ms)
	| _ -> () ) self#get_bytecode#get_code#opcodes ;
	s#toList
      end
    else match method_info_type with
      Stub s -> s#get_virtual_calls
    | _ -> []
      
  method get_interface_calls =
    if self#has_bytecode then
      let s = new ClassMethodSignatureCollections.set_t in
      begin
	Array.iter (fun opc -> match opc with
	  OpInvokeInterface (cn,ms) -> s#add (make_cms cn ms)
	| _ -> ()) self#get_bytecode#get_code#opcodes ;
	s#toList
      end
    else match method_info_type with
      Stub s -> s#get_interface_calls
    | _ -> []
      
  method has_previous_bytecode_offset (pc:int) =
    self#has_bytecode
    && match self#get_bytecode#get_code#previous pc with Some _ -> true | _ -> false
      
  method has_next_bytecode_offset (pc:int) =
    self#has_bytecode
    && match self#get_bytecode#get_code#next pc with Some _ -> true | _ -> false
      
      
  method private has_local_variable_entry (n:int) (pc:int) =
    self#has_local_variable_table &&
      match self#get_bytecode#get_local_variable_table with
      | Some table ->
	  List.exists (fun (low,len,_,ty,nreg) -> 
	    n = nreg && (pc >= low) && (pc < low+len)) table
      | _ -> false

  method has_local_variable_name = self#has_local_variable_entry

  method has_local_variable_type = self#has_local_variable_entry
	
  method has_line_number (pc:int) =
    self#has_bytecode
    && (match self#get_bytecode#get_source_line_number pc with Some _ -> true | _ -> false)
      
  method has_line_number_table =
    self#has_bytecode
    && (match self#get_bytecode#get_line_number_table with Some _ -> true | _ -> false)
      
  method has_local_variable_table =
    self#has_bytecode
    && (match self#get_bytecode#get_local_variable_table with Some _ -> true | _ -> false)
      
  method has_local_variable_type_table =
    self#has_bytecode
    && (match self#get_bytecode#get_local_variable_type_table with Some _ -> true | _ -> false)

  method has_method_stack_layout_loaded =
    match stack_layout with Some _ -> true | _ -> false
      
  method has_method_stack_layout = match stack_layout with Some _ -> true | _ ->
    match method_info_type with ConcreteMethod _ -> true | _ -> false
      
  method get_byte_count = if self#has_bytecode then self#get_bytecode#get_code#length else 0
      
  method get_instruction_count =
    if self#has_bytecode then
      let count = ref 0 in
      let _ = self#bytecode_iteri (fun _ _ -> count := !count + 1) in
      !count
    else
      0
		
  method get_call_instruction_count =
    let count = ref 0 in
    let _ = if self#has_bytecode then 
	self#bytecode_iteri (fun _ i ->
	  match i with
	  | OpInvokeVirtual _ 
	  | OpInvokeSpecial _ 
	  | OpInvokeStatic _
	  | OpInvokeInterface _ -> count := !count + 1
	  | _ -> ()) in
    !count
      
  method get_stack_instruction_count =
    let count = ref 0 in
    let _ = if self#has_bytecode then
	self#bytecode_iteri (fun _ i ->
	  match i with 
	  | OpPop | OpPop2 | OpDup | OpDupX1 | OpDupX2 | OpDup2 | OpDup2X1 | OpDup2X2
	  | OpSwap | OpLoad _  | OpStore _ -> count := !count + 1
	  | _ -> ()) in
    !count
      
  method get_controlflow_instruction_count =
    let count = ref 0 in
    let _ = if self#has_bytecode then
	self#bytecode_iteri (fun _ i ->
	  match i with
	  | OpIfEq _ | OpIfNe _ | OpIfLt _ | OpIfGe _ | OpIfGt _ | OpIfLe _ 
	  | OpIfNull _ | OpIfNonNull _
	  | OpIfCmpEq _ | OpIfCmpNe _ | OpIfCmpLt _ | OpIfCmpGe _ | OpIfCmpGt _
	  | OpIfCmpAEq _ | OpIfCmpANe _ 
	  | OpGoto _ -> count := !count + 1
	  | _ -> ()) in
    !count
      
  method get_arithmetic_instruction_count =
    let count = ref 0 in
    let _ = if self#has_bytecode then
	self#bytecode_iteri (fun _ i ->
	  match i with
	  | OpAdd _ | OpSub _ | OpMult _ | OpDiv _ | OpRem _ | OpNeg _
	  | OpIShl | OpLShl | OpIShr | OpLShr | OpIUShr | OpLUShr 
	  | OpIAnd | OpLAnd | OpIOr | OpLOr | OpIXor | OpLXor -> count := !count + 1
	  | _ -> ()) in
    !count
            
  method get_exception_table = 
    if self#has_bytecode then
      self#get_bytecode#get_exception_table
    else
      []

  method get_exceptions_caught = exception_handlers#get_exceptions_caught

  method get_exception_handlers = 
    exception_handlers
    
  method is_handler_pc (pc:int) =
    List.mem pc (List.map (fun h -> h#handler) self#get_exception_table)
      
  method get_try_blocks_pcs (handler_pc:int) =
    let entries = List.filter (fun h -> h#handler = handler_pc) self#get_exception_table in
    let pcs = new IntCollections.set_t in
    let opcodes = self#get_bytecode#get_code#opcodes in
    begin
      List.iter (fun h ->
	Array.iteri (fun i opc -> match opc with OpInvalid -> () | _ -> 
	  if i >= h#h_start && i <= h#h_end then pcs#add i) 
	  opcodes ) entries ;
      pcs#toList
    end
      
      
  method get_exceptions = match method_info_type with
    | ConcreteMethod m
      | NativeMethod m
      | AbstractMethod m
      | ExcludedMethod (m,_)
      | UntranslatedConcreteMethod m -> m#get_exceptions   (* checked exceptions *)
    | Stub x -> x#get_exceptions
    | InterfaceInheritedMethod _
      | MissingMethod _ -> []
    
  method get_callees = callees#toList
  method get_callers = callers#toList
  method get_field_writes = field_writes#toList
  method get_field_reads  = field_reads#toList
    
  method get_visibility = match method_info_type with
    | ConcreteMethod m 
      | NativeMethod m
      | AbstractMethod m
      | ExcludedMethod (m,_)
      | UntranslatedConcreteMethod m -> m#get_visibility
    | Stub x -> x#get_visibility
    | InterfaceInheritedMethod _
      | MissingMethod _ -> Public
                         
  method get_method_stack_layout = 
    (* to be removed *)
    match stack_layout with Some layout -> layout | _ ->
      match method_info_type with
      | ConcreteMethod m -> 
	let system = new system_t (new symbol_t "dummy") in
	let layout = get_method_stack_layout system m in
	begin stack_layout <- Some layout ; layout end
      | _ ->
	raise (JCH_failure (LBLOCK [ STR "Method " ; 
				     STR self#get_method_name ; 
				     STR " is not a concrete method" ]))


  method set_saved_method_stack_layout (bc:bcdictionary_int) (node:xml_element_int) =
    match stack_layout with Some layout -> () | _ ->   
      match method_info_type with
      | ConcreteMethod _ ->
	let layout = self#get_method_stack_layout in
	let iinode = node#getTaggedChild "instructions" in
	read_xml_and_set_method_stack_layout bc iinode layout 
      | _ ->
	raise (JCH_failure (LBLOCK [ STR "Method " ; 
				     STR self#get_method_name ; 
				     STR " is not a concrete method" ]))
	  
  method bytecode_iteri (f:int -> opcode_t -> unit) =
    if self#has_bytecode then self#get_bytecode#get_code#iteri f
      
  method has_virtual_calls =
    self#has_bytecode &&
      (Array.fold_left (fun a opc -> 
	a || (match opc with OpInvokeVirtual _ | OpInvokeInterface _ -> true | _ -> false))
	 false self#get_bytecode#get_code#opcodes)
      
  method get_opcode (pc:int) = self#get_bytecode#get_code#at pc
    
  method get_pc_to_instr_index =
    let instrnArray = self#get_bytecode#get_code#offset_to_instrn_array in
    let fn n = 
      try
	(instrnArray.(n)) 
      with
	_ ->
	  let length = Array.length instrnArray in
	  instrnArray.(length - 1)  in
    fn
      
  method get_variable_count = 
    if num_variables >= 0 then num_variables else
      raise (JCH_failure (LBLOCK [ STR "Size of scope has not been set for " ; 
				   self#get_class_method_signature#toPretty ]))
	
  method equal (other:'a) = self#get_index = other#get_index 

  method compare (other: 'a) = Stdlib.compare self#get_index other#get_index
    
  method is_missing = match method_info_type with MissingMethod _ -> true | _ -> false

  method is_stubbed = match method_info_type with Stub _ -> true | _ -> false
    
  method failed_to_translate = 
    self#has_jsr_instructions ||
      match method_info_type with UntranslatedConcreteMethod _ -> true | _ -> false
      
  method is_abstract = match method_info_type with
    Stub x -> x#is_abstract
  | InterfaceInheritedMethod _
  | AbstractMethod _ -> true
  | _ -> false
    
  method is_bridge = match method_info_type with
    ConcreteMethod c | UntranslatedConcreteMethod c | ExcludedMethod (c,_) -> c#is_bridge
  | Stub x -> x#is_bridge
  | _ -> false
    
  method is_native = match method_info_type with NativeMethod _ -> true | _ -> false
    
  method is_synchronized = match method_info_type with
    ConcreteMethod m -> m#is_synchronized
  | _ -> false
    
  method is_final = match method_info_type with
    ConcreteMethod m 
  | NativeMethod m
  | AbstractMethod m
  | ExcludedMethod (m,_)
  | UntranslatedConcreteMethod m -> m#is_final
  | Stub x -> x#is_final
  | InterfaceInheritedMethod _
  | MissingMethod _ -> false
    
  method is_static = match method_info_type with
    ConcreteMethod m 
  | NativeMethod m
  | AbstractMethod m
  | ExcludedMethod (m,_)
  | UntranslatedConcreteMethod m -> m#is_static
  | Stub x -> x#is_static
  | InterfaceInheritedMethod _
  | MissingMethod _ -> false
    
  (* Java visibility rules
     
     Class    Package    Subclass    World
     ----------------------------------------------------
     public          Y         Y           Y         Y
     protected       Y         Y           Y         N
     default         Y         Y           N         N
     private         Y         N           N         N
     ----------------------------------------------------
  *)
  method is_private          = match self#get_visibility with Private -> true | _ -> false
  method is_protected        = match self#get_visibility with Protected -> true | _ -> false
  method is_public           = match self#get_visibility with Public -> true | _ -> false
  method is_default_access   = match self#get_visibility with Default -> true | _ -> false

  method is_constructor =
    let cms = self#get_class_method_signature in
    let name = cms#method_signature#name in
    name = "<init>"

  method is_class_constructor =
    let cms = self#get_class_method_signature in
    let name = cms#method_signature#name in
    name = "<clinit>"

  method is_excluded = match method_info_type with ExcludedMethod _ -> true | _ -> false

  method has_bytecode =
    match method_info_type with
    | ConcreteMethod _ | UntranslatedConcreteMethod _ -> true | _ -> false

  method has_handlers =
    self#has_bytecode && (match self#get_exception_table with [] -> false | _ -> true)
      
  method has_jsr_instructions = if self#has_bytecode then
      Array.fold_left (fun r opc -> r || (match opc with OpJsr _ -> true | _ -> false)) 
	false self#get_bytecode#get_code#opcodes
    else
      false
	
  method has_num_variables = num_variables >= 0
    
  method get_name = 
    let cms = self#get_class_method_signature in
    let cmsd = cms#class_method_signature_data in
    let descr = cmsd#method_signature#method_signature_data#descriptor in
    let (_,args) = 
      List.fold_left (fun (fst,acc) a -> 
	if fst then 
	  (false,"(" ^ acc ^ (value_type_to_string a)) 
	else 
	  (fst,acc ^ "," ^ (value_type_to_string a))) (true,"") descr#arguments in
    let args = match descr#arguments with [] -> args ^ "()" | _ -> args ^ ")" in
    cms#class_name#name ^ "." ^ cmsd#name ^ args ^
      (match descr#return_value with Some vt -> ":" ^ (value_type_to_string vt) | _ -> "")

  method get_signature_string = 
    self#get_class_method_signature#method_signature#to_signature_string			

  method toPretty = 
    let scope_size_p = if self#has_num_variables then 
	LBLOCK [ STR " (scope: " ; INT self#get_variable_count ; STR ")" ] else STR "" in
    let pDynamicallyDispatched = 
      if self#is_dynamically_dispatched then STR " (dynamically dispatched)" else STR "" in
    let pMainMethod = if self#is_main_method then STR " (main method)" else STR "" in
    let pCalledByReflection = 
      if self#is_called_by_reflection then STR " (called by reflection)" else STR "" in
    let pIndirectlyCalled =
      if self#is_indirectly_called then STR " (called indirectly)" else STR "" in
    let visibility = 
      if self#is_private then "private"
      else if self#is_default_access then "default"
      else if self#is_protected then "protected"
      else "public" in
    let mInfoType = match method_info_type with
      | ConcreteMethod _ -> "concrete"
      | NativeMethod _ -> "native"
      | AbstractMethod _ -> "abstract"
      | ExcludedMethod _ -> "excluded" 
      | UntranslatedConcreteMethod _ -> "untranslated"
      | Stub _ -> "stub"
      | InterfaceInheritedMethod _ -> "interface inherited"
      | MissingMethod _ -> "missing" in
    LBLOCK [ self#get_class_method_signature#toPretty ; STR " (" ; 
	     pp_quantity callers#size "caller" "callers" ; STR ", " ;
	     pp_quantity callees#size "callee" "callees" ; STR ")" ;
	     STR " (" ; STR visibility ; STR ")" ;
	     STR " (type: " ; STR mInfoType ; STR ") " ;
	     pDynamicallyDispatched ; pCalledByReflection ; pMainMethod ; pIndirectlyCalled ;
	     if self#is_bridge then STR " (bridge)" else STR "" ; scope_size_p ]
      
  method bytecode_to_pretty =
    let genericP = if self#has_generic_signature then 
	LBLOCK [ STR "Generic Signature: " ; NL ; self#get_generic_signature#toPretty ; NL ]
      else
	STR "" in
    let pStatic = if self#is_static then STR " (static)" else STR "" in
    let pAccess = 
      if self#is_private then STR " (private)" 
      else if self#is_default_access then STR " (default)" 
      else STR "" in
    let converter = self#get_pc_to_instr_index in
    let line_number_table_to_pretty l =
      let p = ref [] in
      let _ = List.iter (fun (pc,line) ->
	p := (LBLOCK [ fixed_length_pretty ~alignment:StrRight (INT pc) 4   ; STR "  " ; 
		       fixed_length_pretty ~alignment:StrRight (INT line) 4 ; NL ]) :: !p) l in
      LBLOCK [ STR "Line number table" ; NL ; 
	       STR " -----------------" ; NL ; LBLOCK (List.rev !p) ; NL ] in
    let local_variable_table_to_pretty l =
      let p = ref [] in
      let _ = List.iter (fun (start_pc, length, name, ty, index) ->
	p := (LBLOCK [ fixed_length_pretty ~alignment:StrRight (INT start_pc) 4 ; STR "  " ;
		       fixed_length_pretty ~alignment:StrRight (INT length) 4   ; STR "  " ; 
		       fixed_length_pretty (STR name) 15 ; STR "  " ;
		       fixed_length_pretty ~alignment:StrRight (INT index) 3 ; STR "  " ;
		       value_type_to_pretty ty ; NL ]) :: !p) l in
      LBLOCK [ STR "Local variable table" ; NL ;
	       STR "---------------------" ; NL ; LBLOCK (List.rev !p) ; NL ] in
    let local_variable_type_table_to_pretty l =
      let p = ref [] in
      let _ = List.iter (fun (start_pc, length, name, ty, index) ->
	p := (LBLOCK [ fixed_length_pretty ~alignment:StrRight (INT start_pc) 4 ; STR "  " ;
		       fixed_length_pretty ~alignment:StrRight (INT length) 4   ; STR "  " ; 
		       fixed_length_pretty (STR name) 15 ; STR "  " ;
		       fixed_length_pretty ~alignment:StrRight (INT index) 3 ; STR "  " ;
		       ty#toPretty ; NL ]) :: !p) l in
      LBLOCK [ STR "Local variable type table" ; NL ;
	       STR "---------------------" ; NL ; LBLOCK (List.rev !p) ; NL ] in
    if self#has_bytecode then
      let pLineNrTable = if self#has_line_number_table then
	  line_number_table_to_pretty self#get_line_number_table
	else
	  STR "" in
      let pLocalVarTable = if self#has_local_variable_table then
	  local_variable_table_to_pretty self#get_local_variable_table
	else
	  STR "" in
      let pLocalVarTypeTable = if self#has_local_variable_type_table then
	  local_variable_type_table_to_pretty self#get_local_variable_type_table
	else
	  STR "" in
      
      let pExceptionTable = if self#has_handlers then 
	  self#get_exception_handlers#toPretty else STR "" in
      let bc = self#get_bytecode in
      let code = bc#get_code in
      let p = ref [] in
      begin
	for i = code#length - 1 downto 0 do
	  let opcode = code#at i in
	  match opcode with
	    OpInvalid -> ()
	  | _ -> 
	    let has_line_nr = self#has_line_number i in
	    let pIndex = STR (fixed_length_string ~alignment:StrRight (string_of_int i) 5 ) in
	    let pLineNumber = if has_line_nr then 
		STR (fixed_length_string ~alignment:StrRight 
		       (string_of_int (self#get_line_number i)) 7 )
	      else
		STR "" in
	    let pInstrNumber = 
	      fixed_length_pretty ~alignment:StrRight (INT (converter i)) 6 in
	    p := (LBLOCK [ 
	      INDENT (2, LBLOCK [ pIndex ; pInstrNumber ; pLineNumber ; 
				  STR "  " ; opcode_to_pretty (code#at i) ; NL ])]) :: !p
	done ;
	LBLOCK [ genericP ; STR self#get_name ; pStatic ; pAccess ; NL ;
		 (LBLOCK !p) ; NL ;
		 pLineNrTable ; NL ; 
		 pExceptionTable ; pLocalVarTable ; pLocalVarTypeTable ; NL ]
      end
    else
      LBLOCK [ STR self#get_name ; STR ": no bytecode found" ]
	
end
  
let make_method_info (m:method_int) =
  let method_info_type = 
    if m#is_concrete then
      match m#get_implementation with
      | Bytecode _ -> ConcreteMethod m
      | Native -> NativeMethod m
    else 
      AbstractMethod m in
  new method_info_t method_info_type
    
let make_method_stub_info (x:function_summary_int) =
  new method_info_t (Stub x)
    
let make_missing_method_info (cms:class_method_signature_int) =
  new method_info_t (MissingMethod cms)
    
let make_interface_inherited_method_info (cms:class_method_signature_int) =
  new method_info_t (InterfaceInheritedMethod cms)
    

(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
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
open CHAtlas
open CHLanguage
open CHNumerical
open CHOnlineCodeSet
open CHPretty
open CHUtils
   
(* chutil *)
open CHDot
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI

(* ============================================================== Code graph === *)

type cmd_t = (code_int, cfg_int) command_t 

class type cmd_list_int =
object
  method cmd_list : cmd_t list
  method reverse_cmds: unit
  method toPretty: pretty_t
end

class type code_graph_int =
object 
  (* setters *)
  method add_node  : symbol_t -> cmd_t list -> unit
  method add_edge  : symbol_t -> symbol_t -> unit
  method set_cmd   : symbol_t -> cmd_t list -> unit

  (* accessors *)
  method get_cmds     : symbol_t -> cmd_list_int

  (* actions *)
  method remove_edge: symbol_t -> symbol_t -> unit

  (* transformers *)
  method loopbound_transform:
    node:symbol_t ->
      nodecmds:cmd_t list ->
	initsrcs:symbol_t list ->
	  intratgts:symbol_t list ->
	    exittgts:symbol_t list ->
	      initcmds:cmd_t list ->
		intracmds:cmd_t list ->
		  exitcmds:cmd_t list -> unit

  method loopcut_transform:
    node:symbol_t -> xcmds:cmd_t list -> 
      intrasrcs:symbol_t list -> exittgts:symbol_t list -> unit

  method sink_transform:
    node:symbol_t -> preds:(symbol_t * cmd_t list) list -> unit

  (* converters *)
  method to_cfg: symbol_t -> symbol_t -> cfg_int
end

(* ============ SystemSettings ============================================= *)

class type system_settings_int =
object
  (* setters *)
  method add_classpath_unit              : string -> unit
  method add_summary_classpath_unit      : string -> unit
  method add_preanalyzed_classpath_unit  : string -> unit
  method record_start_time               : unit
  method set_verbose                     : unit
  method set_print_chif                  : unit
  method set_excluded_classes            : int list -> unit
  method set_max_instructions            : int -> unit
  method add_pkg_exclude                 : string -> unit

  method set_results_directory           : string -> unit
  method set_output_directory            : string -> unit
  method set_project_name                : string -> unit
  method set_logfile                     : string -> unit
  method log_error                       : pretty_t -> unit
  method disable_logging_missing_classes : unit

  (* accessors *)
  method get_classpath        : JCHFile.cp_unit_t list
  method get_summary_classpath: JCHFile.cp_unit_t list
  method get_preanalyzed_classpath: JCHFile.cp_unit_t list
  method get_preanalyzed_directory: string
  method get_classpath_string : string 
  method get_classpath_units  : string list
  method get_time_since_start : float
  method get_output_directory : string
  method get_results_directory: string
  method get_project_name     : string
  method get_max_instructions : int
  method get_pkg_excludes     : string list

  (* predicates *)
  method is_excluded_class    : int -> bool
  method is_jdk_jar           : string -> bool
  method is_verbose           : bool
  method print_chif           : bool
  method has_instruction_limit: bool
  method is_logging_missing_classes_enabled: bool

  (* printing *)
  method to_pretty: pretty_t
end


(* ============ SignatureBindings ========================================== *)
class type signature_bindings_int =
object
  (* accessors *)
  method get_this_variable           : variable_t
  method get_indexed_ref_arguments   : (int * variable_t) list
  method get_indexed_string_arguments: (int * variable_t) list
  method get_ref_argument_types      : (variable_t * value_type_t) list

  (* predicates *)
  method has_this_variable: bool
  method is_static        : bool
end


(* ============= ClassSummary ============================================== *)

type property_accessor_t =
  | MethodAccessor of method_signature_int

type class_property_t =
  | LogicalSize of property_accessor_t

class type class_summary_int =
object
  (* accessors *)
  method get_class_name : class_name_int
  method get_super_class: class_name_int
  method get_interfaces : class_name_int list
  method get_methods    : method_signature_int list
  method get_fields     : field_signature_int list
  method get_class_properties: class_property_t list
  method get_default_implementations: class_name_int list

  (* predicates *)
  method is_interface   : bool
  method is_final       : bool
  method is_abstract    : bool
  method is_immutable   : bool
  method is_dispatch    : bool
  method has_super_class: bool
  method defines_method : method_signature_int -> bool
  method defines_field  : field_signature_int -> bool

  (* printing *)
  method toPretty       : pretty_t
end


(* ============== BytecodeLocation ========================================= *)

class type bytecode_location_int =
object ('a)
  method compare                   : 'a -> int

  (* accessors *)
  method m: int
  method i: int
  method get_class_method_signature: class_method_signature_int
  method get_method_index          : int
  method get_pc                    : int

  (* predicates *)
  method is_modified               : bool

  (* printing *)
  method toString                  : string
  method toPretty                  : pretty_t
end

class type operation_locations_int =
object
  method add_operation:bytecode_location_int -> operation_t -> unit
  method get_operation:bytecode_location_int -> operation_t
  method has_operation:bytecode_location_int -> bool
end


(* ============== Invariant ================================================ *)

class type j_invariant_int =
object ('a)
  (* setters *)
  method set_domain: string -> atlas_t -> unit

  (* accessors *)
  method get_domains       : (string * atlas_t) list
  method get_domain        : string -> atlas_t
  
  (* predicates *)
  method has_domain : string -> bool
  method is_bottom  : bool
  method is_not_null: variable_t -> bool
  method is_null    : variable_t -> bool
  method can_be_null: variable_t -> bool

  (* printing *)
  method toPretty   : pretty_t
end


class type invariants_int =
object
  (* setters *)
  method add_invariant: string -> symbol_t -> symbol_t -> string -> atlas_t -> unit

  (* accessors *)
  method get_invariant: ?mode:string -> bytecode_location_int -> j_invariant_int
end

(* ================= FieldInfo ============================================= *)

class type field_stub_int =
object ('a)
  (* accessors *)
  method get_class_name     : class_name_int
  method get_signature      : field_signature_int
  method get_class_signature: class_field_signature_int
  method get_value          : constant_value_t
  method get_visibility     : access_t
  method get_defining_class : class_name_int
  method get_defining_class_field_signature : class_field_signature_int

  (* predicates *)
  method is_static          : bool
  method is_final           : bool
  method is_not_null        : bool
  method is_interface_field : bool
  method is_constant        : bool
  method is_inherited       : bool
  method has_value          : bool

  (* cloning *)
  method set_inherited: class_field_signature_int -> 'a

  (* printing *)
  method toPretty    : pretty_t
end

type field_info_type_t =
| ConcreteField of field_int
| StubbedField of field_stub_int
| MissingField of class_field_signature_int

class type field_info_int =
object ('a)
  method compare            : 'a -> int

  (* setters *)
  method add_writing_method : class_method_signature_int -> unit
  method add_reading_method : class_method_signature_int -> unit
  method set_not_null       : unit           (* to be used only for final static fields *)
  method set_array_length   : int -> unit    (* to be used only for final static fields *)

  (* accessors *)
  method get_index          : int
  method get_field          : field_info_type_t
  method get_class_name     : class_name_int
  method get_class_signature: class_field_signature_int
  method get_value          : constant_value_t
  method get_array_length   : int
  method get_reading_methods: class_method_signature_int list
  method get_writing_methods: class_method_signature_int list
  method get_visibility     : access_t

  (* predicates *)
  method is_missing        : bool
  method is_stubbed        : bool
  method is_static         : bool
  method is_final          : bool
  method is_constant       : bool
  method is_initialized    : bool
  method is_not_null       : bool

  method is_private        : bool
  method is_protected      : bool
  method is_public         : bool
  method is_default_access : bool

  method has_value         : bool
  method has_array_length  : bool

  method is_accessible_to_stubbed_methods: bool

  (* printing *)
  method toPretty : pretty_t
  method get_alternate_text : string

end

(* ================ ClassInfo ============================================== *)

type class_info_type_t =
| ConcreteClass of java_class_or_interface_int
| InterfaceType of java_class_or_interface_int
| AbstractClass of java_class_or_interface_int
| StubbedClass of class_summary_int
| MissingClass of class_name_int


class type class_info_int =
object
  (* setters *)
  method add_creator           : class_method_signature_int -> unit
  method add_subclass          : class_name_int -> unit
  method add_implementing_class: class_name_int -> unit
  method set_dispatch          : unit

  (* accessors *)
  method get_index                 : int
  method get_class                 : class_info_type_t
  method get_class_name            : class_name_int
  method get_super_class           : class_name_int
  method get_interfaces            : class_name_int list
  method get_generic_signature     : class_signature_int
  method get_method                : method_signature_int -> method_int
  method get_methods_defined       : method_signature_int list
  method get_native_methods_defined: method_signature_int list
  method get_field                 : field_signature_int -> field_int
  method get_field_signature       : string -> field_signature_int
  method get_fields_defined        : field_signature_int list
  method get_creators              : class_method_signature_int list
  method get_wrapped_primitive_type: java_basic_type_t
  method get_source_origin         : string
  method get_md5_digest            : string
  method get_bootstrap_methods     : bootstrap_method_int list
  method get_bootstrap_method      : int -> bootstrap_method_int
  method get_lambda_function       : int -> (object_type_t * method_signature_int)
       
  method get_instruction_count     : int
  method get_field_count           : int
  method get_scalar_object_size    : int   (* does not include objects created in constructors *)

  method get_subclasses             : class_name_int list
  method get_implementing_classes   : class_name_int list
  method get_default_implementations: class_name_int list
  method get_interface_default_methods: method_signature_int list

  method get_length_accessor: property_accessor_t
    
  method get_version: string

  (* predicates *)
  method is_interface         : bool
  method is_missing           : bool
  method is_stubbed           : bool
  method has_super_class      : bool
  method has_super_interfaces : bool
  method has_generic_signature: bool
  method has_md5_digest       : bool
  method is_final             : bool
  method is_abstract          : bool
  method is_immutable         : bool
  method is_dispatch          : bool
  method is_collection_class  : bool
  method is_map_class         : bool
  method is_wrapper_class     : bool
  method has_method           : method_signature_int -> bool
  method defines_method       : method_signature_int -> bool
  method defines_field        : field_signature_int -> bool
  method implements_interface : class_name_int -> bool
  method returns_lambda_function: int -> bool

  method has_length: bool
    
  method has_version: bool

  (* printing *)
  method toPretty : pretty_t
end

(* ============== FunctionSummary ========================================== *)

type loop_info_t = {
  li_first_pc      : int ;
  li_entry_pc      : int ;
  li_last_pc       : int ;
  li_instr_count   : int ;           (* number of instructions in the loop *)
  li_cond_pcs      : int list;       (* pc's of conditionals that dominate loop exit *)
  li_inner_loops   : (int * int) list ;
  li_outer_loops   : (int * int) list ;
  li_max_iterations: jterm_t list ;
  li_pc_invariants : (int * relational_expr_t list) list (* pc, invariant list *) ;
  li_calls         : (int * int * int) list (* cn-ix, ms-ix, pc *)
}

type method_loop_infos_t = class_method_signature_int * loop_info_t list

type bc_basicvalue_t =
  | BcvArg of int
  | BcvIntConst of numerical_t
  | BcvLongConst of numerical_t
  | BcvByteConst of numerical_t
  | BcvShortConst of numerical_t
  | BcvDoubleConst of float
  | BcvFloatConst of float
  | BcvArrayElement of java_basic_type_t * bc_objectvalue_t * bc_basicvalue_t
  | BcvThisField of class_name_int * field_signature_int
  | BcvThatField of class_name_int * field_signature_int * bc_objectvalue_t
  | BcvStaticField of class_name_int * field_signature_int
  | BcvArrayLength of bc_objectvalue_t
  | BcvInstanceOf of object_type_t * bc_objectvalue_t
  | BcvBinOpResult of opcode_t * bc_basicvalue_t * bc_basicvalue_t
  | BcvUnOpResult of opcode_t * bc_basicvalue_t
  | BcvQResult of opcode_t list * bc_value_t list * bc_basicvalue_t * bc_basicvalue_t  
  | BcvConvert of opcode_t * bc_basicvalue_t
  | BcvCallRv of bc_call_t

and bc_objectvalue_t =
  | BcoArg of int
  | BcoNull
  | BcoClassConst of object_type_t
  | BcoStringConst of string
  | BcoNewObject of class_name_int * bc_value_t list
  | BcoNewArray of value_type_t * bc_basicvalue_t
  | BcoMultiNewArray of object_type_t * bc_basicvalue_t list
  | BcoArrayElement of java_basic_type_t * bc_objectvalue_t * bc_basicvalue_t 
  | BcoThisField of class_name_int * field_signature_int
  | BcoThatField of class_name_int * field_signature_int * bc_objectvalue_t
  | BcoStaticField of class_name_int * field_signature_int
  | BcoCheckCast of object_type_t * bc_objectvalue_t
  | BcoQResult of opcode_t list * bc_value_t list * bc_objectvalue_t * bc_objectvalue_t  
  | BcoCallRv of bc_call_t

and bc_value_t =
  | BcBasic of bc_basicvalue_t
  | BcObject of bc_objectvalue_t
             
and bc_call_t = {
    bcp_type: string ;              (* virtual, private, interface, static *)
    bcp_base_object: bc_objectvalue_t option ;
    bcp_base_type: object_type_t ;
    bcp_ms: method_signature_int ;
    bcp_args: bc_value_t list
  }

type bc_action_t =
  | BcNop
  | BcNopX
  | BcInitObject
  | BcInitSuper
  | BcNewObject of class_name_int * bc_value_t list
  | BcDropValues of bc_value_t list
  | BcPutThisField of class_name_int * field_signature_int * bc_value_t
  | BcPutThatField of class_name_int * field_signature_int * bc_objectvalue_t * bc_value_t
  | BcPutStaticField of class_name_int * field_signature_int * bc_value_t
  | BcArrayStore of java_basic_type_t * bc_objectvalue_t * bc_basicvalue_t * bc_value_t
  | BcConditionalAction of opcode_t list * bc_value_t list * bc_action_t list * bc_action_t list
  | BcWrapCall of bc_call_t
  | BcThrow of bc_objectvalue_t

type bc_action_value_t =
  | BcaValue of bc_value_t
  | BcaAction of bc_action_t
  | BcaActions of bc_action_t list
  | BcaTest of opcode_t list * bc_value_t list
  | BcaRetGoto of opcode_t
  | BcaOpcodes of opcode_t list
  | BcaRvActions of bc_action_t list * bc_value_t

type bc_pattern_t =
  | BcpNop    (* no result, no side effects *)
  | BcpNopX   (* no result, no side effects, but may throw exception *)
  | BcpAction of bc_action_t list
  | BcpResult of bc_action_t list * bc_value_t
  | BcpThrow of bc_action_t list * bc_objectvalue_t
  | BcpResultExcept of class_name_int * bc_action_t list * bc_value_t * bc_value_t
  | BcpResultExceptThrow of class_name_int * bc_action_t list * bc_value_t * bc_objectvalue_t
  | BcpActionExcept of class_name_int * bc_action_t list
  | BcpActionExceptThrow of class_name_int * bc_action_t list * bc_objectvalue_t
  | BcpInfiniteLoop of bc_action_t list
  | BcpIllegalSeq of string * opcode_t list
  
type precondition_predicate_t =
| PreRelationalExpr of relational_expr_t
| PreNull of jterm_t
| PreNotNull of jterm_t
| PreValidString of jterm_t * string

type postcondition_predicate_t =
| PostRelationalExpr of relational_expr_t
| PostTrue                                                  (* return value is true *)
| PostFalse                                                (* return value is false *)
| PostNewObject of class_name_int
| PostNull                                                  (* return value is null *)
| PostNotNull                                           (* return value is not null *)
| PostElement of jterm_t
| PostEmptyCollection
| PostSameCollection of jterm_t
| PostWrapped of jterm_t
| PostUnwrapped 
| PostValidString of string
| PostObjectClass of class_name_int         (* return value is an instance of class *)

class type postcondition_int =
object
  (* accessors *)
  method get_name: string
  method get_predicate: postcondition_predicate_t

  (* predicates *)
  method is_error: bool

  (* converters *)
  method write_xml: xml_element_int -> method_signature_int -> unit

  (* printing *)
  method toPretty: pretty_t
end

type sideeffect_t =
| NumericJoin of jterm_t * jterm_t * jterm_t
| NumericAbstract of jterm_t
| SetValue of jterm_t
| Wrap of jterm_t * jterm_t
| ConditionalSideEffect of precondition_predicate_t * sideeffect_t

type taint_element_t =
  | TTransfer of jterm_t * jterm_t
  | TRefEqual of jterm_t * jterm_t
  | TDefPut of jterm_t
  | TRemove of jterm_t
    
class type taint_int =
object ('a)
  (* setters *)
  method add_taint  : 'a -> unit
  method add_element: taint_element_t -> unit

  (* accessors *)
  method get_elements: taint_element_t list

  (* xml *)
  method write_xml: xml_element_int -> method_signature_int -> unit

  (* printing *)
  method toPretty: pretty_t
end

class type string_sink_int =
object
  method get_arg : int
  method get_form: string
  method get_dest: string
  method write_xml : xml_element_int -> method_signature_int -> unit
  method toPretty: pretty_t
end

type resource_type_t = 	RMemory | RWaitingTime | RThreads | RFileSize

class type resource_sink_int =
object
  method get_arg : int
  method get_type: resource_type_t
  method write_xml : xml_element_int -> method_signature_int -> unit
  method toPretty: pretty_t
end
	
class type exception_info_int =
object
  (* accessors *)
  method get_exception       : class_name_int
  method get_safety_condition: precondition_predicate_t list
  method get_error_condition : precondition_predicate_t list
  method get_description     : string
    
  (* predicates *)
  method has_safety_condition: bool
  method has_error_condition : bool
  method has_description     : bool
    
  (* xml *)
  method write_xml           : xml_element_int -> method_signature_int -> unit
    
  (* printing *)
  method toPretty            : pretty_t
end

class type function_summary_int =
object
  (* accessors *)
  method get_cms                   : class_method_signature_int
  method get_method_signature      : method_signature_int
  method get_post                  : postcondition_int list
  method get_error_post            : postcondition_int list
  method get_sideeffects           : sideeffect_t list
  method get_exceptions            : class_name_int list
  method get_exception_infos       : exception_info_int list
  method get_visibility            : access_t
  method get_taint                 : taint_int
  method get_taint_elements        : taint_element_t list
  method get_defining_method       : class_method_signature_int
  method get_string_sinks          : string_sink_int list
  method get_string_sink           : int -> string_sink_int
  method get_resource_sinks        : resource_sink_int list
  method get_resource_sink         : int -> resource_sink_int
  method get_virtual_calls         : class_method_signature_int list
  method get_interface_calls       : class_method_signature_int list
  method get_time_cost             : jterm_range_int
  (* default values for arguments, from_model *)
  method get_space_cost            : jterm_range_int
  method get_pattern               : bc_action_t

  (* predicates *)
  method is_abstract        : bool
  method is_final           : bool
  method is_static          : bool
  method is_bridge          : bool
  method is_inherited       : bool
  method is_valid           : bool
  method is_default         : bool
  method has_defining_method: bool
  method has_string_sink    : int -> bool
  method has_resource_sink  : int -> bool    (* resource quantity sink *)
  method has_pattern        : bool

  (* xml *)
  method write_xml_summary: xml_element_int -> unit
  method write_xml        : xml_element_int -> unit

  (* printing *)
  method toPretty  : pretty_t
end


(* ============== MethodInfo =============================================== *)

type analysis_type_t = TypeAnalysis | TaintAnalysis | NumericAnalysis

type method_info_type_t =
| ConcreteMethod of method_int
| UntranslatedConcreteMethod of method_int
| Stub of function_summary_int
| NativeMethod of method_int
| AbstractMethod of method_int
| InterfaceInheritedMethod of class_method_signature_int
| MissingMethod of class_method_signature_int
| ExcludedMethod of method_int * string


(* represents the handler code that is associated with a catch block or a
   finally block (one object for each handler block).

   Upon initial creation of the method an instance of exception_handlers_int
   is created but no handler_block_int instances are created yet. 

   To create handler_block_int objects call JCHExceptionTable.set_handler_blocks ();
   this will compute the extent of each catch/finally block by performing a
   reachability analysis
*)
class type handler_block_int =
object
  (* accessors *)
  method get_start_pc     : int    (* returns the first instruction of this handler block *)
  method get_end_pc       : int    (* returns the last instruction of this handler block 
                                      Note: this is the highest pc in the handler block,
                                      but not necessarily the last instruction to be
                                      executed, or it may not be executed at all if
                                      the catch/finally block has multiple exits, or
                                      other complex control flow  *)
  method get_pcs          : int list    (* returns the list of pc's that are included in the
					   catch/finally block *)
  method get_handled_type : class_name_int  (* returns the class name of the exception caught by
                                             this handler; throws an exception if this is a
                                             finally block *)
  method get_basic_blocks : (int * int) list   (* returns a list (begin,end) pc's for the
						  basic blocks included in this handler *)

  (* predicates *)
  method has_handled_type : bool  (* returns true if this is a catch block *)
  method is_finally_block : bool  (* returns true if this is a finally block *)
  method is_empty         : bool  (* returns true if this block has no instructions beyond
				     saving the exception, and potentially a goto instruction *)
  method has_return_instruction: bool  (* returns true if the block includes a return instruction *)
  method has_throw_instruction : bool  (* returns true if the block includes a throw instruction *)

  (* printing *)
  method code_to_pretty: pretty_t
  method toPretty      : pretty_t
end

(* convenenience object that manages creation and access of the handler blocks
   of a method. There is one of these objects for each method. 

   To create handler_block_int objects call JCHExceptionTable.set_handler_blocks ();
   this will compute the extent of each catch/finally block by performing a
   reachability analysis
*)
class type exception_handlers_int =
object
  (* setters *)
  (* set_handler_block (handler_pc, block, basic_blockcs)
		 creates a handler_block_int object for the handler at pc = handler_pc*)
  method set_handler_block  : int -> (int * opcode_t) list -> (int * int) list -> unit

  (* accessors *)
  (* returns the handler_block_int object at the given pc (requires the handler blocks to have
     been initialized *)
  method get_handler_block  : int -> handler_block_int
  (* returns a list of handler pc's of catch blocks that could catch an exception thrown by
     the given pc, in order of encounter; returns the empty list if the pc is not in a try
     block with associated catch blocks *)
  method get_exn_handlers   : int -> (int * class_name_int) list 
  (* returns the pc of the finally handler that would be executed if the instruction at the
     given pc throws an exception. Throws an exception if the given pc is not within a try
     block associated with a finally block. Call has_finally_handler to check if the pc is
     within a try block associated with a finally block *)
  method get_finally_handler: int -> int

  (* returns a list of all handler blocks in this method *)
  method get_handler_blocks      : handler_block_int list
  (* returns a list of all handler pc's that catch an exception, together with 
     exception caught *)
  method get_all_exn_handlers    : (int * class_name_int) list
  (* returns a list of handler pc's of finally blocks *)
  method get_all_finally_handlers: int list
  (* returns a list of all handler pc's (catch blocks and finally blocks combined *)
  method get_all_handler_pcs     : int list

  method get_exceptions_caught : class_name_int list

  (* predicates *)
  method has_finally_handler: int -> bool   (* returns true if the pc is in scope of a finally handler *)

  (* printing *)
  method code_to_pretty: pretty_t
  method toPretty      : pretty_t
end

class type method_info_int =
object ('a)

  (* setters *)
  method add_callee                : class_method_signature_int -> unit
  method add_caller                : class_method_signature_int -> unit
  method add_field_read            : class_field_signature_int -> unit
  method add_field_write           : class_field_signature_int -> unit

  method set_translation_failure   : unit
  method set_num_variables         : int -> unit

  method set_called_by_reflection  : unit
  method set_dynamically_dispatched: unit
  method set_indirectly_called     : unit
  method set_main_method           : unit
  method set_analysis_exclusions   : analysis_type_t list -> unit
  method add_argument_assumption   : relational_expr_t -> unit
  method set_saved_method_stack_layout: bcdictionary_int -> xml_element_int -> unit
    
  (* accessors *)
  method get_index                 : int
  method get_class_name            : class_name_int
  method get_method_name           : string
  method get_argument_assumptions  : relational_expr_t list
  method get_class_method_signature: class_method_signature_int
  method get_generic_signature     : method_type_signature_int
  method get_procname              : symbol_t
  method get_implementation        : method_info_type_t
  method get_bytecode              : bytecode_int
  method get_opcode                : int -> opcode_t (* opcode at given pc (offset) in bytecode *)
  method get_pc_to_instr_index     : int -> int      (* converter from pc to instr index *)
  method get_method                : method_int
  method get_callees               : class_method_signature_int list  (* called by this method *)
  method get_callers               : class_method_signature_int list  (* those that call this method *)
  method get_field_writes          : class_field_signature_int list
  method get_field_reads           : class_field_signature_int list
  method get_visibility            : access_t
  method get_exception_handlers    : exception_handlers_int  (* convenenience object to create
								and access handler blocks *)
  method get_exception_table       : exception_handler_int list (* exception table that is
								 included in the bytecode *)
  method get_exceptions_caught     : class_name_int list
  method get_try_blocks_pcs        : int -> int list   (* list of pc's that are covered by given handler *)
  method get_exceptions            : class_name_int list (* checked exceptions *)
  method get_line_number           : int -> int   (* get source line number for given pc *)
  method get_line_number_table     : (int * int) list
  method get_local_variable_table  : (int * int * string * value_type_t * int) list
  method get_local_variable_name   : int -> int -> string    (* variable index, pc *)
  method get_local_variable_type_table  : (int * int * string * field_type_signature_int * int) list
  method get_local_variable_type   : int -> int -> value_type_t    (* register, pc *)
  method get_register_variable     : int -> value_type_t -> variable_t
  method get_varname_mapping       : int -> (int -> string)    (* pc *)
  method get_argname_mapping       : (int -> string)
  method get_method_stack_layout   : method_stack_layout_int

  method get_previous_bytecode_offset : int -> int
  method get_next_bytecode_offset     : int -> int

  method get_byte_count             : int
  method get_instruction_count      : int
  method get_variable_count         : int
  method get_call_instruction_count : int
  method get_stack_instruction_count: int
  method get_controlflow_instruction_count: int
  method get_arithmetic_instruction_count : int

  method get_virtual_calls         : class_method_signature_int list
  method get_interface_calls       : class_method_signature_int list

  method get_analysis_exclusions   : analysis_type_t list

  (* iterators *)
  method bytecode_iteri       : (int -> opcode_t -> unit) -> unit

  (* predicates *)
  method equal                : 'a -> bool
  method compare              : 'a -> int

  method is_missing           : bool
  method is_stubbed           : bool
  method is_abstract          : bool
  method is_native            : bool
  method is_final             : bool
  method is_static            : bool
  method is_bridge            : bool
  method is_synchronized      : bool

  method failed_to_translate  : bool

  method is_private           : bool
  method is_protected         : bool
  method is_default_access    : bool
  method is_public            : bool

  method has_bytecode         : bool
  method has_jsr_instructions : bool
  method has_handlers         : bool
  method is_constructor       : bool
  method is_class_constructor : bool

  method has_virtual_calls    : bool

  method is_excluded             : bool

  method has_argument_assumptions: bool
  method has_generic_signature   : bool
  method has_line_number         : int -> bool
  method is_handler_pc           : int -> bool
  method has_line_number_table   : bool
  method has_local_variable_table: bool 
  method has_local_variable_type_table: bool 
  method has_local_variable_type : int -> int -> bool
  method has_local_variable_name : int -> int -> bool
  method has_method_stack_layout : bool
  method has_method_stack_layout_loaded: bool

  method has_previous_bytecode_offset : int -> bool
  method has_next_bytecode_offset     : int -> bool

  method has_num_variables : bool

  method is_dynamically_dispatched: bool
  method is_called_by_reflection  : bool
  method is_indirectly_called     : bool    (* called from within a summarized method *)
  method is_main_method           : bool

  method need_not_be_analyzed     : bool

  (* printing *)
  method get_name            : string
  method get_signature_string: string
  method toPretty            : pretty_t
  method bytecode_to_pretty  : pretty_t

end

(* ============= CFG basic block =========================================== *)

class type bc_block_int =
object
  (* accessors *)
  method get_firstpc: int
  method get_lastpc : int
  method get_successors: int list
  method get_cost   : int             (* STAC increment to cost variable *)

  (* iterators *)
  method iter: (int -> opcode_t -> unit) -> unit
end

class type bc_graph_int =
object
  method getRootNode: symbol_t
  method getNextNodes: symbol_t -> symbol_t list
end

(* ============= FunctionSummaryLibrary ==================================== *)

class type function_summary_library_int =
object
  (* setters *)
  method add_class_summary:
           ((class_name_int * class_summary_int) * 
	      (class_field_signature_int * field_stub_int) list *
		(class_method_signature_int * loop_info_t list * function_summary_int) list) -> unit
  method exclude_class      : string -> unit

  (* accessors *)
  method get_method_summary : ?anysummary:bool -> class_method_signature_int -> function_summary_int
  method get_field_summary  : class_field_signature_int -> field_stub_int
  method get_class_summary  : class_name_int -> class_summary_int

  method get_final_summaries: class_name_int -> class_method_signature_int list
  method get_invalid_methods: class_method_signature_int list

  (* iterators *)
  method iter: (function_summary_int -> unit) -> unit

  (* predicates *)
  method has_method_summary : ?anysummary:bool -> class_method_signature_int -> bool
  method has_field_summary  : class_field_signature_int -> bool
  method has_class_summary  : class_name_int -> bool

  (* info *)
  method size : int

  (* printing *)
  method statistics_to_pretty: pretty_t
  method toPretty: pretty_t

end

(* ============ User Data ================================================== *)


class type userdata_int =
object
  (* setters *)
  method register_constants  : xml_element_int -> unit
  method add_default_costdata: xml_element_int -> unit
  method add_class_data      : xml_element_int -> unit
  method add_userdata        : xml_element_int -> unit

  (* accessors *)
  method get_loopbound       : int -> int -> jterm_range_int
  method get_method_sidechannelchecks: int -> (int * int) list
  method get_instructioncost : int -> int -> jterm_range_int
  method get_blockcost       : int -> int -> jterm_range_int
  method get_methodcost      : int -> jterm_range_int
  method get_run_method      : int -> int -> class_method_signature_int
  method get_callees         : int -> int -> class_method_signature_int list
  method get_nopreplacements : int -> int list
  method get_sidechannelchecks : (int * (int * int) list) list
  method get_edge            : (int * int) -> class_name_int

  (* predicates *)
  method has_loopbound      : int -> int -> bool
  method has_instructioncost: int -> int -> bool
  method has_blockcost      : int -> int -> bool
  method has_methodcost     : int -> bool
  method has_run_method     : int -> int -> bool
  method has_edge           : (int * int) -> bool

  (* printing *)
  method toPretty: pretty_t

end

(* ============= Cost results ============================================== *)

class type costresults_int =
object
  (* setters *)
  method add_class_results : xml_element_int -> unit

  (* accessors *)
  method get_cost_string   : int -> int -> string

end


(* ============= Results =================================================== *)

type pc_converter_t = int -> int

(* ============ InstructionInfo ============================================ *)

class type method_target_int = 
object ('a)
  method clone                 : 'a

  (* setters *)
  method add_target            : method_info_int -> unit
  method add_indirect_target   : method_info_int -> unit
  method assert_invocation_objects: class_name_int list -> unit

  (* accessors *)
  method get_all_targets       : method_info_int list  (* all regular targets, no indirect targets *)
  method get_valid_targets     : method_info_int list  (* only concrete and stubbed targets *) 
  method get_indirect_targets  : method_info_int list
  method get_stubs             : function_summary_int list
  method get_procs             : symbol_t list
  method get_reason_for_top    : pretty_t
    
  (* predicates *)
  method is_top                : bool

  (* xml *)
  method write_xml             : xml_element_int -> unit

  (* printing *)
  method toPretty             : pretty_t
end


class type instruction_info_int =
object ('a)
  method compare                 : 'a -> int

  (* setters *)
  method set_field_target        : field_info_int -> unit
  method add_method_target       : method_info_int -> unit
  method add_indirect_method_target: method_info_int -> unit
  method assert_invocation_objects: class_name_int list -> unit

  (* accessors *)
  method get_location            : bytecode_location_int
  method get_opcode              : opcode_t
  method get_method_target       : ?restrict_to:class_name_int list -> unit -> method_target_int
  method get_field_target        : field_info_int
  method get_declared_object_type: object_type_t option
  method get_actual_object_types : object_type_t list

  (* predicates *)
  method is_modified             : bool
  method has_method_target       : bool
  method has_field_target        : bool
  method has_declared_object_type: bool

  method is_method_call          : bool
  method is_method_call_static   : bool  
  method is_method_call_special  : bool
  method is_method_call_virtual  : bool
  method is_method_call_interface: bool
  
  method is_field_access: bool
  method is_field_write : bool
  method is_field_read  : bool
  method is_field_get_static: bool
  method is_field_get_field : bool
  method is_field_put_static: bool
  method is_field_put_field : bool

  method may_throw_invocation_exceptions: bool

  (* printing *)
  method toPretty : pretty_t
  method toString : string
end

(* ============= Relational expressions ==================================== *)

class type relational_invariant_int =
object ('a)
  method compare  : 'a -> int
  method index    : int
  method get_expr : relational_expr_t
  method write_xml: xml_element_int -> unit
  method toPretty : pretty_t
end

(* ============= Taint Analysis ============================================ *)

type  taint_origin_type_t =
  | T_ORIG_VAR of int * variable_t    (* cmsix, variable *)
  | T_ORIG_FIELD of int * string * int * int  (* cfsix, info-string, cmsix, pc *)
  | T_ORIG_CALL of int * string * int * int (* callee-cmsix, info-string, caller-cmsix, pc *)
  | T_ORIG_TOP_TARGET of method_target_int * int * int (* target, caller-cmsix, pc  *)
  | T_ORIG_STUB of int * int * int (* target-cmsix, caller-cmsix, pc *)

type tainted_variable_data_t = {
    tvar: variable_t ;
    untrusted: taint_origin_type_t list 
(*    unknown: taint_origin_type_t list*)
  }

type taint_node_type_t =
  | TN_FIELD of int (* cfsix *)
  (* Only the static fields have a node associated with them. The taint of 
     non-static field info is incorporated in the taint of the object *)
  | TN_VAR of (int * variable_t * int)      (* cmsix * var * pc_in_scope *)
  | TN_VAR_EQ of (int * variable_t * variable_t * symbol_t list)
  (* x = y from if conditions on switch tables and the states where this holds *)
  | TN_CALL of (int * int * int * int * variable_t option * variable_t list)
  (* call-index * pc * caller * target * return * args *) 
  | TN_UNKNOWN_CALL of (int * int * int * variable_t option * variable_t list)
(* call-index * pc * caller * target * return * args *)
  | TN_CONDITIONAL of int * int (* cmsix, pc of conditional *)
  | TN_OBJECT_FIELD of int * variable_t * int * int (* cmsix, variable, cfsix, pc *)
  | TN_SIZE of int * variable_t * int (* cmsix, variable whose size is affected, pc *)
  | TN_REF_EQUAL

class type taint_dictionary_int =
  object

    method index_string: string -> int
    method index_symbol: symbol_t -> int
    method index_symbol_list: symbol_t list -> int
    method index_variable: variable_t -> int
    method index_variable_list: variable_t list -> int
    method index_method_target: method_target_int -> int
    method index_taint_origin: taint_origin_type_t -> int
    method index_taint_origin_list: taint_origin_type_t list -> int
    method index_tainted_variable: tainted_variable_data_t -> int
    method index_tainted_variable_ids: int list -> int
    method index_taint_node_type: taint_node_type_t -> int

    method get_string: int -> string
    method get_symbol: int -> symbol_t
    method get_symbol_list: int -> symbol_t list
    method get_variable: int -> variable_t
    method get_variable_list: int -> variable_t list
    method get_method_target: int -> method_target_int
    method get_taint_origin: int -> taint_origin_type_t
    method get_taint_origin_list: int -> taint_origin_type_t list
    method get_tainted_variable: int -> tainted_variable_data_t
    method get_tainted_variable_ids: int -> int list
    method get_taint_node_type: int -> taint_node_type_t

    method write_xml_string: ?tag:string -> xml_element_int -> string -> unit
    method read_xml_string : ?tag:string -> xml_element_int -> string
    method write_xml_symbol: ?tag:string -> xml_element_int -> symbol_t -> unit
    method read_xml_symbol : ?tag:string -> xml_element_int -> symbol_t
    method write_xml_variable: ?tag:string -> xml_element_int -> variable_t -> unit
    method read_xml_variable : ?tag:string -> xml_element_int -> variable_t
    method write_xml_method_target: ?tag:string -> xml_element_int -> method_target_int -> unit
    method read_xml_method_target : ?tag:string -> xml_element_int -> method_target_int
    method write_xml_taint_origin: ?tag:string -> xml_element_int -> taint_origin_type_t -> unit
    method read_xml_taint_origin : ?tag:string -> xml_element_int -> taint_origin_type_t
    method write_xml_taint_origin_list:
             ?tag:string -> xml_element_int -> taint_origin_type_t list -> unit
    method read_xml_taint_origin_list:
             ?tag:string -> xml_element_int -> taint_origin_type_t list
    method write_xml_tainted_variable:
             ?tag:string -> xml_element_int -> tainted_variable_data_t -> unit
    method read_xml_tainted_variable:
             ?tag:string -> xml_element_int -> tainted_variable_data_t
    method write_xml_tainted_variable_ids: ?tag:string -> xml_element_int -> int list -> unit
    method read_xml_tainted_variable_ids : ?tag:string -> xml_element_int -> int list

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

    method toPretty: pretty_t

  end

class type taint_origin_int =
object ('a)
  method compare   : 'a -> int

  (* accessors *)
  method get_index : int
  method get_origin: taint_origin_type_t

  (* predicates *)
  method is_var_origin  : bool
  method is_field_origin: bool
  method is_call_origin : bool
  method is_top_origin  : bool
  method is_stub_origin : bool

  (* xml *)
  method write_xml : xml_element_int -> unit

  (* printing *)
  method toPretty  : pretty_t
end

class type taint_origin_set_int =
object ('a)
  method compare    : 'a -> int

  (* accessors *)
  method get_index  : int
  method get_origins: taint_origin_type_t list
  method get_indices: int list

  (* predicates *)
  method has_origin : taint_origin_int -> bool
  method has_origin_index : int -> bool
  method is_empty   : bool

  (* xml *)
  method write_xml  : xml_element_int -> unit

  (* printing *)
  method toPretty   : pretty_t
  method to_short_pretty: pretty_t
  method to_pretty_inds: pretty_t
end


class type taint_node_int =
  object ('a)
    method add_all_field_untrusted_origins : taint_origin_set_int IntCollections.table_t -> bool
    method add_all_untrusted_origins : 'a -> bool
    method add_field_untrusted_origins : int -> taint_origin_set_int -> bool
    method add_size_untrusted_origins : taint_origin_set_int -> bool
    method add_untrusted_origins : taint_origin_set_int -> bool
    method compare : 'a -> int 
    method get_call_vars : CHLanguage.variable_t list
    method get_call_pc : int
    method get_field_inds : int list
    method get_field_untrusted_origins : int -> taint_origin_set_int
    method get_index : int
    method get_node_type : taint_node_type_t
    method get_size_untrusted_origins : taint_origin_set_int
    method get_stub_untrusted : CHLanguage.symbol_t option
    method get_untrusted_origins : taint_origin_set_int
    method get_var : CHLanguage.variable_t
    method is_bool_var : bool
    method is_call : bool
    method is_unknown_call : bool
    method is_conditional : bool
    method is_const_var : bool
    method is_field : bool
    method is_immutable : bool 
    method is_immutable_var : bool
    method is_loop_counter_var : bool
    method is_obj_field : bool
    method is_var : bool
    method is_ref_equal : bool
    method is_size : bool
    method propagate_taint : 'a -> bool
    method set_field_untrusted_origins : int -> taint_origin_set_int -> unit
    method set_size_untrusted_origins : taint_origin_set_int -> unit
    method set_stub_untrusted : CHLanguage.symbol_t -> unit
    method set_untrusted_origins : taint_origin_set_int -> unit
    method to_pretty_no_taint : CHPretty.pretty_t
    method toPretty : CHPretty.pretty_t
    method write_xml: CHXmlDocument.xml_element_int -> unit
  end


(* ============ Application ================================================ *)

class type application_int =
object

  method reset             : unit

  (* setters *)
  method add_application_jar: string -> unit
  method add_class         : java_class_or_interface_int -> unit
  method replace_class     : java_class_or_interface_int -> unit
  method add_missing_class : class_name_int -> unit
  method add_class_stub    : class_info_int -> unit

  method add_method        : method_int -> unit
  method add_method_link   : class_method_signature_int -> class_method_signature_int -> unit
  method add_missing_method: class_method_signature_int -> unit
  method add_interface_inherited_method: class_method_signature_int -> unit
  method add_stub          : function_summary_int -> unit

  method add_field         : field_int -> unit
  method add_field_link    : class_field_signature_int -> class_field_signature_int -> unit
  method add_missing_field : class_field_signature_int -> unit
  method add_field_stub    : field_stub_int -> unit

  method add_instruction   : instruction_info_int -> unit

  (* accessors *)
  method get_application_jars: string list
  method get_class         : class_name_int -> class_info_int
  method get_method        : class_method_signature_int -> method_info_int
  method get_field         : class_field_signature_int -> field_info_int
  method get_instruction   : bytecode_location_int -> instruction_info_int

  method get_method_by_index: int -> method_info_int

  method get_packages       : string list
  method get_classes        : class_info_int list
  method get_methods        : method_info_int list
  method get_stubbed_methods: method_info_int list
  method get_fields         : field_info_int list
  method get_instructions   : instruction_info_int list

  method get_application_classes: class_info_int list

  method get_implementing_classes: class_name_int -> class_info_int list
  method get_all_interfaces      : class_name_int -> class_name_int list
  method get_ancestors           : class_name_int -> class_name_int list
  method get_subclasses          : class_name_int -> class_name_int list

  method get_inherited_methods: class_method_signature_int list

  method get_derived_classes: class_name_int -> class_name_int list

  method get_num_classes  : int
  method get_num_methods  : int

  (* iterators *)
  method iter_classes   : (class_info_int -> unit) -> unit
  method iter_methods   : (method_info_int -> unit) -> unit
    
  (* predicates *)
  method has_class      : class_name_int -> bool
  method has_method     : class_method_signature_int -> bool
  method has_field      : class_field_signature_int -> bool
  method has_instruction: bytecode_location_int -> bool

  method is_interface     : class_name_int -> bool
  method is_abstract_class: class_name_int -> bool
  method is_descendant    : class_name_int -> class_name_int -> bool (* is c1 a descendant of c2 *)
  method implements_interface: class_info_int-> class_name_int -> bool 

  method is_application_class : class_name_int -> bool
  method is_application_method: class_method_signature_int -> bool

  method is_inherited : class_method_signature_int -> bool

  method write_xml_missing_classes: xml_element_int -> unit

end

(* ============ Callgraph ================================================== *)

type ms_implementers_t = {
  mscn_classes : int list ;
  mscn_stubs   : int list ;
  mscn_native  : int list
}

type non_virtual_target_type_t =
| PrivateMethod
| StaticMethod
| FinalClass
| FinalMethod
| LocalAnalysis


type call_targets_t =
  | NonVirtualTarget of non_virtual_target_type_t * int         (* cnix *)
  | ConstrainedVirtualTargets of string * int list              (* cnix list *)
  | VirtualTargets of int list                                  (* cnix list *)
  | EmptyTarget of bool * class_name_int * method_signature_int
                 
class type method_signature_implementations_int =
object

  method register_signature           : method_signature_int -> unit
  method initialize                   : unit
  method get_ms_index                 : string -> string -> int
  method get_implementations          : method_signature_int -> class_name_int list
  method get_interface_implementations: 
    class_name_int -> method_signature_int -> class_name_int list
  method write_xml                     : xml_element_int -> unit

end

class type cgdictionary_int =
  object
    method index_target: call_targets_t -> int
    method get_target: int -> call_targets_t
    method write_xml_target: ?tag:string -> xml_element_int -> call_targets_t -> unit
    method read_xml_target : ?tag:string -> xml_element_int -> call_targets_t
    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit
    method toPretty: pretty_t
  end

class type callgraph_base_int =
object
  method build_graph   : unit
  method get_callees   : int -> class_method_signature_int list    
  method get_pc_callees: int -> int -> class_method_signature_int list
  method bottomup_iter : (method_info_int -> unit) -> unit
  method read_xml      : xml_element_int -> unit
  method write_xml     : xml_element_int -> unit
end

(* ============ ClassSummaryTemplate ======================================= *)

class type method_summary_builder_int =
object

  (* setters *)
  method add_exception_info: exception_info_int -> unit
  method add_post          : postcondition_int -> unit
  method add_sideeffect    : sideeffect_t -> unit
  method add_string_sink   : string_sink_int -> unit
  method add_resource_sink : resource_sink_int -> unit
  method set_taint         : taint_int -> unit
  method set_valid         : unit

  (* converters *)
  method to_function_summary: function_summary_int

  (* xml *)
  method write_xml          : xml_element_int -> unit

  (* printing *)
  method toPretty           : pretty_t

end

(* ============ CHIFSystem ================================================= *)

class type chif_system_int =
object
  (* actions *)
  method new_system      : string -> unit
  method translate       : ?default_exn:bool -> string -> unit 
  method translate_method: string -> ?assert_types:bool -> method_info_int -> unit
  method create_method_stack_layout: method_info_int -> unit

  (* services *)
  method make_code : class_method_signature_int -> (code_int, cfg_int) command_t list -> code_t

  (* accessors *)
  method get_system           : string -> system_int
  method get_systems          : system_int list
  method get_system_names     : string list
  method get_procedure        : string -> symbol_t -> procedure_int
  method get_procedure_by_cms : string -> class_method_signature_int -> procedure_int
  method get_method_translation_failures : class_method_signature_int list
  method get_method_stack_layout: method_info_int -> method_stack_layout_int

  (* predicates *)
  method has_system           : string -> bool
  method has_procedure        : string -> symbol_t -> bool
  method has_procedure_by_cms : string -> class_method_signature_int -> bool
  method has_method_stack_layout: class_method_signature_int -> bool
  method has_method_translation_failed: class_method_signature_int -> bool

  (* printing *)
  method procedure_to_dot      : string -> symbol_t -> dot_graph_int option
  method procedure_to_pretty   : string -> symbol_t -> pretty_t
  method toPretty              : string -> pretty_t
  method stack_layout_to_pretty: method_info_int -> pretty_t
end


(* ============ Analysis Results =========================================== *)

class type method_invariants_int =
object
  method add_invariants: (int * relational_expr_t list) list -> unit
  method get_invariants: int -> relational_expr_t list
  method write_xml     : xml_element_int -> unit
  method read_xml      : xml_element_int -> unit
end
  
class type tainted_variable_int =
object ('a)
  method index         : int
  method compare       : 'a -> int
  method getvariable   : variable_t
  method gettaint      : taint_origin_type_t list
  method may_be_tainted: bool
  method write_xml     : xml_element_int -> unit
  method toPretty      : pretty_t
end

class type method_taints_int =
object
  method add_taints    : (int * (variable_t * taint_origin_set_int) list) list -> unit
  method get_taint     : int -> tainted_variable_int list
  method get_loopcounter_taint_level: int -> int
  method write_xml     : xml_element_int -> unit
  method read_xml      : xml_element_int -> unit
  method pc_to_pretty  : int -> pretty_t
end

(* Used to collect analysis results and save them to xml *)
class type class_analysis_results_int =
object

  (* setters *)
  method set_method_invariants: int -> (int * relational_expr_t list) list -> unit
  method set_method_taint_origins: 
    int -> (int * (variable_t * taint_origin_set_int) list) list -> unit
  method set_method_return_origins: int -> taint_origin_set_int option -> unit
  method set_method_loops     : int -> loop_info_t list -> unit

  (* xml *)
  method save_xml_class: unit

end

(* Used to support the GUI; analysis results are loaded on demand and cached *)
class type application_analysis_results_int =
object

  (* accessors *)
  method get_taints    : int -> method_taints_int
  method get_invariants: int -> method_invariants_int

  (* predicates *)
  method has_taints    : int -> bool
  method has_invariants: int -> bool

end

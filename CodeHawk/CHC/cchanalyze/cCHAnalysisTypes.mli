(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHNumericalConstraints
open CHOnlineCodeSet
open CHPretty
open CHStack

(* chutil *)
open CHNestedCommands

(* xprlib *)
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

(* cchpre *)
open CCHPreTypes


(* ======================================================= constraint sets === *)

class type constraint_set_int =
  object ('a)
    method add: numerical_constraint_t -> unit
    method get_constraints: numerical_constraint_t list
    method project_out: variable_t list -> 'a option
    method has: variable_t -> bool
    method toPretty: pretty_t
  end

(* ================================================================ commands === *)

type cmd_t = (code_t, cfg_t) command_t

type c_cmd_t = nested_cmd_t

(* =========================================================== c-environment === *)

class type c_environment_int =
object

  (** {1 Setters}*)

  method set_current_stmt_id : int -> unit
  method set_current_location: location -> unit

  (** {1 Accessors} *)

  method get_scope: scope_int
  method get_current_stmt_id: int
  method get_current_stmt_id_label: symbol_t
  method get_current_location: location
  method get_fdecls: cfundeclarations_int
  method get_varinfo: int -> varinfo
  method get_functionname: string
  method get_xpr_dictionary: xprdictionary_int
  method get_variable_manager: variable_manager_int
  method get_p_entry_sym: symbol_t

  (** {1 Services} *)

  (** {2 Create variables} *)

  method mk_program_var: varinfo -> offset -> variable_type_t -> variable_t
  method mk_return_var: typ -> variable_type_t -> variable_t
  method mk_symbolic_value_var: xpr_t -> typ -> variable_type_t -> variable_t
  method mk_base_variable: xpr_t -> offset -> typ -> variable_type_t -> variable_t
  method mk_check_variable:
           (bool * int * int) list -> typ -> variable_type_t -> variable_t
  method mk_augmentation_variable:
           string -> string -> int -> variable_type_t -> variable_t
  method mk_memory_variable: int -> offset -> variable_type_t -> variable_t
  method mk_stack_memory_variable:
           varinfo -> offset -> typ -> variable_type_t -> variable_t
  method mk_global_memory_variable:
           varinfo -> offset -> typ -> variable_type_t -> variable_t
  method mk_formal_ptr_base_variable: varinfo -> variable_type_t -> variable_t
  method mk_call_var: string -> int -> variable_t
  method mk_call_vars: variable_t

  method mk_base_address_value: variable_t -> offset -> typ -> variable_t
  method mk_global_address_value: varinfo -> offset -> typ -> variable_t
  method mk_stack_address_value: varinfo -> offset -> typ -> variable_t
  method mk_memory_address_value: int -> offset -> variable_t
  method mk_string_address: string -> offset -> typ -> variable_t

  method mk_function_return_value:
           location
           -> program_context_int
           -> varinfo
           -> xpr_t option list
           -> variable_t

  method mk_exp_return_value:
           location
           -> program_context_int
           -> xpr_t
           -> xpr_t option list
           -> typ
           -> variable_t

  method mk_function_sideeffect_value:
           location
           -> program_context_int
           -> varinfo
           -> xpr_t option list
           -> int
           -> typ
           -> variable_t

  method mk_tainted_value:
           variable_t -> xpr_t option -> xpr_t option -> typ -> variable_t

  method mk_byte_sequence: variable_t -> xpr_t option -> variable_t

  method mk_num_temp: variable_t
  method mk_sym_temp: variable_t
  method mk_temp: variable_type_t -> variable_t
  method mk_num_constant: numerical_t -> variable_t

  method mk_par_deref_init:
           varinfo
           -> offset
           -> typ
           -> variable_type_t
           -> (variable_t * variable_t * variable_t * variable_t)

  method mk_struct_par_deref:
           varinfo
           -> typ
           -> int
           -> variable_type_t
           -> (variable_t * variable_t) list

  method add_return_context: program_context_int -> unit

  method register_formals:
           varinfo list
           -> variable_type_t
           -> (string * typ * variable_t * variable_t) list

  method register_globals:
           varinfo list
           -> variable_type_t
           -> (string * typ * variable_t * variable_t) list

  method register_program_locals: varinfo list -> variable_type_t -> unit
  method register_function_return: typ -> variable_type_t -> unit

  (** {2 Retrieve variables} *)

  method get_return_var: variable_t
  method get_return_contexts: program_context_int list
  method get_memory_variables: variable_t list
  method get_memory_variables_with_base: variable_t -> variable_t list
  method get_parameters: variable_t list

  method get_pointer_variables  : variable_type_t -> variable_t list   (* symbolic program variable with type TPtr *)
  method get_site_call_vars: program_context_int -> (variable_t list * variable_t list)
  (* augmentation variables with purpose: call, split by context *)
  method get_call_vars: variable_t list
  method get_fn_entry_call_var: variable_t

  method get_variable_type: variable_t -> typ
  method get_local_variable: variable_t -> (varinfo * offset)
  method get_global_variable: variable_t -> (varinfo * offset)
  method get_memory_variable: variable_t -> (memory_reference_int * offset)
  method get_memory_address: variable_t -> (memory_reference_int * offset)
  method get_memory_region: symbol_t -> memory_region_int
  method get_vinfo_offset: variable_t -> varinfo -> offset option
  method get_initial_value_variable: variable_t -> variable_t

  method get_declared_type_value_range:
           variable_t -> numerical_t option * numerical_t option

  method get_external_addresses: variable_t list
  method get_symbolic_dereferences: variable_t list

  method get_parameter_exp: variable_t -> exp
  method get_global_exp: variable_t -> exp
  method get_callvar_callee: variable_t -> varinfo
  method get_callvar_args: variable_t -> xpr_t option list
  method get_callvar_context: variable_t -> program_context_int
  method get_callsym_callee: symbol_t -> varinfo
  method get_callsym_args: symbol_t -> xpr_t option list
  method get_callsym_context: symbol_t -> program_context_int
  method get_callsym_location: symbol_t -> location
  method get_tainted_value_origin: variable_t -> variable_t
  method get_tainted_value_bounds: variable_t -> xpr_t option * xpr_t option
  method get_byte_sequence_origin: variable_t -> variable_t
  method get_memory_reference : variable_t -> memory_reference_int

  method get_region_name: int -> string   (* memory region index *)
  method get_indicator: variable_t -> int  (* augmentation variable *)

  (** {1 Predicates} *)

  method is_augmentation_variable: variable_t -> bool
  method is_call_var: variable_t -> bool
  method is_program_variable: variable_t -> bool
  method is_local_variable: variable_t -> bool
  method is_global_variable: variable_t -> bool
  method is_fixed_value: variable_t -> bool
  method is_memory_variable: variable_t -> bool
  method is_memory_address: variable_t -> bool
  method is_fixed_xpr: xpr_t -> bool
  method is_initial_value: variable_t -> bool
  method is_initial_parameter_value: variable_t -> bool
  method is_initial_parameter_deref_value: variable_t -> bool
  method is_initial_global_value: variable_t -> bool
  method is_function_return_value: variable_t -> bool
  method is_function_return_value_sym: symbol_t -> bool
  method is_function_sideeffect_value: variable_t -> bool
  method is_function_sideeffect_value_sym: symbol_t -> bool
  method is_tainted_value: variable_t -> bool
  method is_byte_sequence: variable_t -> bool
  method has_constant_offset: variable_t -> bool
  method has_return_var: bool
  method check_variable_applies_to_po:
           variable_t -> ?argindex:int -> bool -> int -> bool

  (** {1 Transactions} *)

  method start_transaction: unit
  method end_transaction: (bool * cmd_t list)

  method get_function_break_label: string
  method start_loop: unit
  method end_loop: unit
  method start_switch: unit
  method end_switch: unit
  method get_break_label: string
  method get_continue_label: string

end


(** Provides invariants for a given cfg context that make use of assumptions
    currently active for the requester.*)
class type orakel_int =
object

  method get_external_value : program_context_int -> xpr_t -> xpr_t option
  method get_regions: program_context_int -> xpr_t -> symbol_t list

end

(* ====================================================== control flow graph === *)

class type gotos_int =
object
  method is_goto_function: bool
  method is_goto_block: stmt -> bool
end

(** {1 Translators} *)

(** Expression translator *)
class type exp_translator_int =
object

  method translate_exp: program_context_int -> exp -> xpr_t
  method translate_lhs: program_context_int -> lval -> variable_t
  method translate_condition:
           program_context_int -> exp -> cmd_t * cmd_t  (* then,else *)

end


(** Assignment translator *)
class type assignment_translator_int =
object

  method translate: program_context_int -> location -> lval -> exp -> c_cmd_t list

end


(** Call translator *)
class type call_translator_int =
object

  method translate:
           program_context_int
           -> location
           -> lval option
           -> exp
           -> exp list
           -> c_cmd_t list

end


class type operations_provider_int =
object
  method get_cmd_operations: program_context_int -> cmd_t list
  method get_return_operation: program_context_int -> exp -> cmd_t list
  method get_c_cmd_operations: program_context_int -> c_cmd_t list
end


(** Control-flow graph translator *)
class type cfg_translator_int =
object

  method translate_breakout_block:
           block -> gotos_int -> program_context_int -> cmd_t list
  method translate_cfg_breakout_block:
           block -> gotos_int -> program_context_int -> cmd_t list

end



class type c_invariants_int =
object
  method reset: unit
  method add_invariant: string -> string -> atlas_t -> unit
  method get_invariants: (string, (string, atlas_t) Hashtbl.t) Hashtbl.t
end


type domain_opsemantics_t =
  string
  -> invariant:atlas_t
  -> stable:bool
  -> fwd_direction:bool
  -> context:symbol_t stack_t
  -> operation:operation_t
  -> atlas_t


(** Function translator *)
class type function_translator_int =
object
  method translate: fundec -> (domain_opsemantics_t option * system_int)
end


class type invariant_list_query_int =
  object
    method lt:
             numerical_t
             -> (counterexample_t option * dependencies_t *  string) option
    method geq:
             numerical_t
             -> (counterexample_t option * dependencies_t * string) option
  end


(** Primary object that keeps track of invariants and can be queries *)
class type po_query_int =
  object
    method env: c_environment_int
    method fenv: cfundeclarations_int
    method fname: string

    method record_safe_result: dependencies_t -> string -> unit
    method record_violation_result: dependencies_t -> string -> unit
    method delegate_to_api:
             ?isfile:bool -> ?isglobal:bool -> po_predicate_t -> int list -> bool
    method mk_global_request: xpredicate_t -> unit
    method mk_postcondition_request: xpredicate_t -> varinfo -> unit
    method set_diagnostic: string -> unit
    method set_exp_diagnostic: ?lb:bool -> ?ub:bool -> exp -> string -> unit
    method set_diagnostic_invariants: int -> unit
    method set_diagnostic_call_invariants: unit
    method set_vinfo_diagnostic_invariants: varinfo -> unit
    method set_diagnostic_arg: int -> string -> unit
    method set_key_diagnostic: string -> string -> unit
    method set_ref_diagnostic: string -> unit
    method add_local_spo: location -> program_context_int -> po_predicate_t -> unit
    method check_command_line_argument:
             exp -> (int -> int -> string) -> (int -> int -> string)
             -> (int -> string) -> bool
    method check_implied_by_assumptions: po_predicate_t -> po_predicate_t option

    method get_external_value: exp -> xpr_t
    method get_proof_obligation: proof_obligation_int
    method get_summary: string -> function_summary_t option
    method get_api_assumptions: api_assumption_int list
    method get_function_library_calls: (string * string) list
    method get_function_direct_callsites: direct_callsite_int list
    method get_function_indirect_callsites: indirect_callsite_int list
    method get_canonical_fnvar_index: variable_t -> int
    method get_postconditions:
             variable_t -> annotated_xpredicate_t list * annotated_xpredicate_t list
    method get_sym_postconditions:
             symbol_t -> annotated_xpredicate_t list * annotated_xpredicate_t list
    method get_sideeffects: variable_t -> annotated_xpredicate_t list
    method get_sym_sideeffects: symbol_t -> annotated_xpredicate_t list
    method get_tainted_value_origin: variable_t -> (string * varinfo * xpredicate_t)
    method get_witness: xpr_t -> variable_t -> xpr_t option
    method get_values: int -> (int * non_relational_value_t) list
    method get_exp_invariants: exp -> invariant_int list
    method get_exp_value: exp -> (int list * xpr_t option)
    method get_exp_upper_bound_value: exp -> (int list * xpr_t option)
    method get_invariants: int -> invariant_int list
    method get_extended_values: int -> exp -> invariant_int list
    method get_call_invariants: invariant_int list
    method get_invariants_lb: int -> invariant_int list     (* sorted for lower-bound *)
    method get_invariants_ub: int -> invariant_int list     (* sorted for upper-bound *)
    method get_pepr_bounds: int -> (invariant_int list * xpr_t list list * xpr_t list list)
    method get_parameter_constraints: xpr_t list
    method get_ntp_value: exp -> (invariant_int * numerical_t) option
    method get_command_line_argument_count : (int * int) option
    method get_command_line_argument_index : exp -> int

    method get_num_value: exp -> numerical_t option
    method get_function_return_value_buffer_size:
             variable_t -> (assumption_type_t list * xpr_t) option
    method get_gv_lowerbound: string -> int option
    method get_gv_upperbound: string -> int option
    method get_lowerbound_xpr: int -> exp -> (xpr_t * int list) option
    method get_upperbound_xpr: int -> exp -> (xpr_t * int list) option

    method xpr_buffer_offset_size:
             int
             -> int
             -> xpr_t
             -> (string * xpr_t * xpr_t * dependencies_t) option (* bytes *)

    method get_buffer_offset_size:
             int
             -> typ
             -> exp
             -> (string * xpr_t * xpr_t * dependencies_t) option (* bytes *)

    method get_elb: exp -> non_relational_value_t -> exp option
    method get_eub: exp -> non_relational_value_t -> exp option
    method get_evb: exp -> non_relational_value_t -> exp option

    method x2api: xpr_t -> exp option
    method x2global: xpr_t -> exp option
    method get_api_expression: xpr_t -> exp
    method get_global_expression: xpr_t -> exp
    method get_function_return_callee: xpr_t -> varinfo
    method get_vinfo_offset_values: varinfo -> (invariant_int * offset) list
    method remove_null_syms      : symbol_t list -> symbol_t list

    method e2x: exp -> xpr_t

    method is_formal: int -> bool
    method is_api_expression: xpr_t -> bool
    method is_global_expression: xpr_t -> bool
    method is_function_return: xpr_t -> bool
    method is_command_line_argument: exp -> bool
    method is_memory_base_address: variable_t -> string option

    method invariants_to_pretty: (int * non_relational_value_t) list -> pretty_t
    method invariant_values_to_pretty: invariant_int list -> pretty_t
    method vinfo_values_to_pretty:
             (int * offset * non_relational_value_t) list -> pretty_t

  end

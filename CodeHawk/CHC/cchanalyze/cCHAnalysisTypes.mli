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
  method mk_external_state_variable: string -> variable_type_t -> variable_t
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

  method get_external_state_value:
           program_context_int -> variable_t -> xpr_t option

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


(** Primary object that keeps track of invariants and can be queried

    This object provides the access point for all information available for
    a single proof obligation (ppo or spo). For brevity, within the description
    this proof obligation is referred to as PO
*)
class type po_query_int =
  object

    (** {1 Basic info} *)

    (** Returns the function symbol table environment. *)
    method env: c_environment_int

    (** Returns the function declarations environment. *)
    method fenv: cfundeclarations_int

    (** Returns the name of the function. *)
    method fname: string

    (** Returns the proof obligation associated with this object (indicated with
        PO in the remainder descriptions of this object).*)
    method get_proof_obligation: proof_obligation_int

    (** Returns the list of api assumptions for this function.*)
    method get_api_assumptions: api_assumption_int list

    (** Returns a list of (header filename, function name) tuples for all library
        calls made by this function (deduplicated).*)
    method get_function_library_calls: (string * string) list

    (** Returns a list of the callsites of all direct calls made by this
        function.*)
    method get_function_direct_callsites: direct_callsite_int list

    (** Returns a list of the callsites of all indirect calls made by this
        function.*)
    method get_function_indirect_callsites: indirect_callsite_int list

    (** Returns a list of all call_var invariants at the cfg context of this
        PO.*)
    method get_call_invariants: invariant_int list

    (** Returns a list of constraints created by the PEPR domain.

        Note: not currently used.
     *)
    method get_parameter_constraints: xpr_t list

    (** {1 Record results} *)

    (** [record_safe_result deps expl] adds the assumptions in [deps] to the
        function api or global environment with PO as a dependent, sets the
        status of PO to safe (Green), and records the dependencies and
        explanation [expl] in PO. Optionally a [site] can be added that
        records the location in the ocaml code that provided the decision
     *)
    method record_safe_result:
             ?site:(string * int * string) option
             -> dependencies_t
             -> string
             -> unit

    (** [record_violation_result deps expl] sets the status of PO to violated
        (Red), and records the dependencies [deps] and explanation [expl]
        in PO. Optionally a [site] can be added that records the location in
        the ocaml code that provided the decision
     *)
    method record_violation_result:
             ?site:(string * int * string) option
             -> dependencies_t
             -> string
             -> unit

    (** [delegate_to_api isfile isglobal ppred invindices] checks if the local
        predicate [ppred] can be converted to an external (api) predicate. If so,
        it converts [ppred] to an api predicate and creates a dependency on this
        api assumption, justified by the invariants indicated by [invindices].
        It sets the status to safe (Green) and adds an explanation stating that the
        PO has been delegated to the api. In this case [true] is returned.
        Optionally a [site] can be added that records the location in the ocaml
        code that provided the decision.

        If [ppred] cannot be converted to an api predicate a diagnostic is set
        to this effect, and [false] is returned.
     *)
    method delegate_to_api:
             ?site:(string * int * string) option
             -> ?isfile:bool
             -> ?isglobal:bool
             -> po_predicate_t
             -> int list
             -> bool

    (** {1 Make requests} *)

    (** {2 Global request} *)

    (** [mk_global_request xpred] adds a global assumption request to the function
        api for external predicate [xpred] and adds a diagnostic to this effect.*)
    method mk_global_request: xpredicate_t -> unit

    (** {2 Postcondition request} *)

    (** [mk_postcondition_request xpred callee] adds a postcondition request to
        the function api for external predicate [xpred] and callee [callee] and
        adds a diagnostic to this effect.*)
    method mk_postcondition_request: xpredicate_t -> varinfo -> unit

    (** {1 Set diagnostics} *)

    (** [set_diagnostic msg] adds message [msg] to the list of general diagnostics
        of PO. Optionally a [site] can be added that records the location of the
        generation of the diagnostic message.*)
    method set_diagnostic: ?site: (string * int * string) option -> string -> unit

    (** [set_key_diagnostic key msg] adds message [msg] as a key diagnostic to
        PO with key [key] Optionally a [site] can be added that records the
        location of the generation of the diagnostic message..

        A key diagnostic is a diagnostic that refers to a particular as yet
        unsolved challenge in the analysis such as the analysis of
        null-termination that prevents the proof obligation to be discharged.
     *)
    method set_key_diagnostic:
             ?site:(string * int * string) option -> string -> string -> unit

    (** [set_ref_diagnostic fname] adds a key diagnostic to PO for a challenge
        in the analysis associated with the function summary for [fname].
        Optionally a [site] can be added that records the location of the
        generation of the diagnoatic message.
     *)
    method set_ref_diagnostic:
             ?site:(string * int * string) option -> string -> unit

    (** [set_diagnostic_arg argindex msg] adds a diagnostic message [msg] to
        PO associated with the PO argument with (1-based) index [argindex].
        Optionally a [site] can be added that records the location of the
        generation of the diagnostic message.
     *)
    method set_diagnostic_arg:
             ?site:(string * int * string) option -> int -> string -> unit

    (** [set_exp_diagnostic lb ub exp msg] adds a diagnostic msg [msg] to PO for
        the expression [exp] prefixed by lb-exp if [lb], ub-exp if [ub] or exp
        if neither of these is true. Optionally a [site] can be added that records
        the location of the generation of the diagnostic message.
     *)
    method set_exp_diagnostic:
             ?site:(string * int * string) option
             -> ?lb:bool
             -> ?ub:bool
             -> exp
             -> string
             -> unit

    (** [set_diagnostic_invariants argindex] adds the invariants associated with
        the argument with (1-based) index [argindex] to the diagnostic invariant
        table for [argindex].*)
    method set_diagnostic_invariants: int -> unit

    (** Adds a message to PO that contains all calls that separate this PO from
        an entry symbol. Optionally a [site] can be added that records the
        location of the generation of the diagnostic message.
     *)
    method set_diagnostic_call_invariants:
             ?site:(string * int * string) option -> unit -> unit

    (** [set_vinfo_diagnostic vinfo] adds a diagnostic message to PO that lists
        all values that variable [vinfo] may have in this PO. Optionally a [site]
        can be added that records the location of the generation of the diagnostic
        message.
     *)
    method set_vinfo_diagnostic_invariants:
             ?site:(string * int * string) option -> varinfo -> unit

    method set_all_diagnostic_invariants:
             ?site:(string * int * string) option -> unit -> unit

    method set_init_vinfo_mem_diagnostic_invariants:
             ?site:(string * int * string) option -> varinfo -> offset -> unit

    method add_local_spo: location -> program_context_int -> po_predicate_t -> unit

    (** {1 Checks} *)

    (** {2 Command-line argument check} *)

    (** [check_command_line_argument exp safemsg vmsg dmsg] checks if [exp] is a
        command-line argument, and if so, checks whether its index is less than
        the argument count. If less the PO is set to safe, if greater than or
        equal the PO is set to violation, and if no argument count is found, a
        diagnostic message is set according to [dmsg].*)
    method check_command_line_argument:
             exp
             -> (int -> int -> string)
             -> (int -> int -> string)
             -> (int -> string)
             -> bool

    (** Returns the index of the supporting invariant fact and the
        command-line argument count if this function is main and an invariant
        fact is available with that information. Otherwise returns None.*)
    method get_command_line_argument_count: (int * int) option

    (** [get_command_line_argument_index exp] returns the (0-based) function
        argument index if exp is a function argument.

        raise [CCHFailure] if [exp] is not a command-line argument.*)
    method get_command_line_argument_index: exp -> int


    method check_implied_by_assumptions: po_predicate_t -> po_predicate_t option

    (** {1 Information} *)

    (** {2 Argument invariants} *)

    (** [get_ivaraints argindex] returns a list of invariants related to the PO
        argument with argument index (1-based) [argindex].

        Diagnostic messages are set if invariants cannot be found.*)
    method get_invariants: int -> invariant_int list

    (** same as [get_invariants], but with the result sorted by lower bound.*)
    method get_invariants_lb: int -> invariant_int list

    (** same as [get_invariants], but with the result sorted by upper bound.*)
    method get_invariants_ub: int -> invariant_int list

    (** [get_pepr_bounds argindex] returns a list of invariants for the PO
        argument with argument index (1-based) [argindex] generated by the
        PEPR domain together with lower-bound and upper-bound expressions. *)
    method get_pepr_bounds:
             int -> (invariant_int list * xpr_t list list * xpr_t list list)

    (** [get_values argindex] returns a list of (invariant index, non-relational
        value) tuples for variables that apply to variables that appear in PO.*)
    method get_values: int -> (int * non_relational_value_t) list

    (** [get_extended_values argindex exp] returns the same list of invariants as
        [get_invariants] extended with value-offset invariants for [exp] if [exp]
        is a vinfo.*)
    method get_extended_values: int -> exp -> invariant_int list

    (* [get_lowerbound_xpr argindex exp] attempts to find a lower bound
       expression for the PO argument indicated by (1-based) [argindex] or
       for [exp]. If successful it returns the expression and a list of
       indices of invariants (if any) used to obtain the the lower bound.*)
    method get_lowerbound_xpr: int -> exp -> (xpr_t * int list) option

    (* [get_upperbound_xpr argindex exp] attempts to find an upper bound
       expression for the PO argument indicated by (1-based) [argindex] or
       for [exp]. If successful it returns the expression and a list of
       indices of invariants (if any) used to obtain the the upper bound.*)
    method get_upperbound_xpr: int -> exp -> (xpr_t * int list) option

    (** [get_buffer_offset_size argindex typ exp] attempts to obtain a
        conservative value of the remaining number of bytes in a buffer in
        the argument in PO indicated with [argindex] with type [typ] or from
        [exp], that is, a lower bound on the buffer size and an upper bound on
        the offset. If successful it returns the name of the declared vinfo,
        the remaining size of the buffer, the offset in the buffer, and the
        dependencies on which these values are based.*)
    method get_buffer_offset_size:
             int
             -> typ
             -> exp
             -> (string * xpr_t * xpr_t * dependencies_t) option (* bytes *)

    (** same as [get_buffer_offset_size] for an xpr_t instead of an exp.*)
    method xpr_buffer_offset_size:
             int
             -> int
             -> xpr_t
             -> (string * xpr_t * xpr_t * dependencies_t) option (* bytes *)

    (** {2 Exp invariants} *)

    (** [get_exp_invariants exp] returns a list for the lval-expression of a
        variable [exp] without offset. If [exp] is not a variable, the empty list
        is returned. *)
    method get_exp_invariants: exp -> invariant_int list

    (** [get_exp_value exp] attempts to obtain a constant numerical or symbolic
        value for [exp]. If successful it returns the value together with a list
        of indices of invariants that produced the value.*)
    method get_exp_value: exp -> (int list * xpr_t option)

    (** [get_exp_upper_bound_value exp] attempts to obtain a numerical or symbolic
        upperbound for [exp]. If successful it returns the value together with a
        list of indices of invariants that produced the value.*)
    method get_exp_upper_bound_value: exp -> (int list * xpr_t option)

    (** [get_num_value exp] attempts to reduce [exp] to a numerical value using
        declarations only.*)
    method get_num_value: exp -> numerical_t option

    (** [get_ntp_value exp] attempts to obtain the index of a null-terminating
        value in an array [exp]. If successful it returns the value of the index
        together with the invariant that produced the null-terminator.*)
    method get_ntp_value: exp -> (invariant_int * numerical_t) option

    (** [get_elb expr nrv] attempts to obtain a lower bound from either [exp]
        or [nrv] that can be delegated.*)
    method get_elb: exp -> non_relational_value_t -> exp option

    (** [get_eub exp nrv] attempts to obtain an upper bound from either [exp]
        or [nrv] that can be delegated.*)
    method get_eub: exp -> non_relational_value_t -> exp option

    (** [get_evb exp nrv] attempts to obtain a (symbolic) value from either [exp]
        or [nrv] that can be delegated.*)
    method get_evb: exp -> non_relational_value_t -> exp option

    (** {2 Vinfo invariants} *)

    method get_vinfo_offset_values: varinfo -> (invariant_int * offset) list

    (** {2 Global variables} *)

    (** [get_gv_lowerbound name] returns a lower bound for the global variable
        with name [name] if the file contract has such lower bound, otherwise it
        returns None.*)
    method get_gv_lowerbound: string -> int option

    (** [get_gv_upperbound name] returns an upper bound for the global variable
        with name [name] if the file contract has such upper bound, otherwise it
        returns None.*)
    method get_gv_upperbound: string -> int option

    method get_init_vinfo_mem_invariants: varinfo -> offset -> invariant_int list


    (** {2 Function summary} *)

    (** [get_summary fname] attempts to obtain a function summary from the
        function summary library for function [fname]. *)
    method get_summary: string -> function_summary_t option

    (** [get_postconditions var] returns a tuple of postconditions and error
        postconditions for function returnvalue variable [var]. If the callee in
        [var] has a library function summary, the postconditions are retrieved
        from the library function summary, else if a function contract exists for
        the callee, the postconditions are retrieved from this function contract,
        otherwise the postconditions assumptions are retrieved from the proof
        callcontext in the proof scaffolding.

        raise [CCHFailure] if [var] is not a function return value variable.*)
    method get_postconditions:
             variable_t
             -> annotated_xpredicate_t list * annotated_xpredicate_t list

    (** same as [get_postconditions var] with the symbol component of [var].*)
    method get_sym_postconditions:
             symbol_t
             -> annotated_xpredicate_t list * annotated_xpredicate_t list

    (** [get_sideeffects var] returns the sideeffects for function
        sideeffect variable [var]. If the callee in
        [var] has a library function summary, the sideeffects are retrieved
        from the library function summary, else if a function contract exists for
        the callee, the sideeffects are retrieved from this function contract,
        otherwise the postassumes are retrieved from the proof callcontext in
        the proof scaffolding.

        raise [CCHFailure] if [var] is not a function return value variable.*)
    method get_sideeffects: variable_t -> annotated_xpredicate_t list

    (** same as [get_sideeffects var] with the symbol component of [var].*)
    method get_sym_sideeffects: symbol_t -> annotated_xpredicate_t list

    (** [get_function_return_callee xpr] returns the varinfo representing the
        callee associated with return value variable expression [xpr].

        raise [CCHFailure] if [xpr] is not a return value variable expression.*)
    method get_function_return_callee: xpr_t -> varinfo

    (** [get_tainted_value_origin var] returns a tuple of an explanation, the
        vinfo for the callee that conferred the taint on [var] and the
        postcondition or sideeffect through which the taint was transmitted.

        raise [CCHFailure] if [var] is not a tainted value.*)
    method get_tainted_value_origin:
             variable_t -> (string * varinfo * xpredicate_t)

    (** [get_witness x var] attempts to create a witness expression for tainted
        variable [var] that satisfies (violation) constraint expression [x].

        Note: a witness expression is created only if the tainted value comes with
        both a lowerbound and an upperbound (that is, a lowerbound and upperbound
        must be present in the function summary.)*)
    method get_witness: xpr_t -> variable_t -> xpr_t option

    (** [get_function_return_value_buffer_size var] attempts to determine the size
        of a returned buffer from the postconditions associated with the function
        return value variable and the arguments given to that call.*)
    method get_function_return_value_buffer_size:
             variable_t -> (assumption_type_t list * xpr_t) option

    (** {1 Normalization} *)

    (** [get_canonical_fnvar_index var] returns the variable index number of [var].
        If [var] is a function return value or a side-effect value, a new,
        canonical index, is generated for a call without arguments, otherwise
        the index number of [var] itself is returned.*)
    method get_canonical_fnvar_index: variable_t -> int

    (** {1 Conversion} *)

    (** {2 Exp -> xpr} *)

    (** [e2x exp] attempts to syntactically convert [exp] to an [xpr_t]. This
        succeeds if [exp] is a numerical constant. Otherwise a random constant is
        returned.*)
    method e2x: exp -> xpr_t

    (** [get_external_value exp] attempts to convert [exp] to an [xpr_t] using
        the [num_exp_translator] with location invariants provided to aid in the
        conversion. If [exp] cannot be converted against the invariants, a random
        constant is returned.*)
    method get_external_value: exp -> xpr_t

    (** {2 Xpr -> exp} *)

    (** [x2api xpr] attempts to convert expression [xpr] (possibly produced by
        invariants) to a c expression that can be used in an api assumption.*)
    method x2api: xpr_t -> exp option

    (** [get_api_expression xpr] returns a c expression that can represent xpr
        in an api assumption.

        raise [CCHFailure] if [xpr] cannot be thus converted.*)
    method get_api_expression: xpr_t -> exp

    (** [x2global xpr] attempts to convert expression [xpr] into a global c
        expression. This succeeds if [xpr] is a constant or if it is the initial
        value of a global variable.*)
    method x2global: xpr_t -> exp option

    (** [get_global_expression xpr] returns the equivalent c expression of [xpr]
        if [xpr] is a constant value or the initial value of a global variable (or
        some combination of the two).

        raise [CCHFailure] if [xpr] is not a constant value or initial value of a
        global variable.*)
    method get_global_expression: xpr_t -> exp

    (** [remove_null_syms syms] returns the sublist of memory region symbols
        [syms] that are not NULL.

        raise [CCHFailure] if one or more of the symbols in [syms] are not memory
        region symbols.*)
    method remove_null_syms: symbol_t list -> symbol_t list

    (** {1 Predicates} *)

    method is_formal: int -> bool
    method is_api_expression: xpr_t -> bool
    method is_global_expression: xpr_t -> bool
    method is_function_return: xpr_t -> bool
    method is_command_line_argument: exp -> bool
    method is_memory_base_address: variable_t -> string option

    (** {1 Printing} *)

    method invariants_to_pretty: (int * non_relational_value_t) list -> pretty_t
    method invariant_values_to_pretty: invariant_int list -> pretty_t
    method vinfo_values_to_pretty:
             (int * offset * non_relational_value_t) list -> pretty_t

  end

(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023-2024 Aarno Labs LLC

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
open CHNumerical
open CHPEPRTypes
open CHPretty

(* xprt *)
open XprTypes

(* chutil *)
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

class type idregistry_int =
  object
    method add: string -> string -> string    (* prefix, hash string *)
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit
  end

(** {1 Memory representations}*)

(** {2 Memory base} *)

(** The memory_base_t type denotes the (symbolic) address of the base of a memory
   region that is used as the ground type in a memory reference (a representation
   of a memory variable) and in a memory region (a representation of the entire
   memory region identified by this base.
 *)
type memory_base_t =
  | CNull of int
  (** index of companion memory region *)

  | CStringLiteral of string
  (** address of a string literal *)

  | CStackAddress of variable_t
  (** base address of a regular memory region on the stack: local variable *)

  | CGlobalAddress of variable_t
  (** base address of a global memory region: global variable *)

  | CBaseVar of variable_t
  (** address provided by contents of an externally controlled variable *)

  | CUninterpreted of string
  (** address without interpretation *)


(** {2 Memory_region} *)

(** A memory region denotes the entire region identified by its base address. It
    is used as a rhs for pointers for analyses that are independent of offsets
    within the memory region such as null analysis and valid-mem analysis. Null
    analysis can be performed solely by memory region identification. Valid-mem
    analysis requires the memory region to be represented as a lhs, since its
    status can change from valid to non-valid by free operations.
 *)
class type memory_region_int =
  object ('a)

    method index : int
    method compare: 'a -> int

    method get_memory_base: memory_base_t
    method get_base_var: variable_t
    method get_null_region: int
    method get_stack_var  : variable_t

    (** returns [true] if guaranteed to be valid memory, [false] otherwise *)
    method is_valid: bool

    (** returns [true] if guaranteed to be not null, [false] otherwise *)
    method is_not_null: bool

    (** returns [true] if guaranteed to be [null], [false] otherwise *)
    method is_null: bool

    method is_stack_region: bool
    method is_basevar_region: bool
    method is_string_region : bool
    method is_uninterpreted: bool

    method write_xml : xml_element_int -> unit

    method toPretty: pretty_t
  end


class type memory_region_manager_int =
  object

    (** {1 Region creation}*)

    method mk_base_region: memory_base_t -> memory_region_int
    method mk_null: int -> memory_region_int     (* index of companion region *)
    method mk_string_region: string -> memory_region_int

    (** [mk_stack_region] returns a stack memory region with the address given
        by [addr]*)
    method mk_stack_region: variable_t -> memory_region_int

    (** [mk_global_region addr] returns a global memory region with address
        given by [addr]*)
    method mk_global_region: variable_t -> memory_region_int

    (** [mk_external_region base] returns a memory with base pointer [base]*)
    method mk_external_region: variable_t -> memory_region_int
    method mk_uninterpreted_region: string -> memory_region_int

    method mk_null_sym: int -> symbol_t
    method mk_string_region_sym: string -> symbol_t
    method mk_stack_region_sym : variable_t -> symbol_t

    method mk_global_region_sym: variable_t -> symbol_t
    method mk_external_region_sym: variable_t -> symbol_t
    method mk_uninterpreted_sym: string -> symbol_t
    method mk_base_region_sym: memory_base_t -> symbol_t

    (** {1 Region access}*)

    method get_memory_region: int -> memory_region_int
    method get_basevar_regions: memory_region_int list
    method get_null_syms: symbol_t list

    (** {1 Region predicates}*)

    method is_null: int -> bool
    method is_not_null: int -> bool
    method is_valid: int -> bool
    method is_string_region: int -> bool
    method is_uninterpreted: int -> bool

  end


(** {2 Memory reference} *)

(* A memory reference is a memory base address;
   points to the storage location of a variable at that location in memory
 *)
type memory_reference_data_t = {
    memrefbase: memory_base_t ;
    memreftype: typ
  }


class type memory_reference_int =
object ('a)

  (* identification *)
  method index: int

  (* comparison *)
  method compare: 'a -> int

  (* accessors *)
  method get_data: memory_reference_data_t
  method get_base: memory_base_t
  method get_type: typ
  method get_name: string
  method get_external_basevar: variable_t
  method get_stack_address_var: variable_t
  method get_global_address_var: variable_t
  method get_base_variable: variable_t

  (* predicates *)
  method has_base_variable: bool
  method has_external_base: bool
  method is_stack_reference: bool
  method is_global_reference: bool

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty : pretty_t

end

class type memory_reference_manager_int =
object ('a)

  (* object creators *)
  method mk_string_reference: string -> typ -> memory_reference_int
  method mk_stack_reference: variable_t -> typ -> memory_reference_int
  method mk_global_reference: variable_t -> typ -> memory_reference_int
  method mk_external_reference: variable_t -> typ -> memory_reference_int

  (* accessors *)
  method get_memory_reference: int -> memory_reference_int

end


(** {1 Variable representation} *)

(** {2 Constant-value variable} *)

(** A constant_value_variable is a place holder for a constant value to enable the
    propagation of its (symbolic) value in the various analyses. They represent
    values that do not have a concrete value in the analysis domain, but are
    constant throughout the analysis of a function. They should only be used as
    rhs values (no assignment).
 *)
type constant_value_variable_t =
  | InitialValue of variable_t * typ
  (** value of variable upon function entry *)

  | FunctionReturnValue of
      location * program_context_int * varinfo * (xpr_t option list)
  (** value returned by a direct call *)

  | ExpReturnValue of
      location * program_context_int * xpr_t * (xpr_t option list) * typ
  (** value returned by an indirect call *)

  | FunctionSideEffectValue of
      location * program_context_int * varinfo * (xpr_t option list) * int * typ
  (** value set as side effect of a direct call *)

  | ExpSideEffectValue of
      location * program_context_int * xpr_t * (xpr_t option list) * int * typ
  (** value set as side effect of an indirect call *)

  | SymbolicValue of xpr_t * typ
  (** expression that consists entirely of symbolic constants *)

  | TaintedValue of variable_t * xpr_t option * xpr_t option * typ
  (** tainted value with lower-bound and upper-bound expressions *)

  | ByteSequence of variable_t * xpr_t option
  (** byte sequence written by v with length x *)

  | MemoryAddress of int * offset
  (** memory reference index *)


(** {2 Unique storage location} *)

type c_variable_denotation_t =
  | LocalVariable of varinfo * offset
  (** stack variable, type of variable *)

  | GlobalVariable of varinfo * offset
  (** global variable *)

  | ExternalStateVariable of string
  (** variable in an external library that holds state, but is only accessible
      to the application via functions in that library according to a fixed
      protocol.

      Example:
      libc/strtok: libc maintains a pointer to the current position in the string
      to be tokenized upon the first call to strtok with a string argument.
      Subsequent calls pass NULL as first argument to have libc advance the pointer
      through the string. The return value of strtok is guaranteed to be a pointer
      within the same string or NULL, however this fact cannot be obtained from
      the strtok call itself, because the pointer to the string is no longer
      present as argument. Therefore it must be obtained from elsewhere.
   *)

  | MemoryVariable of int * offset
  (** variable identified by memory reference index *)

  | MemoryRegionVariable of int
  (** variable used for valid-mem region analysis *)

  | ReturnVariable of typ

  | FieldVariable of fielduse
  (** variable that denotes the collection of all fields with the given name *)

  | CheckVariable of (bool * int * int) list * typ
  (** is_ppo, proof obligation id, exp seq number *)

  | AuxiliaryVariable of constant_value_variable_t

  | AugmentationVariable of string * string * int
  (** name, purpose, reference index, variable that does not interact with
      other variables to collect info *)

(** {2 Dictionary} *)

class type vardictionary_int =
  object

    method xd: xprdictionary_int
    method fdecls: cfundeclarations_int

    method index_memory_base: memory_base_t -> int
    method index_memory_reference_data: memory_reference_data_t -> int
    method index_constant_value_variable: constant_value_variable_t -> int
    method index_c_variable_denotation: c_variable_denotation_t -> int

    method get_memory_base: int -> memory_base_t
    method get_memory_reference_data: int -> memory_reference_data_t
    method get_constant_value_variable: int -> constant_value_variable_t
    method get_c_variable_denotation: int -> c_variable_denotation_t

    method get_indexed_variables: (int * c_variable_denotation_t) list
    method get_indexed_memory_bases: (int * memory_base_t) list
    method get_indexed_memory_reference_data: (int * memory_reference_data_t) list

    method write_xml_memory_base:
             ?tag:string -> xml_element_int -> memory_base_t -> unit
    method read_xml_memory_base:
             ?tag:string -> xml_element_int -> memory_base_t

    method write_xml_memory_reference_data:
             ?tag:string -> xml_element_int -> memory_reference_data_t -> unit
    method read_xml_memory_reference_data:
             ?tag:string -> xml_element_int -> memory_reference_data_t

    method write_xml_constant_value_variable:
             ?tag:string -> xml_element_int -> constant_value_variable_t -> unit
    method read_xml_constant_value_variable:
             ?tag:string -> xml_element_int -> constant_value_variable_t

    method write_xml_c_variable_denotation:
             ?tag:string -> xml_element_int -> c_variable_denotation_t -> unit
    method read_xml_c_variable_denotation:
             ?tag:string -> xml_element_int -> c_variable_denotation_t

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

    method toPretty : pretty_t

  end

(** {2 C-variable}*)

class type c_variable_int =
object ('a)
  (* identity *)
  method index  : int
  method compare: 'a -> int

  (* accessors *)
  method get_name : string
  method get_type : memory_reference_manager_int -> typ
  method get_denotation: c_variable_denotation_t
  method get_initial_value_variable: variable_t
  method get_function_return_value_callee: varinfo
  method get_function_return_value_args: xpr_t option list
  method get_function_return_value_context: program_context_int
  method get_function_return_value_location: location
  method get_tainted_value_origin: variable_t
  method get_tainted_value_bounds: xpr_t option * xpr_t option
  method get_byte_sequence_origin: variable_t
  method get_purpose: string    (*  augmentation variable  *)
  method get_indicator: int     (*  augmentation variable *)

  (* predicates *)
  method is_program_variable: bool
  method is_fixed_value: bool
  method is_initial_value: bool
  method is_function_return_value: bool
  method is_function_sideeffect_value: bool
  method is_tainted_value: bool
  method is_byte_sequence: bool
  method is_augmentation_variable: bool
  method has_constant_offset: bool
  method applies_to_po: ?argindex:int -> bool -> int -> bool

  (* printing *)
  method toPretty: pretty_t

end

(** {2 Variable manager}*)

class type variable_manager_int =
object

  (** {1 Variable creation}*)

  method mk_local_variable: varinfo -> offset -> c_variable_int

  method mk_global_variable: varinfo -> offset -> c_variable_int

  method mk_memory_variable: int -> offset -> c_variable_int

  method mk_return_variable: typ -> c_variable_int

  method mk_augmentation_variable: string -> string -> int -> c_variable_int

  method mk_external_state_variable: string -> c_variable_int

  method mk_check_variable: (bool * int * int) list -> typ -> c_variable_int

  method mk_symbolic_value: xpr_t -> typ -> c_variable_int

  (** mk_memory_address memindex [offset] returns a memory address from memory
      reference index [memindex] and an offset*)
  method mk_memory_address: int -> offset -> c_variable_int

  method mk_string_address: string -> offset -> typ -> c_variable_int

  method mk_initial_value: variable_t -> typ -> c_variable_int

  method mk_memreg_variable: int -> c_variable_int

  method mk_field_variable: fielduse -> c_variable_int

  method mk_function_return_value:
           location
           -> program_context_int
           -> varinfo
           -> xpr_t option list
           -> c_variable_int

  method mk_exp_return_value :
           location
           -> program_context_int
           -> xpr_t
           -> xpr_t option list
           -> typ
           -> c_variable_int

  method mk_function_sideeffect_value:
           location
           -> program_context_int
           -> varinfo
           -> xpr_t option list
           -> int -> typ
           -> c_variable_int

  method mk_tainted_value:
           variable_t -> xpr_t option -> xpr_t option -> typ -> c_variable_int

  method mk_byte_sequence: variable_t -> xpr_t option -> c_variable_int

  (** {1 Variable access} *)

  method vard: vardictionary_int

  method memrefmgr: memory_reference_manager_int

  method memregmgr: memory_region_manager_int

  method get_variable: int -> c_variable_int

  method get_variable_type: int -> typ

  method get_symbolic_value: int -> xpr_t

  method get_check_variable: int -> ((bool * int * int) list * typ)

  (** [get_parameter_exp varindex] returns the expression associated with
      the initial-value variable with index [varindex] of either a local
      variable or a memory variable with an external base variable.

      raise CCHFailure if [varindex] does not belong to such a variable.
   *)
  method get_parameter_exp: int -> exp

  (** [get_global_exp varindex] returns the expression associated with the
      initial-value variable with index [varindex] of a global variable.

      raise CCHFailure if [varindex] does not belong to such a variable.
   *)
  method get_global_exp: int -> exp

  (** [get_callee varindex] returns the varinfo of the function belonging
      to the return variable or side-effect variable with index [varindex].

      raise CCHFailure if [varindex] does not belong to a function-return
      of function-side-effect variable.
   *)
  method get_callee: int -> varinfo

  method get_callee_args: int -> xpr_t option list

  method get_callee_context: int -> program_context_int

  method get_callee_location: int -> location

  method get_tainted_value_origin: int -> variable_t

  (** [get_tainted_value_bounds varindex] returns the optional lower and upper
      bounds of a tainted variable with index index [varindex].

      raise CCHFailure if [varindex] does not belong to a tainted variable.
   *)
  method get_tainted_value_bounds: int -> xpr_t option * xpr_t option

  method get_byte_sequence_origin: int -> variable_t

  method get_memory_reference: int -> memory_reference_int

  method get_local_variable: int -> (varinfo * offset)

  method get_global_variable: int -> (varinfo * offset)

  method get_memory_variable: int -> (memory_reference_int * offset)

  method get_memory_address: int -> (memory_reference_int * offset)
  method get_initial_value_variable: int -> variable_t

  (** [get_purpose varindex] returns the purpose associated with the
      augmentation variable with index [varindex]

      raise CCHFailure if [varindex] does not belong to an augmentation
      variable.
   *)
  method get_purpose: int -> string

  (** [get_indicator varindex] returns the indicator associated with the
      augmentation variable with index [varindex]

      raise CCHFailure if [varindex] does not belong to an augmentation
      variable.
   *)
  method get_indicator: int -> int

  (** [get_canonical_fnvar_index varindex] returns the index of a variable that
      represents the same function-return value or side-effect variable as the
      variable with [varindex], but without arguments.

      raise CCHFailure if [varindex] does not belong to a function-return or
      side-effect value variable.
   *)
  method get_canonical_fnvar_index: int -> int

  (** {1 Predicates on variables}*)

  method is_symbolic_value: int -> bool

  method is_check_variable: int -> bool

  method is_program_lval: int -> bool

  method is_local_variable: int -> bool

  method is_global_variable: int -> bool

  method is_memory_variable: int -> bool

  method is_memory_address: int -> bool

  method is_program_variable: int -> bool

  method is_augmentation_variable: int -> bool

  method is_fixed_value: int -> bool

  method is_initial_value: int -> bool

  method is_initial_parameter_value: int -> bool

  method is_initial_global_value: int -> bool

  method is_initial_parameter_deref_value: int -> bool

  method is_function_return_value: int -> bool

  method is_function_sideeffect_value: int -> bool
  method is_tainted_value: int -> bool

  method is_byte_sequence: int -> bool

  method has_constant_offset: int -> bool

  method applies_to_po: int -> ?argindex:int -> bool -> int -> bool

  (** {1 Xml/printing} *)

  method write_xml: xml_element_int -> unit

  method variable_to_pretty: variable_t -> pretty_t

end


(** {1 Assignment Dictionary}*)


type assignment_data_t = {
    asg_rhs: exp ;
    asg_loc: location ;
    asg_context: program_context_int
  }

type global_value_t =
  | GlobalValue of string * int * exp option * exp list
   (** vname, vid, init-exp, assign-exps *)


type assignment_t =
  | InitAssignment of string * int * init
  (** vname, vid *)

  | GlobalAssignment of string * string * int * assignment_data_t
  (** fname, vname, vid *)

  | GlobalIndexAssignment of string * string * int * int * assignment_data_t

  | StaticAssignment of string * string * int * assignment_data_t
  (** fname, vname, vid *)

  | StaticIndexAssignment of string * string * int * int * assignment_data_t

  | FieldAssignment of string * string  * int * lval * assignment_data_t
  (** fname, fieldname, ckey *)

  | UnknownAssignment of string * lval * assignment_data_t
(** fname, lhs *)


class type assignment_dictionary_int =
  object

    method reset: unit

    method index_assignment: assignment_t -> int

    method index_global_value: global_value_t -> int

    method get_assignment: int -> assignment_t

    method get_global_value: int -> global_value_t

    method get_assignments: assignment_t list

    method get_global_values: global_value_t list

    method read_xml_assignment: ?tag:string -> xml_element_int -> assignment_t

    method read_xml_global_value:
             ?tag:string -> xml_element_int -> global_value_t

    method write_xml_assignment:
             ?tag:string -> xml_element_int -> assignment_t -> unit

    method write_xml_global_value:
             ?tag:string -> xml_element_int -> global_value_t -> unit

    method write_xml: xml_element_int -> unit

    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t

  end


(** {1 Proof obligations}*)


(** Predicates on expressions and other types that are evaluated on a program
    state.*)
type po_predicate_t =


  | PNotNull of exp
  (** Pointer expression [exp] is not null.*)

  | PNull of exp
  (** Pointer expression [exp] is null.*)

  | PValidMem of exp
  (** Pointer expression [exp] points to a valid (not freed) memory region.*)

  | PControlledResource of string * exp
  (** Value of controlled resource expression [exp] is not tainted.*)

  | PInScope of exp
  (** Pointer expression [exp] points to memory currently in scope.*)

  | PStackAddressEscape of lval option * exp
  (** Pointer expression is not assigned to lval with longer lifetime and
      is not returned. *)

  | PAllocationBase of exp
  (** Pointer expression [exp] holds the start address of a dynamically allocated
      memory region (i.e., this expression can be freed)*)

  | PTypeAtOffset of typ * exp
  (** Expression [exp] has the given type (to be checked when casting).*)

  | PLowerBound of typ * exp
  (** Pointer expression [exp] with type [typ] has a value greater than or
      equal to zero. *)

  | PUpperBound of typ * exp
  (** Pointer expression [exp] has a value that is less than or equal to the
      highest address that can be dereferenced for type [typ].*)

  | PIndexLowerBound of exp
  (** array access within declared array with known length *)

  | PIndexUpperBound of exp * exp
  (** array access within declared array with known length *)

  | PInitialized of lval
  (** lval has a value *)

  | PInitializedRange of exp * exp
  (** number of elements that must have a value *)

  | PCast of typ * typ * exp
  (** exp must be compatible with the target type *)

  | PPointerCast of typ * typ * exp
  (** the memory pointed to must be compatible with the target type *)

  | PFormatCast of typ * typ *  exp
  (** cast of argument to expected format specifier *)

  | PSignedToUnsignedCastLB of ikind * ikind * exp
  (** exp must be non-negative *)

  | PSignedToUnsignedCastUB of ikind * ikind * exp
  (** exp must fit upper bound of target type *)

  | PUnsignedToSignedCast of ikind * ikind * exp
  (** exp must fit upper bound of target type *)

  | PUnsignedToUnsignedCast of ikind * ikind * exp
  (** exp must fit upper bound of target type *)

  | PSignedToSignedCastLB of ikind * ikind * exp
  (** exp must fit lower bound of target type *)

  | PSignedToSignedCastUB of ikind * ikind * exp
  (** exp must fit upper bound of target type *)

  | PNotZero of exp
  (** value must not be zero *)

  | PNonNegative of exp
  (** value must be non-negative *)

  | PNullTerminated of exp
  (** memory region pointed to by exp must be null terminated *)

  | PIntUnderflow of binop * exp * exp * ikind
  (** result of operation must not exceed max size of ikind *)

  | PIntOverflow of binop * exp * exp * ikind
  (** result of operation must not below min size of ikind *)

  | PUIntUnderflow of binop * exp * exp * ikind
  (** result of operation must not be below zero (well-defined, but checked for
      stronger IH) *)

  | PUIntOverflow of binop * exp * exp * ikind
  (** result of operation must not exceed max size of ikind (well-defined, but
      checked for IH *)

  | PWidthOverflow of exp * ikind
  (** value must be smaller than width of ikind type *)

  | PPtrLowerBound of typ * binop * exp * exp
  (** result of pointer operation must be  greater than or equal to zero ;
      type refers to the target type *)

  | PPtrUpperBound of typ * binop * exp * exp
  (** result of pointer operation must be less than or equal to the size of
      the type (equal to cannot be dereferenced, but is allowed as result of
      pointer arithmetic; type refers to the target type *)

  | PPtrUpperBoundDeref of typ * binop * exp * exp
  (** result of pointer operations must be able to be dereferenced; type refers
      to the target type *)

  | PCommonBase of exp * exp
  (** the two expressions must point into the same memory region *)

  | PCommonBaseType of exp * exp
  (** the two expressions must point into the same array type *)

  | PFormatString of exp
  (** exp must point to a string literal *)
  | PVarArgs of exp * int * exp list
  (** format string exp conforms with argument expressions *)

  | PNoOverlap of exp * exp
  (** the two memory regions pointed to must not overlap *)

  | PValueConstraint of exp
  (** boolean expression that must be true *)

  | PDSCondition of ds_condition_t * exp
  (** data structure condition applied to exp *)

  | PContract of int * string * exp
  (** file-id, contract name, expression passed under contract *)

  | PConfined of exp
  (** pointer expression goes out of scope without leaking any references *)

  | PMemoryPreserved of exp
  (** pointed to memory still exists *)

  | PValuePreserved of exp
  (** value of expression at start of function is preserved *)

  | PUniquePointer of exp
  (** expression is the only reference to the memory region *)

  | PPreservedAllMemory
  (** preserved all external memory (may allocate and free locally used memory) *)

  | PPreservedAllMemoryX of exp list
  (** preserved all external memory except the pointers indicated *)

  | PContractObligation of string
  (** named contract obligation with assigned semantics *)

  | PBuffer of exp * exp
  (** e1 points to a buffer with at least e2 bytes after e1 *)

  | PRevBuffer of exp * exp
  (** e1 points to a buffer with at least e2 bytes before e1 *)

  | PNewMemory of exp
  (** e points to a buffer allocated after the invocation of the function *)

  | PHeapAddress of exp
  (** e points to heap memory *)

  | PGlobalAddress of exp
  (** e points to global memory *)

  | PDistinctRegion of exp * int
  (** memref index is distinct from the region pointed to by exp *)


type violation_severity_t =
  | UndefinedBehavior
  | ImplementationDefinedBehavior
  | DistinctFromMathResult
  | IHStrengthening


type po_reference_entry_t = {
    por_section: string ;
    por_item: string
  }


(** index nr (starting at 1), name, type, description *)
type po_explanation_argument_t = int * string * string * string


type po_explanation_t = {
    pox_tag: string ;
    pox_desc: string ;
    pox_arguments: po_explanation_argument_t list ;
    pox_cstandard_refs: po_reference_entry_t list ;
    pox_notes: string list;
    pox_severity: violation_severity_t
  }


class type predicate_dictionary_int =
  object

    method reset: unit

    method index_po_predicate: po_predicate_t -> int

    method get_po_predicate: int -> po_predicate_t

    method read_xml_po_predicate:
             ?tag:string -> xml_element_int -> po_predicate_t

    method write_xml_po_predicate:
             ?tag:string -> xml_element_int -> po_predicate_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty : pretty_t

  end


type po_status_t = Green | Orange | Red | Purple | Blue | Grey


type ppo_type_t =
  | PPOprog of location * program_context_int * po_predicate_t
  | PPOlib of
      location * program_context_int * po_predicate_t * string * xpredicate_t


type spo_type_t =
  | CallsiteSPO of location * program_context_int * po_predicate_t * int
  (** api-id *)

  | ReturnsiteSPO of
      location * program_context_int * po_predicate_t * xpredicate_t

  | LocalSPO of location * program_context_int * po_predicate_t


type po_type_t =
  | PPO of ppo_type_t
  | SPO of spo_type_t


type assumption_type_t =
  | ApiAssumption of po_predicate_t
  | GlobalApiAssumption of po_predicate_t
  | PostAssumption of int * xpredicate_t   (* callee vid *)
  | GlobalAssumption of xpredicate_t
  | LocalAssumption of po_predicate_t


type dependencies_t =
  | DStmt
  (** discharged against the statement itself and the declarations *)

  | DLocal of int list
  (** discharged against local invariants *)

  | DReduced of int list * assumption_type_t list
  (** invariants, reduction to local assumptions *)

  | DEnvC of int list * assumption_type_t list
  (** invariants, assumptions used in delegation *)

  | DUnreachable of string
  (** discharged based on unreachability of <domain name> *)


type counterexample_t =
  | TaintedValue of numerical_t


class type podictionary_int =
  object

    method fdecls: cfundeclarations_int

    method index_assumption: assumption_type_t -> int
    method index_ppo_type: ppo_type_t -> int
    method index_spo_type: spo_type_t -> int

    method get_assumption: int -> assumption_type_t
    method get_ppo_type: int -> ppo_type_t
    method get_spo_type: int -> spo_type_t

    method write_xml_assumption:
             ?tag:string -> xml_element_int -> assumption_type_t -> unit
    method read_xml_assumption:
             ?tag:string -> xml_element_int -> assumption_type_t

    method write_xml_ppo_type:
             ?tag:string -> xml_element_int -> ppo_type_t -> unit
    method read_xml_ppo_type:
             ?tag:string -> xml_element_int -> ppo_type_t

    method write_xml_spo_type:
             ?tag:string -> xml_element_int -> spo_type_t -> unit
    method read_xml_spo_type:
             ?tag:string -> xml_element_int -> spo_type_t

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t

  end


class type diagnostic_int =
  object
    method clear: unit
    method set_invariants: int -> int list -> unit   (* expression index *)
    method get_invariants: (int * int list) list
    method add_msg: string -> unit
    method add_arg_msg: int -> string -> unit
    method add_key_msg: string -> string -> unit
    method is_empty: bool
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit
    method arg_messages_to_pretty : pretty_t
    method key_messages_to_pretty : pretty_t
    method toPretty: pretty_t
  end

(** Proof obligations

   Proof obligations are local to a function. All type indices (compinfo indices)
   are local indices. Primary proof obligations are always local to the function
   and thus naturally use local indices. Supporting proof obligations originate from
   api's of other functions, which have global indices; these global indices are
   converted to local indices when supporting proof obligations are created *)
class type proof_obligation_int =
  object

    method index: int

    method set_status: po_status_t -> unit

    method set_dependencies: dependencies_t -> unit

    method set_explanation: string -> unit

    method add_diagnostic_msg: string -> unit

    method add_diagnostic_arg_msg: int -> string -> unit

    method add_diagnostic_key_msg: string -> string -> unit

    method set_diagnostic_invariants: int -> int list -> unit

    method set_resolution_timestamp: string -> unit

    method get_predicate: po_predicate_t

    method get_location: location

    method get_context: program_context_int

    method get_dependencies: dependencies_t option

    method get_explanation: string

    method get_diagnostic: diagnostic_int

    method get_status: po_status_t

    method get_timestamp: string

    method is_closed: bool

    method is_violation: bool

    method is_opaque: bool

    method is_ppo: bool

    method write_xml: xml_element_int -> unit

    method toPretty: pretty_t
  end


class type ppo_manager_int =
  object

    method add_ppo: location -> program_context_int -> po_predicate_t -> unit
    method add_lib_ppo:
             location
             -> program_context_int
             -> po_predicate_t
             -> string
             -> xpredicate_t
             -> unit

    method get_ppo: int -> proof_obligation_int
    method get_ppos: proof_obligation_int list

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


(** {1 Call sites}*)

class type indirect_callsite_int =
  object

    method set_callees: varinfo list -> unit

    method get_callexp: exp
    method get_callees: varinfo list
    method get_arguments: exp list
    method get_context: program_context_int
    method get_header: string
    method get_location: location
    method get_spos: proof_obligation_int list
    method get_postassumes: annotated_xpredicate_t list
    method get_spo_lists: (int * proof_obligation_int list) list

    method write_xml: xml_element_int -> unit

  end


class type direct_callsite_int =
  object
    method get_callee: varinfo
    method get_arguments: exp list
    method get_context: program_context_int
    method get_header: string
    method get_location: location
    method get_spos: proof_obligation_int list
    method get_postassumes: annotated_xpredicate_t list
    method get_spo_lists: (int * proof_obligation_int list) list

    method write_xml: xml_element_int -> unit
  end


class type callsite_manager_int =
  object

    method add_direct_call:
             location
             -> program_context_int
             -> ?header:string
             -> varinfo
             -> exp list
             -> unit
    method add_indirect_call:
             location
             -> program_context_int
             -> ?header:string
             -> exp
             -> exp list
             -> unit
    method create_contract_proof_obligations: unit

    method get_call_count: int
    method get_spos: proof_obligation_int list
    method get_direct_callsites: direct_callsite_int list
    method get_indirect_callsites: indirect_callsite_int list
    method get_indirect_callsite: program_context_int -> indirect_callsite_int
    method get_direct_callsite: program_context_int -> direct_callsite_int

    method has_indirect_callsite: program_context_int -> bool
    method has_direct_callsite: program_context_int -> bool

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

(** {1 Return sites}*)


class type returnsite_int =
  object

    method add_postcondition: xpredicate_t -> unit
    method add_preservation_condition: globalvar_contract_int -> unit
    method add_inequality_condition:
             globalvar_contract_int -> binop -> int -> unit

    method get_exp: exp
    method get_context: program_context_int
    method get_location: location
    method get_spos: proof_obligation_int list

    method has_exp: bool

    method write_xml: xml_element_int -> unit
  end


class type returnsite_manager_int =
  object

    method add_return: location -> program_context_int -> exp option -> unit
    method create_contract_proof_obligations: unit

    method get_spos: proof_obligation_int list
    method get_postconditions: xpredicate_t list

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit
  end


(** {1 Supporting proof obligations}*)

class type spo_manager_int =
  object

    method add_local_spo:
             location -> program_context_int -> po_predicate_t -> unit
    method add_direct_call:
             location
             -> program_context_int
             -> ?header:string
             -> varinfo
             -> exp list
             -> unit
    method add_indirect_call:
             location
             -> program_context_int
             -> ?header:string
             -> exp
             -> exp list
             -> unit
    method add_return: location -> program_context_int -> exp option -> unit
    method create_contract_proof_obligations: unit

    method get_spo: int -> proof_obligation_int
    method get_spos: proof_obligation_int list
    method get_callsite_manager: callsite_manager_int

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


(** {1 Api assumptions}*)

class type api_assumption_int =
object

  method add_dependent_ppo: int -> unit
  method add_dependent_spo: int -> unit

  (* accessors *)
  method index: int
  method get_predicate: po_predicate_t
  method get_dependent_ppos: int list
  method get_dependent_spos: int list
  method toPretty: pretty_t

  (* xml *)
  method write_xml: xml_element_int -> unit

end


class type contract_assumption_int =
object

  method add_dependent_ppo: int -> unit
  method add_dependent_spo: int -> unit

  (* accessors *)
  method index: int
  method get_callee: int
  method get_xpredicate: xpredicate_t
  method get_dependent_ppos: int list
  method get_dependent_spos: int list
  method toPretty: pretty_t

  (* predicates *)
  method has_callee: bool
  method is_global: bool

  (* xml *)
  method write_xml: xml_element_int -> unit
end



class type postcondition_request_int =
object ('a)

  method add_dependent_ppo: int -> unit
  method add_dependent_spo: int -> unit

  (* accessors *)
  method get_request: postrequest_t
  method get_postcondition: xpredicate_t
  method get_callee: int                    (* fvid of callee *)
  method get_dependent_ppos: int list
  method get_dependent_spos: int list
  method toPretty: pretty_t

  (* xml *)
  method write_xml: xml_element_int -> unit

end


class type global_assumption_int =
object ('a)

  method add_dependent_ppo: int -> unit
  method add_dependent_spo: int -> unit

  (* accessors *)
  method index: int
  method get_predicate : xpredicate_t
  method get_dependent_ppos: int list
  method get_dependent_spos: int list
  method toPretty: pretty_t

  (* xml *)
  method write_xml: xml_element_int -> unit

end


class type ds_assumption_int =
object ('a)

  method add_dependents: int list -> unit

  (* accessors *)
  method index : int
  method get_predicate: po_predicate_t
  method get_dependent_ppos: int list
  method get_dependent_spos: int list

  (* xml *)
  method write_xml: xml_element_int -> unit

end

(** {1 Assignments}*)

class type global_assignment_int =
object ('a)

  (* accessors *)
  method get_lhs: lval
  method get_rhs: exp
  method get_location : location

  (* predicates *)
  method is_lhs_global: cfundeclarations_int -> bool
  method is_rhs_global: cfundeclarations_int -> bool

  (* xml *)
  method write_xml: xml_element_int -> unit

end


class type field_assignment_int =
object ('a)

  (* accessors *)
  method get_id : string
  method get_rhs: exp
  method get_location: location
  method get_context : program_context_int
  method get_field_name   : string
  method get_comp_key : int

  (* xml *)
  method write_xml: xml_element_int -> unit

  (* printing *)
  method toPretty: pretty_t
end


class type assignment_manager_int =
  object

    method add_assignment:
             string -> location -> program_context_int -> lval -> exp -> unit

    (* xml *)
    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

  end


(** {1 Function api}*)

class type function_api_int =
object

  (* setters *)
  method add_api_assumption :
           ?isfile:bool -> ?isglobal:bool -> ?ppos:int list -> ?spos:int list
           -> po_predicate_t -> po_predicate_t option
  method add_global_assumption_request:
           ?ppos:int list -> ?spos:int list -> xpredicate_t -> unit
  method add_postcondition_assumption:
           ?ppos:int list -> ?spos:int list -> int -> xpredicate_t -> unit
  method add_global_assumption:
           ?ppos:int list -> ?spos:int list -> xpredicate_t -> unit
  method add_postcondition_request:
           ?ppos:int list -> ?spos:int list -> int -> xpredicate_t -> unit
  method add_postcondition_guarantee: xpredicate_t -> unit
  method add_library_call: string -> string -> unit
  method add_missing_summary: string -> unit
  method add_unevaluated: po_predicate_t -> int -> unit
  method add_contract_precondition: cfundeclarations_int -> int -> unit
  method add_contract_condition_failure: string -> string -> unit

  (* accessors *)
  method get_api_assumptions   : api_assumption_int list
  method get_contract_assumptions: contract_assumption_int list
  method get_assumption_requests: global_assumption_int list
  method get_postcondition_requests: postcondition_request_int list
  method get_postcondition_guarantees: xpredicate_t list
  method get_library_call_names: string list
  method get_library_calls: (string * string) list
  (** header name, function name *)

  method get_api_assumption   : int -> api_assumption_int

  (* xml *)
  method write_xml: xml_element_int -> unit
  method read_xml : xml_element_int -> unit

end


class type function_api_manager_int =
object

  method initialize_cfile  : file -> unit

  method set_function: string -> int -> unit

  method get_current_function_api: function_api_int
  method get_function_api: int -> function_api_int

  method has_function_api: int -> bool

  method save: unit
end


(** {1 User assumptions}*)


class type user_assumptions_int =
  object
    method get: int -> string
    method has: int -> bool
    method has_assumptions: bool
    method read_xml: xml_element_int -> unit
  end

(** {1 Proof scaffolding}*)

class type proof_scaffolding_int =
  object

    method reset: unit

    method initialize_pod: string -> cfundeclarations_int -> unit
    method retrieve_contract_preconditions:
             cfundeclarations_int -> string -> unit

    method get_function_api: string -> function_api_int

    method get_ppo_manager: string -> ppo_manager_int

    method get_spo_manager: string -> spo_manager_int

    method get_proof_obligations: string -> proof_obligation_int list

    method get_call_count: string -> int
    method get_direct_callsites: string -> direct_callsite_int list
    method get_indirect_callsites: string -> indirect_callsite_int list
    method get_direct_callsite:
             string -> program_context_int -> direct_callsite_int
    method get_indirect_callsite:
             string -> program_context_int -> indirect_callsite_int

    method has_direct_callsite: string -> program_context_int -> bool
    method has_indirect_callsite: string -> program_context_int -> bool

    method write_xml_api: xml_element_int -> string -> unit
    method read_xml_api : xml_element_int -> string -> unit

    method write_xml_ppos: xml_element_int -> string -> unit
    method read_xml_ppos : xml_element_int -> string -> unit

    method write_xml_spos: xml_element_int -> string -> unit
    method read_xml_spos : xml_element_int -> string -> unit

    method write_xml_pod: xml_element_int -> string -> unit
    method read_xml_pod:
             xml_element_int -> string -> cfundeclarations_int -> unit

  end


(** {1 Invariants}*)


type address_type_t = Heap | Stack | External


type non_relational_value_t =
  | FSymbolicExpr of xpr_t
  | FSymbolicBound of bound_type_t * xpr_t list list
  | FIntervalValue of numerical_t option * numerical_t option
  | FBaseOffsetValue of
      address_type_t * xpr_t * numerical_t option * numerical_t option * bool
  (** can be null *)

  | FRegionSet of symbol_t list
  | FInitializedSet of symbol_t list
  | FPolicyStateSet of symbol_t list


type invariant_fact_t =
  | Unreachable of string (* domain that signals unreachability *)
  | NonRelationalFact of variable_t * non_relational_value_t
  | ParameterConstraint of xpr_t


(** an invariant can be used if its assumptions are currently active *)
class type invariant_int =
  object ('a)
    method index: int
    method compare: 'a -> int
    method compare_lb: 'a -> int
    method compare_ub: 'a -> int
    method get_fact: invariant_fact_t
    method get_regions: symbol_t list
    method get_preservation_ids: int list
    method applies_to_var: ?var_equal:bool -> variable_t -> bool
    method in_domain: string -> bool
    method is_unreachable: string option
    method is_interval: bool
    method is_symbolic_bound: bool
    method is_regions: bool
    method is_smaller: 'a -> bool
    method indirect_call_return_value: string option
    method direct_call_return_value: string option
    method const_value: numerical_t option
    method lower_bound: numerical_t option
    method upper_bound: numerical_t option
    method lower_bound_xpr: xpr_t option
    method upper_bound_xpr: xpr_t option
    method lower_bound_xpr_alternatives: xpr_t list option
    method upper_bound_xpr_alternatives: xpr_t list option
    method pepr_lower_bound: xpr_t list list option
    method pepr_upper_bound: xpr_t list list option
    method expr: xpr_t option
    method symbolic_expr: xpr_t option
    method base_offset_value:
             (address_type_t
              * xpr_t
              * numerical_t option
              * numerical_t option
              * bool) option (* can be null *)
    method write_xml: xml_element_int -> unit
    method value_to_pretty: pretty_t
    method toPretty: pretty_t
  end


class type location_invariant_int =
  object

    (* setters *)
    method add_fact: invariant_fact_t -> unit
    method get_invariants: invariant_int list
    method get_sorted_invariants:
             (invariant_int -> invariant_int -> int) -> invariant_int list
    method get_var_invariants: variable_t -> invariant_int list
    method get_parameter_constraints: invariant_int list

    (* xml *)
    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    (* printing *)
    method toPretty: pretty_t
  end


class type invariant_io_int =
  object

    method add_fact: program_context_int -> invariant_fact_t -> unit
    method get_invariant: int -> invariant_int

    method get_location_invariant: program_context_int -> location_invariant_int

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


class type invdictionary_int =
  object

    method xd: xprdictionary_int
    method fdecls: cfundeclarations_int

    method index_non_relational_value: non_relational_value_t -> int
    method index_invariant_fact: invariant_fact_t -> int

    method get_non_relational_value: int -> non_relational_value_t
    method get_invariant_fact: int -> invariant_fact_t

    method write_xml_non_relational_value:
             ?tag:string -> xml_element_int -> non_relational_value_t -> unit
    method read_xml_non_relational_value:
             ?tag:string -> xml_element_int -> non_relational_value_t

    method write_xml_invariant_fact:
             ?tag:string -> xml_element_int -> invariant_fact_t -> unit
    method read_xml_invariant_fact:
             ?tag:string -> xml_element_int -> invariant_fact_t

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t

  end


type data_structure_assumption_t =
| DNotNull of string
| DUpperBound of string
| DLowerBound of string
| DValidMem of string
| DInitialized of string
| DEquals of string * int (** field is initialized with value *)


class type data_structure_invariant_int =
object
  method has_assumption:
           file_environment_int -> po_predicate_t -> string option
end

class type data_structure_invariants_int =
object
  method has_assumption:
           file_environment_int -> po_predicate_t -> string option
end

(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
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
open CHNumerical
open CHPretty

(* xprlib *)
open XprTypes

(* chutil *)
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes


(** {1 Machine sizes}

    Adapted from the automatically generated machdep in CIL
 *)

type machine_sizes_t = {
  sizeof_short : xpr_t;
  sizeof_int   : xpr_t;

  sizeof_bool  : xpr_t;
  sizeof_long  : xpr_t;

  sizeof_longlong : xpr_t;
  sizeof_ptr      : xpr_t;
  sizeof_enum     : xpr_t;
  sizeof_float    : xpr_t;
  sizeof_double   : xpr_t;

  sizeof_longdouble  : xpr_t;
  sizeof_void        : xpr_t;
  sizeof_fun         : xpr_t;

  alignof_short  : xpr_t;
  alignof_int    : xpr_t;
  alignof_bool   : xpr_t;
  alignof_long   : xpr_t;

  alignof_longlong  : xpr_t;
  alignof_ptr       : xpr_t;
  alignof_enum      : xpr_t;
  alignof_float     : xpr_t;

  alignof_double    : xpr_t;
  alignof_longdouble: xpr_t;
  alignof_str       : xpr_t;
  alignof_fun       : xpr_t;
  alignof_aligned   : xpr_t;
}

type max_sizes_t = {
  sizeof_int  : int;
  sizeof_float: int;
  sizeof_void : int;
  sizeof_ptr  : int;
  sizeof_fun  : int;
  sizeof_enum : int
  }

class type type_range_int =
  object
    method min: numerical_t
    method max: numerical_t
  end

class type ['a] sumtype_string_converter_int =
  object
    method to_string: 'a -> string
    method from_string: string -> 'a
  end


(** {1 Dictionary}*)

type constantstring = string * bool * int

class type cdictionary_int =
  object

    method reset: unit

    method index_attrparam: attrparam -> int
    method index_attribute: attribute -> int
    method index_attributes: attributes -> int
    method index_attrparam: attrparam -> int
    method index_constant: constant -> int
    method index_exp: exp -> int
    method index_funarg: funarg -> int
    method index_funargs: funarg list -> int
    method index_lhost: lhost -> int
    method index_lval: lval -> int
    method index_opt_lval: lval option -> int
    method index_offset: offset -> int
    method index_typ: typ -> int
    method index_typsig: typsig -> int
    method index_string: string -> int

    method get_attrparam: int -> attrparam
    method get_attribute: int -> attribute
    method get_attributes: int -> attributes
    method get_attrparam: int -> attrparam
    method get_constant: int -> constant
    method get_exp: int -> exp
    method get_funarg: int -> funarg
    method get_funargs: int -> funarg list
    method get_lhost: int -> lhost
    method get_lval: int -> lval
    method get_opt_lval: int -> lval option
    method get_offset: int -> offset
    method get_typ: int -> typ
    method get_typsig: int -> typsig
    method get_string: int -> string

    method read_xml_attributes: ?tag:string -> xml_element_int -> attributes

    method write_xml_exp: ?tag:string -> xml_element_int -> exp -> unit
    method write_xml_exp_opt: ?tag:string -> xml_element_int -> exp option -> unit
    method read_xml_exp : ?tag:string -> xml_element_int -> exp
    method read_xml_exp_opt: ?tag:string -> xml_element_int -> exp option

    method read_xml_funarg_list: ?tag:string -> xml_element_int -> funarg list

    method write_xml_lval: ?tag:string -> xml_element_int -> lval -> unit
    method read_xml_lval : ?tag:string -> xml_element_int -> lval
    method read_xml_lval_opt: ?tag:string -> xml_element_int -> lval option

    method write_xml_offset: ?tag:string -> xml_element_int -> offset -> unit
    method read_xml_offset: ?tag:string -> xml_element_int -> offset

    method write_xml_typ : ?tag:string -> xml_element_int -> typ -> unit
    method read_xml_typ  : ?tag:string -> xml_element_int -> typ

    method write_xml_string: ?tag:string -> xml_element_int -> string -> unit
    method read_xml_string : ?tag:string -> xml_element_int -> string

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

    method toPretty : pretty_t

  end

(** {1 Declarations} *)

type enumitem = string * exp * location

class type cdeclarations_int =
  object

    method reset: unit

    method index_init: init -> int
    method index_offset_init: offset * init -> int
    method index_typeinfo: typeinfo -> int
    method index_varinfo: varinfo -> int
    method index_fieldinfo: fieldinfo -> int
    method index_compinfo: compinfo -> int
    method index_enumitem: enumitem -> int
    method index_enuminfo: enuminfo -> int
    method index_location: location -> int
    method index_filename: string -> int

    method get_init: int -> init
    method get_offset_init: int -> offset * init
    method get_typeinfo: int -> typeinfo
    method get_varinfo: int -> varinfo
    method get_fieldinfo: int -> fieldinfo
    method get_compinfo: int -> compinfo
    method get_enumitem: int -> enumitem
    method get_enuminfo: int -> enuminfo
    method get_location: int -> location
    method get_filename: int -> string

    method get_opaque_varinfos: varinfo list
    method get_varinfo_by_name: string -> varinfo
    method has_varinfo_by_name: string -> bool

    method write_xml_init: ?tag:string -> xml_element_int -> init -> unit
    method read_xml_init : ?tag:string -> xml_element_int -> init

    method write_xml_typeinfo: ?tag:string -> xml_element_int -> typeinfo -> unit
    method read_xml_typeinfo : ?tag:string -> xml_element_int -> typeinfo

    method write_xml_varinfo: ?tag:string -> xml_element_int -> varinfo -> unit
    method read_xml_varinfo : ?tag:string -> xml_element_int -> varinfo

    method write_xml_fieldinfo: ?tag:string -> xml_element_int -> fieldinfo -> unit
    method read_xml_fieldinfo : ?tag:string -> xml_element_int -> fieldinfo

    method write_xml_compinfo: ?tag:string -> xml_element_int -> compinfo -> unit
    method read_xml_compinfo : ?tag:string -> xml_element_int -> compinfo

    method write_xml_enumitem: ?tag:string -> xml_element_int -> enumitem -> unit
    method read_xml_enumitem : ?tag:string -> xml_element_int -> enumitem

    method write_xml_enuminfo: ?tag:string -> xml_element_int -> enuminfo -> unit
    method read_xml_enuminfo : ?tag:string -> xml_element_int -> enuminfo

    method write_xml_location: ?tag:string -> xml_element_int -> location -> unit
    method read_xml_location : ?tag:string -> xml_element_int -> location

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

    method toPretty : pretty_t

  end


(** {1 Context} *)

class type cfg_context_int =
  object ('a)
    method compare: 'a -> int
    method index: int
    method equal: 'a -> bool

    method pop: 'a

    method add_instr: int -> 'a
    method add_stmt: int -> 'a
    method add_return: 'a
    method add_if_expr: 'a
    method add_if_then: 'a
    method add_if_else: 'a
    method add_switch_expr: 'a
    method add_loop: 'a
    method add_goto: 'a

    method get_context: int list
    method get_complexity: int

    method is_return_context: bool

    method write_xml: xml_element_int -> unit
    method to_string: string
    method toPretty: pretty_t
  end


class type exp_context_int =
  object ('a)
    method index: int
    method compare: 'a -> int

    method add_var: 'a
    method add_arg: int -> 'a (* index of argument, starting at 1 *)
    method add_args: int list -> 'a   (* list of argument indices, starting at 1 *)
    method add_addrof: 'a
    method add_binop: int -> 'a   (* first or second operator *)
    method add_cast: 'a
    method add_field_offset: string -> 'a   (* name of the field *)
    method add_lhs: 'a
    method add_rhs: 'a
    method add_ftarget: 'a
    method add_unop: 'a
    method add_index: 'a
    method add_index_offset: 'a
    method add_lval: 'a
    method add_mem: 'a
    method add_deref_read: 'a
    method add_question:  int -> 'a  (* first, second, or third operator *)
    method add_startof: 'a

    method get_context: int list
    method get_complexity: int

    method write_xml: xml_element_int -> unit
    method to_string: string
    method toPretty: pretty_t
  end


class type program_context_int =
  object ('a)

    method compare: 'a -> int
    method construct: cfg_context_int -> exp_context_int -> 'a
    method project_on_cfg: 'a

    method add_instr: int -> 'a
    method add_stmt: int -> 'a
    method add_return: 'a
    method add_if_expr: 'a
    method add_if_then: 'a
    method add_if_else: 'a
    method add_switch_expr: 'a
    method add_loop: 'a
    method add_goto: 'a

    method add_var: 'a
    method add_arg: int -> 'a (* index of argument, starting at 1 *)
    method add_args: int list -> 'a   (* list of argument indices, starting at 1 *)
    method add_addrof: 'a
    method add_binop: int -> 'a   (* first or second operator *)
    method add_cast: 'a
    method add_field_offset: string -> 'a   (* name of the field *)
    method add_lhs: 'a
    method add_rhs: 'a
    method add_ftarget: 'a
    method add_unop: 'a
    method add_index: 'a
    method add_index_offset: 'a
    method add_lval: 'a
    method add_mem: 'a
    method add_deref_read: 'a
    method add_question:  int -> 'a  (* first, second, or third operator *)
    method add_startof: 'a

    method pop: 'a

    method get_cfg_context: cfg_context_int
    method get_exp_context: exp_context_int

    method is_return_context: bool

    method to_string: string
    method toPretty: pretty_t

  end


class type ccontexts_int =
  object

    method reset: unit

    method index_context: program_context_int -> int
    method get_context: int -> program_context_int

    method write_xml_context:
             ?tag:string -> xml_element_int -> program_context_int -> unit
    method read_xml_context:
             ?tag:string -> xml_element_int -> program_context_int

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

(** {1 Environments} *)

class type file_environment_int =
  object

    method initialize: file -> unit

    (* accessors *)
    method get_globalvar: int -> varinfo
    method get_globalvars: varinfo list
    method get_globalvar_by_name: string -> varinfo
    method get_comp: int -> compinfo
    method get_enum: string -> enuminfo
    method get_type: string -> typ
    method get_field_type: int -> string -> typ
    method get_field_info: int -> string -> fieldinfo
    method get_type_unrolled: typ -> typ
    method get_external_header: string -> string
    method get_application_functions: varinfo list

    method get_machine_sizes: machine_sizes_t

    (* predicates *)
    method has_globalvar: int -> bool
    method is_external_function: string -> bool
    method has_external_header: string -> bool
    method is_application_function: int -> bool
  end

(** {1 Transformers} *)

class type exp_transformer_int =
object
  method transform_exp   : exp -> exp
  method transform_type  : typ -> typ
  method transform_lval  : lval -> lval
  method transform_lhost : lhost -> lhost
  method transform_offset: offset -> offset
end

class type exp_walker_int =
object
  method walk_exp   : exp -> unit
  method walk_type  : typ -> unit
  method walk_lval  : lval -> unit
  method walk_lhost : lhost -> unit
  method walk_offset: offset -> unit
end


(** {1 Function summary} *)

type api_parameter_t =
  | ParFormal of int           (* starting at 1 *)
  | ParGlobal of string

type s_offset_t =
  | ArgNoOffset
  | ArgFieldOffset of string * s_offset_t
  | ArgIndexOffset of numerical_t * s_offset_t

type s_term_t =
  | ArgValue of api_parameter_t *  s_offset_t
  | LocalVariable of string
  | ReturnValue
  | NamedConstant of string
  | NumConstant of numerical_t
  | IndexSize of s_term_t
  | ByteSize of s_term_t
  | ArgAddressedValue of s_term_t * s_offset_t
  | ArgNullTerminatorPos of s_term_t
  | ArgSizeOfType of s_term_t
  | ArithmeticExpr of binop * s_term_t * s_term_t
  | FormattedOutputSize of s_term_t
  | Region of s_term_t     (* memory region that is pointed to by s_term *)
  | RuntimeValue
  | ChoiceValue of s_term_t option * s_term_t option (* free to choose between bounds *)

type xpredicate_t =      (* predicate used in representation of external conditions *)
  | XAllocationBase of s_term_t         (* term points to start of allocated region that can be freed *)
  | XControlledResource of string * s_term_t   (* term is not/must not be tainted *)
  | XBlockWrite of s_term_t * s_term_t  (* unstructured write of bytes to pointed adress with given length *)
  | XBuffer of s_term_t * s_term_t  (* term points to a memory region with at least t2 bytes after pointer *)
  | XConfined of s_term_t               (* pointer expression is out of scope without leaking references *)
  | XConstTerm of s_term_t              (* pointed to term is not modified *)
  | XFormattedInput of s_term_t         (* term corresponds to argument that provides the format string *)
  | XFalse                              (* always false, used as post condition *)
  | XFreed of s_term_t                  (* term pointed to is freed *)
  | XFunctional                         (* function has no observable side effects *)
  | XInitialized of s_term_t            (* lval denoted is initialized *)
  | XInitializedRange of s_term_t * s_term_t  (* term pointed to is initialized for t2 length *)
  | XInputFormatString of s_term_t      (* term points to scanf format string *)
  | XInvalidated of s_term_t            (* term pointed to may not be valid any more *)
  | XNewMemory of s_term_t
  (* term points to newly allocated memory (since the start of the function), stack or heap *)
  | XStackAddress of s_term_t           (* term points to stack memory *)
  | XHeapAddress of s_term_t            (* term points to heap memory *)
  | XGlobalAddress of s_term_t          (* term points to global memory *)
  | XNoOverlap of s_term_t * s_term_t   (* the two pointed-to memory regions do not overlap *)
  | XNotNull of s_term_t                (* term is not null *)
  | XNull of s_term_t                   (* term is null *)
  | XNotZero of s_term_t                (* term is not zero *)
  | XNonNegative of s_term_t            (* term is not negative  *)
  | XNullTerminated of s_term_t         (* term pointed to is null-terminated *)
  | XOutputFormatString of s_term_t     (* term points to printf format string *)
  | XPreservesAllMemory                 (* function does not free any external memory *)
  | XPreservesAllMemoryX of s_term_t list (* function does not free any external memory except given terms *)
  | XPreservesMemory of s_term_t        (* function does not free pointed to memory *)
  | XPreservesValue of s_term_t         (* function does not modify the value of s_term *)
  | XPreservesNullTermination           (* function does not strip null-terminating bytes *)
  | XPreservesValidity of s_term_t      (* validity of pointed to resource is maintained *)
  | XRelationalExpr of binop * s_term_t * s_term_t
  | XRepositioned of s_term_t           (* term pointed to my be freed and reassigned *)
  | XRevBuffer of s_term_t * s_term_t   (* term points to memory region with at least t2 bytes before pointer *)
  | XTainted of s_term_t * s_term_t option * s_term_t option
         (* value of term is externally controlled with optional lower and upper bound *)
  | XUniquePointer of s_term_t          (* pointer reference is the only one *)
  | XValidMem of s_term_t               (* pointed-to memory has not been freed (at time of delivery) *)
(* policy-related predicates *)
  | XPolicyPre of s_term_t * string * string list  (* the term has to be in one of the given states *)
  | XPolicyValue of s_term_t * string * string option
  (* the term is a newly created policy value and optionally makes a first transition *)
  | XPolicyTransition of s_term_t * string * string (* the term transitions according to a named transition
                                                       in the policy *)

type postrequest_t = int * xpredicate_t  (* fvid of callee *)

type postassume_t = int * xpredicate_t (* fvid of callee *)

type summary_annotation_t  =
  | ExternalCondition of string
  | EnvironmentCondition of string
  | UnmodeledArgumentDependency of string
  | NoAnnotation

type annotated_xpredicate_t = (xpredicate_t * summary_annotation_t)

(* data structure condition *)
type ds_condition_t = {
    dsc_name: string;
    dsc_ckey : int;
    dsc_fields : xpredicate_t list
  }

type function_summary_t = {
    fs_fname : string;
    fs_domainref: (string * string) option; (* specialized reasoning domain *)
    fs_params : (string * int) list;
    fs_preconditions: annotated_xpredicate_t list;
    fs_postconditions: annotated_xpredicate_t list;
    fs_error_postconditions: annotated_xpredicate_t list;
    fs_sideeffects: annotated_xpredicate_t list
  }


class type function_summary_library_int =
object
  method add_summary_jar: string -> unit
  method read_function_summary_string: string -> string -> unit
  method read_xml_substitute_summary:
           xml_element_int -> string -> unit (* from globaldefs.xml contract *)
  method get_summary : string -> function_summary_t
  method has_summary : string -> string -> bool
  method has_builtin_summary: string -> bool
  method statistics_to_pretty: pretty_t
end


(** {1 Interface dictionary} *)

class type interface_dictionary_int =
  object

    method reset: unit

    method index_api_parameter: api_parameter_t -> int
    method index_s_offset: s_offset_t -> int
    method index_s_term: s_term_t -> int
    method index_xpredicate: xpredicate_t -> int
    method index_postrequest: postrequest_t -> int
    method index_postassume: postassume_t -> int
    method index_ds_condition: ds_condition_t -> int

    method get_api_parameter: int -> api_parameter_t
    method get_s_offset: int -> s_offset_t
    method get_s_term: int -> s_term_t
    method get_xpredicate: int -> xpredicate_t
    method get_postrequest: int -> postrequest_t
    method get_postassume: int -> postassume_t
    method get_ds_condition: int -> ds_condition_t

    method write_xml_api_parameter:
             ?tag:string -> xml_element_int -> api_parameter_t -> unit
    method read_xml_api_parameter:
             ?tag:string -> xml_element_int -> api_parameter_t

    method write_xml_s_term: ?tag:string -> xml_element_int -> s_term_t -> unit
    method read_xml_s_term: ?tag:string -> xml_element_int -> s_term_t

    method write_xml_xpredicate:
             ?tag:string -> xml_element_int -> xpredicate_t -> unit
    method read_xml_xpredicate:
             ?tag:string -> xml_element_int -> xpredicate_t

    method write_xml_postrequest:
             ?tag:string -> xml_element_int -> postrequest_t -> unit

    method read_xml_postrequest:
             ?tag:string -> xml_element_int -> postrequest_t

    method write_xml_ds_condition:
             ?tag:string -> xml_element_int -> ds_condition_t -> unit

    method read_xml_ds_condition:
             ?tag:string -> xml_element_int -> ds_condition_t

    method write_xml: xml_element_int -> unit
    method read_xml : xml_element_int -> unit

    method toPretty: pretty_t

  end


(** {1 Contracts} *)

type contract_instr_t =
  SetVar of int * s_term_t * s_term_t        (* line, lhs, rhs *)

type contract_note_t = {
    cn_tag: string;
    cn_prq: string;
    cn_txt: string
  }

class type function_contract_int =
  object
    method add_postcondition: xpredicate_t -> unit
    method add_precondition: xpredicate_t -> unit
    method get_name: string
    method get_postcondition_ixs: int list           (* xpredicate indices *)
    method get_precondition_ixs: int list            (* xpredicate indices *)
    method get_sideeffect_ixs: int list              (* xpredicate indices *)
    method get_postconditions: xpredicate_t list
    method get_preconditions: xpredicate_t list
    method get_sideeffects: xpredicate_t list
    method get_notes: contract_note_t list
    method get_tagged_notes: string -> contract_note_t list
    method get_instrs: int -> contract_instr_t list
    method read_xml: xml_element_int -> string list -> unit
    method ignore_function: bool    (* function stated to originate from header file *)
    method has_instrs: int -> bool
    method write_xmlx: xml_element_int -> unit
    method postconditions_to_pretty: pretty_t
    method preconditions_to_pretty: pretty_t
    method toPretty: pretty_t
  end

type contract_global_var_t = {
    cgv_name: string;
    cgv_value: int option;
    cgv_lb: int option;
    cgv_ub: int option;
    cgv_static: bool;
    cgv_const: bool;
    cgv_notnull: bool;
    cgv_initialized_fields: string list
  }


class type file_contract_int =
  object
    method reset: unit
    method add_function_contract: string -> string list -> unit
    method add_precondition: string -> xpredicate_t -> unit
    method get_global_variables: contract_global_var_t list
    method get_function_contract: string -> function_contract_int
    method get_gv_lower_bound: string -> int option
    method get_gv_upper_bound: string -> int option
    method has_function_contract: string -> bool
    method ignore_function: string -> bool
    method gv_is_not_null: string -> bool
    method gv_field_is_initialized: string -> string -> bool
    method read_xml: xml_element_int -> unit
    method write_xmlx: xml_element_int -> unit
    method toPretty: pretty_t
  end


class type global_contract_int =
  object
    method is_nofree: bool
    method read_xml: xml_element_int -> unit
  end


(** {1 System settings} *)


type analysis_level_t =
  | UndefinedBehavior
  (** only indicate undefined behavior (Red) *)

  | ImplementationDefinedBehavior
  (** indicate undefined behavior and implementation defined behavior
      (Red,Purple) (default) *)

  | ValueWrapAround
  (** indicate undefined behavior, implementation-defined behavior, and value
      wrap around of unsigned integers (Red, Purple, Blue) *)


(** Paths and analysis options*)
class type system_settings_int =
  object

    (** {1 Paths}*)

    (** {2 Project path}
        The project path is the path to the top-level directory of the project.
        In case of a single file this is the directory in which the c source
        file resides. In case of a multi-file project this is the directory in
        which the Makefile resides.*)

    method set_projectpath: string -> unit
    method get_projectpath: string

    (** {2 Project name}
        The project name determines the name under which the analysis results
        are stored.*)

    method set_projectname: string -> unit
    method get_projectname: string

    (** {2 C File path}
        The cfile path is the relative path from the project path to the directory
        in which the source file resides. In case of a single file, the file path
        is the empty string.*)

    method set_cfilepath: string -> unit
    method get_cfilepath: string
    method has_cfilepath: bool

    (** {2 C File name}
        The cfilename is the base name of the source file without extension.*)

    method set_cfilename: string -> unit
    method get_cfilename: string

    (** {2 Target path}
        The target path is the (absolute) path to the directory in which the
        parse/analysis results are to be stored.*)

    method set_targetpath: string -> unit
    method get_targetpath: string

    (** {2 Contract path}
        The contract path is the (absolute) path to the directory in which
        contract files reside. This is currently not used and under
        reconsideration.*)
    method set_contractpath: string -> unit
    method get_contractpath: string
    method has_contractpath: bool

    (** {1 Analysis level}
        Currently supports three levels:
        - undefined behavior: only check conditions that may lead to undefined
            behavior
        - implementation-defined behavior: also check conditions that may arise
            because of implementation defined behavior
        - value wrap around: also flag potential value wrap around of unsigned
            integers.*)

    method set_analysis_level: analysis_level_t -> unit
    method is_undefined_only: bool
    method is_implementation_defined: bool
    method is_value_wrap_around: bool

    (** {1 Other settings*)

    method set_verbose: bool -> unit
    method verbose: bool

    method set_filterabspathfiles: bool -> unit
    method filterabspathfiles: bool

    method set_wordsize: int -> unit
    method get_wordsize: int
    method has_wordsize: bool

    method set_use_unreachability: unit
    method use_unreachability: bool

  end

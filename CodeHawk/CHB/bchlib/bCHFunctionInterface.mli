(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* chutil *)
open CHFormatStringParser
open CHXmlDocument

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


(** The externally provided or internally inferred function api of an assembly
    function.

    The function interface provides function type signatures ([fts]) for all
    assembly functions, including dynamically linked library functions.

    An externally provided [fts] (e.g., via a header or function summary library)
    is generally taken as authorative (binding) and not affected by analysis
    results collected. An externally provided fts is distinguished as such in the
    function interface by the [bctype] field, which is the function type
    provided. In all other cases this field is [None].

    For an externally provided [fts] the parameter locations in the [fts]
    parameters are constructed upon [fts] input (after parsing the header
    file or xml function summary) and these locations stay with the [fts]
    parameters, that is, they are saved in and reloaded from the saved
    function-info ([finfo]).

    When no [fts] is provided, an [fts] is inferred from analysis results,
    from initial register value and initial stack values. Since these
    results provide individual parameter locations rather than actual [fts]
    parameters (for example, the parameter index cannot be directly inferred
    from a single parameter location), these locations are saved in the
    parameter_locations field of the function interface.

    When an [fts] is requested the [fts] in the type_signature field is
    returned only if the [fts] is externally provided. In all other cases
    an [fts] is constructed on the fly from the parameter_locations available
    at that time (potentially filled in with missing parameters). This [fts],
    however, is not saved, and thus the next time an [fts] is requested it may
    be different (typically, because more analysis results may have become
    available, thus allowing a more precise [fts]).

    In case an [fts] is externally provided for an application function,
    parameter locations are still collected based on analysis results. A check
    can be performed if the inferred [fts] is consistent with the provided [fts].
*)


(** {1 Creation}*)


(** Returns a default function_interface based on limited information available.

    The default values for the various optional parameters are:
    - [cc] (calling convention): "cdecl"
    - [adj] (stack adjustment, stdcall only): 0
    - [bctype] (externally provided function type): [None]
    - [bc_returntype] (only accepted if bctype is not [None]: [t_unknown]
    - [bc_fts_parameters] (only accepted if bctype is not [None]): []
    - [varargs] (does the function have varargs): [false]
    - [locations] (list of inferred parameter locations): []
    - [returntypes] (list of inferred return types): []
 *)
val default_function_interface:
  ?cc:string
  -> ?adj:int
  -> ?bctype:btype_t option
  -> ?bc_returntype:btype_t
  -> ?bc_fts_parameters: fts_parameter_t list
  -> ?varargs:bool
  -> ?locations:parameter_location_t list
  -> ?returntypes: btype_t list
  -> ?lhsname: string option
  -> string
  -> function_interface_t


val demangled_name_to_function_interface: demangled_name_t -> function_interface_t


val bfuntype_to_function_interface: string -> btype_t -> function_interface_t


val bvarinfo_to_function_interface: bvarinfo_t -> function_interface_t


(** {1 Modification}*)

(** [set_function_interface_returntype fintf ty] returns a new function interface
    identical to [fintf] except for the returntype, which is set to [ty].*)
val set_function_interface_returntype:
  function_interface_t -> btype_t -> function_interface_t


(** [fintf_add_stack_adjustment fintf adj] returns a new function interface
    identical to [fintf] except for the stackadjustment and calling convention,
    which are set to [adj] and 'stdcall'. *)
val fintf_add_stack_adjustment:
  function_interface_t -> int -> function_interface_t


val add_function_register_parameter_location:
  function_interface_t -> register_t -> btype_t -> int -> function_interface_t


val add_function_stack_parameter_location:
  function_interface_t -> int -> btype_t -> int -> function_interface_t


val add_function_global_parameter_location:
  function_interface_t
  -> doubleword_int
  -> btype_t
  -> int
  -> function_interface_t


val add_format_spec_parameters:
  function_interface_t -> argspec_int list -> function_interface_t


(** Modifies the types of the function type signature according to a type
transformer (used only for A/W types in windows libraries)*)
val modify_function_interface:
  type_transformer_t -> string -> function_interface_t -> function_interface_t

(** {1 Accessors}*)

val get_fintf_name: function_interface_t -> string

val get_fintf_fts: function_interface_t -> function_signature_t

val get_fts_parameters: function_interface_t -> fts_parameter_t list

val get_fts_returntype: function_interface_t -> btype_t

val get_fts_stack_adjustment: function_interface_t -> int option

val get_stack_parameters: function_interface_t -> fts_parameter_t list

val get_register_parameters: function_interface_t -> fts_parameter_t list

val get_register_parameter_for_register:
  function_interface_t -> register_t -> fts_parameter_t option

val get_stack_parameter:
  function_interface_t -> int -> fts_parameter_t (* index starts at 1 *)

val get_stack_parameter_at_offset:
  function_interface_t -> int -> fts_parameter_t option

val get_stack_parameter_name :
  function_interface_t -> int -> string          (* index starts at 1 *)

val get_stack_parameter_names: function_interface_t -> (int * string) list

val get_stack_parameter_count: function_interface_t -> int


(** {1 Predicates}*)

val has_fmt_parameter: function_interface_t -> bool

val get_fmt_parameter_index: function_interface_t -> int

(** {1 Printing}*)

val function_interface_to_prototype_string:
  ?fullname:string option -> function_interface_t -> string

val function_interface_to_pretty: function_interface_t -> pretty_t

(** {1 Xml reading/writing}*)

(** [read_xml_function_interface xnode] parses a legacy function summary
    api element into a function interface*)
val read_xml_function_interface: xml_element_int -> function_interface_t

val write_xml_function_interface: xml_element_int -> function_interface_t -> unit


(** {1 Type constraints} *)


(** Adds type constraints obtained by relating the function type type variables
    with the actual parameter and return type.

    Note: Constraints will only be added if the function type has been externally
    provided.
*)
val record_function_interface_type_constraints:
      type_constraint_store_int -> string -> function_interface_t -> unit

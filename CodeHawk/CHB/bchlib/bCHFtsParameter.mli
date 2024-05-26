(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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
open CHTraceResult
open CHXmlDocument

(* bchlib *)
open BCHBCTypes
open BCHLibTypes

(** Function-type-signature parameter*)

(** {1 Parameter constructors}*)

val default_parameter_location_detail:
  ?ty:btype_t -> ?extract:(int * int) option -> int -> parameter_location_detail_t


(** Returns a parameter with name "unknown-fts-parameter", unknown type,
    unknown parameter location, and without index.*)
val default_fts_parameter: fts_parameter_t

val mk_field_position: int -> int -> string -> pld_position_t

val mk_array_position: int -> pld_position_t

val mk_global_parameter:
  ?btype:btype_t
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> doubleword_int
  -> fts_parameter_t


(** [mk_indexed_stack_parameter offset index] returns a parameter with
    index [index] located at [offset] (in bytes) on the stack. The
    parameter may be optionally augmented with name, type, description,
    roles, arg_io ([ArgRead], [ArgReadWrite], or [ArgWrite]), size,
    formatstring type, and locations (if this parameter spans multiple
    locations).

    If no locations are specified a parameter with a single stack location
    is created with stackparameter offset [offset].*)
val mk_indexed_stack_parameter:
  ?btype:btype_t
  -> ?name:string
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> ?locations:parameter_location_t list
  -> int   (* offset *)
  -> int   (* index *)
  -> fts_parameter_t


val mk_register_parameter:
  ?name:string
  -> ?btype:btype_t
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> register_t
  -> fts_parameter_t


val mk_indexed_register_parameter:
  ?btype:btype_t
  -> ?name:string
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> ?locations:parameter_location_t list
  -> register_t
  -> int   (* index *)
  -> fts_parameter_t


val mk_register_parameter_location:
  ?btype:btype_t
  -> ?size:int
  -> ?extract:(int * int) option
  -> ?position: pld_position_t list
  -> register_t
  -> parameter_location_t


val mk_stack_parameter_location:
  ?btype:btype_t
  -> ?size:int
  -> ?extract:(int * int) option
  -> int
  -> parameter_location_t


val mk_indexed_multiple_locations_parameter:
  ?btype:btype_t
  -> ?name:string
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io: arg_io_t
  -> ?size:int
  -> parameter_location_t list
  -> int    (* index *)
  -> fts_parameter_t


(** {1 Parameter comparison}*)

val pld_pos_compare: pld_position_t -> pld_position_t -> int

val pld_compare:
  parameter_location_detail_t -> parameter_location_detail_t -> int

val pld_equal:
  parameter_location_detail_t -> parameter_location_detail_t -> bool

val parameter_location_compare:
  parameter_location_t -> parameter_location_t -> int

val parameter_location_equal:
  parameter_location_t -> parameter_location_t -> bool

(** [fts_parameter_compare p1 p2] compares the parameter locations of
    [p1] and [p2]*)
val fts_parameter_compare: fts_parameter_t -> fts_parameter_t -> int

(** [fts_parameter_equal p1 p2] returns true if [p1] and [p2] have
    the same parameter location.*)
val fts_parameter_equal: fts_parameter_t -> fts_parameter_t -> bool


(** {1 Parameter accessors}*)


(** Returns the name and type of the parameter.*)
val get_parameter_signature: fts_parameter_t -> (string * btype_t)


val get_parameter_type: fts_parameter_t -> btype_t


val get_parameter_name: fts_parameter_t -> string


(** Returns the offset of a stack parameter, in bytes, measured from the
    stack pointer at function entry.

    Returns [Error] if the parameter is not a stack parameter.*)
val get_stack_parameter_offset: fts_parameter_t -> int traceresult


(** Returns the register of a register parameter.

    Returns [Error] if the parameter is not a register parameter.*)
val get_register_parameter_register: fts_parameter_t -> register_t traceresult


val convert_fmt_spec_arg: int -> argspec_int -> fts_parameter_t


val get_fmt_spec_type: argspec_int -> btype_t


(** {1 Predicates}*)

val is_global_parameter: fts_parameter_t -> bool


(** Returns true if the parameter has a single parameter location, which is
    on the stack.*)
val is_stack_parameter: fts_parameter_t -> bool


(** [is_stack_parameter_at_offset p n] returns true if parameter [p] is a
    stack parameter with offset [n] bytes.*)
val is_stack_parameter_at_offset: fts_parameter_t -> int -> bool

(** Returns true if the parameter has a single parameter location, which is
    a register.*)
val is_register_parameter: fts_parameter_t -> bool

val is_register_parameter_for_register: fts_parameter_t -> register_t -> bool

val is_arg_parameter: fts_parameter_t -> bool

val is_formatstring_parameter: fts_parameter_t -> bool

val is_floating_point_parameter: fts_parameter_t -> bool


(** {1 Printing}*)

val calling_convention_to_string: calling_convention_t -> string

val pld_position_to_string: pld_position_t -> string


(** Returns a string representation of a parameter location detail, which,
    depending on what information is available, may include:
    - location slice: {size[<start>, <size>]}
    - type of the location, if known
    - position list, in case of field positions or array positions.*)
val parameter_location_detail_to_string: parameter_location_detail_t -> string


(** Returns a string representation of a parameter location as follows:
    - [StackParameter(offset, d)]: s_arg_<offset>_<detail> where <offset>
      is the offset (in bytes) relative to the stack pointer at function entry.
    - [RegisterParameter(r, d)]: r_arg_<register-name>_<detail>
    - [GlobalParameter(g, d)]: g_arg_<global-address>_<detail>
    - [UnknownParameterLocation d]: unknown_<detail>*)
val parameter_location_to_string: parameter_location_t -> string

val fts_parameter_to_pretty: fts_parameter_t -> pretty_t

val fts_parameter_to_string: fts_parameter_t -> string


(** {1 Xml reading}*)

val read_xml_roles: xml_element_int -> (string * string) list


(** [read_xml_fts_parameter xnode] parses a parameter element from a legacy
    function summary.*)
val read_xml_fts_parameter: xml_element_int -> fts_parameter_t


(** {1 Modification}*)

val modify_types_par: type_transformer_t -> fts_parameter_t -> fts_parameter_t

val modify_name_par: string -> fts_parameter_t -> fts_parameter_t

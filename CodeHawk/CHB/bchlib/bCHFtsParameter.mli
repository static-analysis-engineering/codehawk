(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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


val default_fts_parameter: fts_parameter_t

val mk_global_parameter:
  ?btype:btype_t
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> doubleword_int
  -> fts_parameter_t

(* stack parameters are numbered starting from 1
   (located at 4 bytes above the return address) *)
val mk_stack_parameter:
  ?btype:btype_t
  -> ?name:string
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> ?fmt:formatstring_type_t
  -> int
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

val convert_fmt_spec_arg: int -> argspec_int -> fts_parameter_t

val calling_convention_to_string: calling_convention_t -> string

val fts_parameter_to_pretty: fts_parameter_t -> pretty_t

val parameter_location_compare:
  parameter_location_t -> parameter_location_t -> int

(** [fts_parameter_compare p1 p2] compares the parameter locations of
    [p1] and [p2]*)
val fts_parameter_compare: fts_parameter_t -> fts_parameter_t -> int

(** [fts_parameter_equal p1 p2] returns true if [p1] and [p2] have
    the same parameter location.*)
val fts_parameter_equal: fts_parameter_t -> fts_parameter_t -> bool

val read_xml_roles: xml_element_int -> (string * string) list

val read_xml_parameter_location :
  xml_element_int -> parameter_location_t

(** [read_xml_fts_parameter xnode] parses a parameter element from a legacy
    function summary.*)
val read_xml_fts_parameter: xml_element_int -> fts_parameter_t

val modify_types_par: type_transformer_t -> fts_parameter_t -> fts_parameter_t

val modify_name_par: string -> fts_parameter_t -> fts_parameter_t

val is_global_parameter: fts_parameter_t -> bool

val is_stack_parameter: fts_parameter_t -> bool

val is_register_parameter: fts_parameter_t -> bool

val is_arg_parameter: fts_parameter_t -> bool

val is_formatstring_parameter: fts_parameter_t -> bool

val is_floating_point_parameter: fts_parameter_t -> bool

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
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
open CHLanguage
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


val arithmetic_op_to_string: arithmetic_op_t -> string
val arithmetic_op_to_xml_string: arithmetic_op_t -> string

val bterm_to_string: bterm_t -> string
val bterm_to_pretty: bterm_t -> pretty_t

val bterm_compare: bterm_t -> bterm_t -> int
val bterm_opt_compare: bterm_t option -> bterm_t option -> int

val is_arithmetic_operator: string -> bool
val get_arithmetic_operator: string -> arithmetic_op_t


(** [read_xml_bterm node thisf pars] reads a bterm from xml node [node]
    for a function identified by [thisf] and with parameter [pars]*)
val read_xml_bterm:
  xml_element_int -> bterm_t -> fts_parameter_t list -> bterm_t


val mk_global_parameter_term:
  ?btype:btype_t
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> doubleword_int
  -> bterm_t

(* stack parameters are numbered starting from 1
   (located at 4 bytes above the return address)
val mk_stack_parameter_term:
  ?btype:btype_t
  -> ?desc:string
  -> ?roles:(string * string) list
  -> ?io:arg_io_t
  -> ?size:int
  -> int -> bterm_t *)

val arithmetic_op_to_xop: arithmetic_op_t -> xop_t
val xop_to_arithmetic_op: xop_t -> arithmetic_op_t
val is_arithmetic_xop: xop_t -> bool
val is_stack_parameter_term: bterm_t -> bool
val is_global_parameter_term: bterm_t -> bool

val xpr_to_bterm: xpr_t -> (variable_t -> bterm_t) -> bterm_t option

val modify_types_bterm: type_transformer_t -> bterm_t -> bterm_t

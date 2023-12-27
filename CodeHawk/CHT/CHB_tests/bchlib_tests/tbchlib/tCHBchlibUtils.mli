(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2023  Aarno Labs LLC

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

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHBCTypes
open BCHLibTypes

(* tbchlib *)
open TCHBchlibAssertion


(** [extract_chif_cfg_assignments ~start ~len proc] returns [len] (lhs, rhs) pairs
    of the numerical assignments in the second state of the procedure body (which
    is assumed to be a CFG) starting from [start] (default: 0).
    A negative value for [len] decrements the total length accordingly. The value
    [0] for [len] will be converted in the total length.
    The code in the second state is assumed to be contained in a TRANSACTION.*)
val extract_chif_cfg_assignments:
  ?start:int -> ?len:int -> procedure_int -> (variable_t * numerical_exp_t) list


type input_parameter_location_t = string * btype_t * string

type input_fts_parameter_t =
  int * string * btype_t * int * (string * btype_t * string) list


val convert_fts_parameter_input: input_fts_parameter_t -> x_fts_param_t


val convert_parameter_location_input: input_parameter_location_t -> x_fts_loc_t


val input_parameter_location_to_parameter_location:
  string -> input_parameter_location_t -> parameter_location_t


val get_so_xml_summary_string_node: string -> string -> xml_element_int

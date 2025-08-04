(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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
open CHXmlDocument

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


(** {1 Creation}*)

val default_function_semantics: function_semantics_t

val join_semantics:
  function_semantics_t -> function_semantics_t option -> function_semantics_t


val bvarinfo_to_function_semantics:
  bvarinfo_t -> function_interface_t -> function_semantics_t


(** {1 Modification}*)

(** [add_function_precondition fsem pre] returns the function semantics that
    is identical to [fsem] except for [pre] which is either added or replaced for
    a similar existing precondition.

    An existing precondition is replaced if it has the same predicate and
    principal parameters.

    The caller is responsible for ensuring that parameters referenced are
    added to the function interface.
*)
val add_function_precondition:
  function_semantics_t -> xxpredicate_t -> function_semantics_t


val add_function_sideeffect:
  function_semantics_t -> xxpredicate_t -> function_semantics_t


val add_function_postrequest:
  function_semantics_t -> xxpredicate_t -> function_semantics_t


(** [modify_types_semantics transformer fsem] returns function semantics
    that is updated for the changes in types given by [transformer].

    This is currently used only for creating a specialized version of the
    semantics for the ASCII/Wide-string versions of Windows library
    functions.*)
val modify_types_semantics:
  type_transformer_t -> function_semantics_t -> function_semantics_t


(** {1 Printing}*)

val function_semantics_to_pretty: function_semantics_t -> pretty_t

(** {1 Xml reading/writing}*)

(** [read_xml_function_semantics node fname pars] returns the function
    semantics encoded in xml node [node] for the function with name
    [fname] and parameters [pars]*)
val read_xml_function_semantics:
  xml_element_int -> string -> fts_parameter_t list -> function_semantics_t


val read_xml_function_interface_and_semantics:
  xml_element_int
  -> xml_element_int
  -> (function_interface_t * function_semantics_t)


val write_xml_function_semantics: xml_element_int -> function_semantics_t -> unit

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
open CHPretty

(* chutil *)
open CHXmlDocument

(* cchlib *)
open CCHLibTypes


val xpredicate_tag: xpredicate_t -> string

val s_term_to_pretty: s_term_t -> pretty_t

val xpredicate_to_pretty: xpredicate_t -> pretty_t

val s_term_to_dfs_string: s_term_t -> string

val xpredicate_to_dfs_string: xpredicate_t -> string

val get_term_parameters: s_term_t -> int list

val get_xpredicate_parameters: xpredicate_t -> int list

val get_xpredicate_global_variables: xpredicate_t -> string list

val simplify_sterm: s_term_t -> s_term_t

val simplify_xpredicate: xpredicate_t -> xpredicate_t

val read_xml_term:
  xml_element_int
  -> ?lvars:string list
  -> ?gvars:string list
  -> (string * int) list
  -> s_term_t

val read_xml_apply:
  xml_element_int list
  -> ?lvars: string list
  -> ?gvars: string list
  -> (string * int) list
  -> (xml_element_int * string * s_term_t list)

val read_xml_xpredicate:
  xml_element_int
  -> ?gvars:string list
  -> (string * int) list
  -> xpredicate_t list

val read_xml_instr:
  xml_element_int
  -> ?lvars:string list
  -> (string * int) list
  -> contract_instr_t

val write_xmlx_xpredicate:
  xml_element_int -> (string * int) list -> xpredicate_t -> unit

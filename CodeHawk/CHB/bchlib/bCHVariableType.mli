(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHLanguage

(* chutil *)
open CHXmlDocument

(* xprlib *)
open Xprt

(* bchcil *)
open BCHCBasicTypes

(* bchlib *)
open BCHLibTypes


(* Common types -------------------------------------------------------------- *)

val t_unknown: btype_t
val t_void: btype_t
val t_vararg: btype_t

val t_char: btype_t
val t_uchar: btype_t
val t_wchar: btype_t

val t_short: btype_t
val t_int: btype_t
val t_uint: btype_t
val t_long: btype_t

val t_float: btype_t
val t_double: btype_t

val t_voidptr: btype_t

val t_named: string -> btype_t


val t_comp: ?name_space:string list -> string -> btype_t
val t_enum: ?name_space:string list -> string -> btype_t
val t_class: ?name_space:string list -> string -> btype_t

val t_tcomp: ?name_space:tname_t list -> tname_t -> btype_t
val t_tenum: ?name_space:tname_t list -> tname_t -> btype_t
val t_tclass: ?name_space:tname_t list -> tname_t -> btype_t

val t_ptrto: btype_t -> btype_t
val t_refto: btype_t -> btype_t

val t_function: btype_t -> bfunarg_t list -> btype_t
val t_vararg_function: btype_t -> bfunarg_t list -> btype_t
val t_function_anon: btype_t -> btype_t        (* arguments not known *)

val t_add_attr: btype_t -> string -> btype_t

val make_name_from_type: btype_t -> int -> string

(* -------------------------------------------------------------------------- *)

val btype_to_string: btype_t -> string
val tname_to_string: tname_t -> string
val btype_to_pretty: btype_t -> pretty_t

val is_void: btype_t -> bool
val is_pointer: btype_t -> bool
val is_unsigned: btype_t -> bool  (* true if unsigned, false if signed or unknown *)
val is_function_type: btype_t -> bool
val is_unknown_type: btype_t -> bool
val is_known_type: btype_t -> bool
val is_pointer_to_struct: btype_t -> bool

val modify_type : type_transformer_t -> btype_t -> btype_t

val get_ikind_from_size: ?signed:bool -> int -> ikind_t

val get_size_of_btype: btype_t -> int option

val read_xml_type: xml_element_int -> btype_t
val read_xml_returntype: xml_element_int -> btype_t
val read_xml_summary_struct: xml_element_int -> bcompinfo_t

val read_xml_type_transformer: xml_element_int -> type_transformer_t

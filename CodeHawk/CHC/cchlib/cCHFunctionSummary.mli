(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

exception XmlReaderError of int * int * pretty_t
  
val get_freed_terms           : function_summary_t -> s_term_t list
val get_repositioned_terms    : function_summary_t -> s_term_t list
val is_const_parameter        : function_summary_t -> int -> bool
val preserves_memory_parameter: function_summary_t -> int -> bool
val preserves_null_termination: function_summary_t -> int -> bool

val summary_annotation_to_string: summary_annotation_t -> string -> string
val get_summary_annotation_type : summary_annotation_t -> string
val get_summary_annotation_string: summary_annotation_t -> string

val annotated_xpredicate_to_string: annotated_xpredicate_t -> string

val read_xml_precondition_list:
  xml_element_int -> ?gvars:string list -> (string * int) list -> annotated_xpredicate_t list  

val read_xml_postcondition_list :
  xml_element_int
  -> ?gvars:string list
  -> (string * int) list
  -> (annotated_xpredicate_t list * annotated_xpredicate_t list)
  
val read_xml_sideeffect_list:
  xml_element_int -> ?gvars:string list -> (string * int) list -> annotated_xpredicate_t list
  
val read_xml_function_summary: xml_element_int -> function_summary_t
val read_xml_ds_condition    : xml_element_int -> ds_condition_t

val function_summary_library: function_summary_library_int

val has_application_summary: int -> bool
val get_application_summary: int -> function_summary_t
val set_application_summary: int -> function_summary_t -> unit

val has_application_ds_summary: int -> bool
val get_application_ds_summary: int -> ds_condition_t
val set_application_ds_summary: int -> ds_condition_t -> unit

val set_gac_datastructures: int list -> unit
val is_gac_datastructure  : int -> bool

(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

val no_taint_info: taint_int

val precondition_predicate_to_pretty: precondition_predicate_t -> pretty_t

val precondition_predicate_to_xml   : 
  precondition_predicate_t -> method_signature_int -> xml_element_int

val make_postcondition: 
  ?name:string -> bool -> postcondition_predicate_t -> postcondition_int

val sideeffect_to_pretty: sideeffect_t -> pretty_t

val write_xml_sideeffect: 
  xml_element_int -> sideeffect_t -> method_signature_int -> unit

val resource_type_to_string: resource_type_t -> string

val get_taint_element_class_dependencies: taint_element_t -> class_name_int list
    
val make_taint: taint_element_t list -> taint_int

val make_string_sink:
  int -> string -> string -> class_name_int list -> string_sink_int

val make_resource_sink: int -> resource_type_t -> resource_sink_int

val make_exception_info: 
  ?safe:precondition_predicate_t list ->
  ?unsafe:precondition_predicate_t list ->
  ?descr:string ->
  class_name_int -> exception_info_int

val make_function_summary: 
  ?is_static:bool -> 
  ?is_final:bool -> 
  ?is_abstract:bool -> 
  ?is_inherited:bool ->
  ?is_default:bool ->
  ?is_valid:bool ->
  ?defining_method:class_method_signature_int option ->
  ?is_bridge:bool ->
  ?visibility:access_t -> 
  ?exception_infos:exception_info_int list ->
  ?post:postcondition_int list -> 
  ?sideeffects:sideeffect_t list ->
  ?taint:taint_int -> 
  ?virtual_calls:class_method_signature_int list ->
  ?interface_calls:class_method_signature_int list ->
  ?resource_sinks:resource_sink_int list ->
  ?string_sinks:string_sink_int list ->
  ?pattern:bc_action_t option ->
  ?time_cost:jterm_range_int ->
  ?space_cost:jterm_range_int -> class_method_signature_int -> function_summary_int

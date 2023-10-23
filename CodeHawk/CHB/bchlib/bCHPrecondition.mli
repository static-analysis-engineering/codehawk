(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
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
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHBCTypes
open BCHLibTypes

val relational_op_to_string: relational_op_t -> string
  
val relational_op_to_xml_string: relational_op_t -> string

val precondition_to_pretty: precondition_t -> pretty_t

val read_xml_par_preconditions: xml_element_int -> precondition_t list
  
val read_xml_precondition_predicate:
  xml_element_int -> fts_parameter_t list -> precondition_t
  
val read_xml_precondition:
  xml_element_int -> fts_parameter_t list -> precondition_t
  
val read_xml_preconditions:
  xml_element_int -> fts_parameter_t list -> precondition_t list

val relational_op_to_xop: relational_op_t -> xop_t
  
val xop_to_relational_op: xop_t -> relational_op_t

val is_relational_xop: xop_t -> bool

val is_relational_operator: string -> bool
  
val get_relational_operator: string -> relational_op_t

val modify_types_pre: type_transformer_t -> precondition_t -> precondition_t

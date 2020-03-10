(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI

val relational_op_to_string    : relational_op_t -> string
val relational_op_to_xml_string: relational_op_t -> string

val is_relational_op: string -> bool

val symbolic_jterm_constant_to_string: symbolic_jterm_constant_t -> string

val jterm_to_string: ?varname:(int -> string) -> jterm_t -> string

val jterm_compare: jterm_t -> jterm_t -> int

val depth_of_jterm: jterm_t -> int

val get_jterm_class_dependencies: jterm_t -> class_name_int list

val relational_expr_compare: relational_expr_t -> relational_expr_t -> int

val jterm_to_pretty: ?varname:(int -> string) -> jterm_t -> pretty_t

val jterm_to_sexpr_pretty: ?varname:(int -> string) -> jterm_t -> pretty_t

val relational_expr_to_pretty: ?varname:(int -> string) -> relational_expr_t -> pretty_t

val relational_expr_to_sexpr_pretty:
  ?varname:(int -> string) -> relational_expr_t -> pretty_t

(* ------------------------------------------------------- external xml -------- *)

val jterm_to_xmlx: jterm_t -> method_signature_int -> xml_element_int

val read_xmlx_simple_jterm: xml_element_int -> class_method_signature_int -> jterm_t

val read_xmlx_jterm: 
  xml_element_int -> ?argumentnames:((int * string) list) -> class_method_signature_int ->
  jterm_t

val write_xmlx_relational_expr: 
  xml_element_int
  -> method_signature_int
  -> ?setxpr:bool            (* include textual representation as xpr attribute *)  
  -> relational_expr_t -> unit

val read_xmlx_relational_expr:
  xml_element_int -> ?argumentnames:((int * string) list) ->
  class_method_signature_int -> relational_expr_t

(* --------------------------------------------------------- jterm-range ------ *)

val read_xml_jterm_range: xml_element_int -> jterm_range_int
val read_xmlx_jterm_range:
  xml_element_int -> ?argumentnames:(int * string) list -> class_method_signature_int ->
  jterm_range_int

val mk_jterm_range: jterm_t list -> jterm_t list -> jterm_range_int

val top_jterm_range: jterm_range_int
val intminmax_jterm_range: jterm_range_int

val mk_intconstant_jterm_range: numerical_t -> jterm_range_int
val mk_floatconstant_jterm_range: float -> jterm_range_int
val mk_boolconstant_jterm_range: bool -> jterm_range_int
val mk_jterm_jterm_range: jterm_t -> jterm_range_int
val mk_intrange: numerical_t option -> numerical_t option -> jterm_range_int
val mk_floatrange: float option -> float option -> jterm_range_int

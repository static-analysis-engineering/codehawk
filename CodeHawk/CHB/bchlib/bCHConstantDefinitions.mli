(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* Named constants *)

(* chlib *)
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

val has_symbolic_name: ?ty:btype_t option -> doubleword_int -> bool
val get_symbolic_name: ?ty:btype_t option -> doubleword_int -> string

val has_symbolic_address_name: doubleword_int -> bool
val get_symbolic_address_name: doubleword_int -> string
val get_symbolic_address_type: doubleword_int -> btype_t

val has_constant_value: ?ty:btype_t option -> string -> bool
val get_constant_value: ?ty:btype_t option -> string -> doubleword_int

val has_symbolic_flags: btype_t -> bool
val get_symbolic_flags: btype_t -> doubleword_int -> string list

val get_xpr_symbolic_name: ?typespec:(btype_t * bool) option -> xpr_t -> string option

val read_xml_symbolic_constants: xml_element_int -> unit
val read_xml_symbolic_addresses: xml_element_int -> unit
val read_xml_symbolic_flags    : xml_element_int -> unit

val constant_statistics_to_pretty: unit -> pretty_t 

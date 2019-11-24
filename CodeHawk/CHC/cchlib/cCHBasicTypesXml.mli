(* =============================================================================
   CodeHawk C Analyzer 
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

(* chlib *)
open CHLanguage
   
(* chutil *)
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes

(* ===================================================== CH types === *)

val write_xml_symbol  : xml_element_int -> symbol_t -> unit
val read_xml_symbol   : xml_element_int -> symbol_t

val write_xml_symbol_list: ?tag:string -> xml_element_int -> symbol_t list -> unit
val read_xml_symbol_list : ?tag:string -> xml_element_int -> symbol_t list 
  
val write_xml_variable: xml_element_int -> variable_t -> unit
val read_xml_variable : xml_element_int -> variable_t

val write_xml_varuse : xml_element_int -> varuse -> unit
val read_xml_varuse  : xml_element_int -> varuse

val write_xml_fielduse: xml_element_int -> fielduse -> unit
val read_xml_fielduse : xml_element_int -> fielduse

val read_xml_exp_list : xml_element_int -> exp list

val write_xml_exp_option_list: ?tag:string -> xml_element_int -> exp option list -> unit
val read_xml_exp_option_list : ?tag:string -> xml_element_int -> exp option list

val read_xml_cfile    : xml_element_int -> file

val read_xml_instruction : xml_element_int -> instr

val read_xml_function_definition: xml_element_int -> fundec

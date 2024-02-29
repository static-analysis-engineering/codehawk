(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHPretty

(* chutil *)
open CHXmlDocument

(* ================================================================================
 * Xml naming conventions:
 * ------------------------
 * general:
 *    attributes:
 *     a  : address (in hex)
 *     ofs: offset (in decimal)
 * variables: 
 *    element tags:
 *     var : generic variable
 *    lvar : local variable
 *    attributes:
 *    vn : name of the variable
 *    vx : index of the variable
 * functions:
 *    attributes:
 *    fn : name of the function
 * ================================================================================= *)


exception XmlReaderError of int * int * pretty_t

class type xml_header_int =
object
  (* setters *)
  method set_header: string -> unit

  (* accessors *)
  method get_header: xml_element_int

  (* predicates *)
  method has_header: bool
end

(* set default variable type for reading variables *)
val set_symbolic_type: unit -> unit

(* variable name tag, variable index tag *)
val write_xml_variable: xml_element_int -> variable_t -> string -> string -> unit

(* variable name tag, variable index tag *)
val read_xml_variable : xml_element_int -> string -> string -> variable_t
      
val has_control_characters : string -> bool
val hex_string             : string -> string

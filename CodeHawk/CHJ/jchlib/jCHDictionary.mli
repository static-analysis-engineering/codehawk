(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet and Henny Sipma
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
open CHLanguage

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI

val common_dictionary: dictionary_int 

val make_cn: string -> class_name_int
val make_ms: bool -> string -> method_descriptor_int -> method_signature_int
val make_cms: class_name_int -> method_signature_int -> class_method_signature_int
val make_fs: string -> value_type_t -> field_signature_int
val make_cfs: class_name_int -> field_signature_int -> class_field_signature_int

val retrieve_cn: int -> class_name_int
val retrieve_ms: int -> method_signature_int
val retrieve_cms: int -> class_method_signature_int
val retrieve_cfs: int -> class_field_signature_int

val list_class_names: unit -> class_name_int list

val read_xmlx_value_type: xml_element_int -> value_type_t
val read_xmlx_object_type: xml_element_int -> object_type_t

val read_xmlx_method_descriptor: 
  xml_element_int -> (value_type_t list * value_type_t option)

val read_xmlx_method_signature: 
  xml_element_int -> string -> bool -> method_signature_int

val read_xmlx_constructor_signature:
  xml_element_int -> class_name_int -> class_method_signature_int

val read_xmlx_class_method_signature: 
  xml_element_int -> class_name_int -> class_method_signature_int

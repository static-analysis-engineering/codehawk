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
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI

exception UTF8ParseError of pretty_t
                          
val parse_base_type: string -> java_basic_type_t

val parse_class_name: string -> class_name_int

val parse_object_type: string -> object_type_t

val parse_field_type: string -> value_type_t

val parse_field_descriptor: string -> value_type_t

val parse_method_descriptor: string -> method_descriptor_int

val parse_descriptor: string -> descriptor_t

val parse_class_signature: string -> class_signature_int

val parse_method_type_signature: string -> method_type_signature_int

val parse_field_type_signature: string -> field_type_signature_int

val activate_tracing: unit -> unit
val get_utf8_parsed_strings: unit -> (string * (string * pretty_t) list) list

(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet
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

(* jchlib *)
open JCHBasicTypesAPI

val value_signature  : value_type_t -> string

val type2shortstring : value_type_t -> string

val method_signature :
  string ->
  < arguments : value_type_t list; return_value : value_type_t option; .. > ->
  string

val signature : string -> descriptor_t -> string

val jvm_basic_type  : java_basic_type_t -> char

val java_basic_type : java_basic_type_t -> char

val dump_constant_value : 'a IO.output -> constant_value_t -> unit

val dump_constant : 'a IO.output -> constant_t -> unit

val dump_verification_type : verification_type_t -> string

val dump_stackmap :
  'a IO.output -> int * verification_type_t list * verification_type_t list -> unit

val dump_exc :
  'a IO.output ->
  'b ->
  < catch_type : < name : string; .. > option; h_end : int; h_start : 
    int; handler : int; .. > ->
  unit


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

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI
   
(* jchpre *)
open JCHPreAPI

val get_dynamiccount: unit -> int
val get_loop_count: unit -> int
val get_methodsize_count: int -> int
val get_methodsize_no_pattern_count: int -> int

val bc_basic_value_to_pretty: bc_basicvalue_t -> pretty_t
val bc_object_value_to_pretty: bc_objectvalue_t -> pretty_t
val bc_value_to_pretty: bc_value_t -> pretty_t
val bc_action_to_pretty: bc_action_t -> pretty_t

val bc_pattern_to_pretty: bc_pattern_t -> pretty_t

val get_noteworthy: unit -> (string * (string * method_info_int) list) list
val get_interesting: unit -> (string * (string * pretty_t) list) list
val get_call_packages: unit -> (string * int) list
val get_this_packages: unit -> (string * int) list

val get_pattern:
  ?maxlog:int
  -> ?maxmatch:int
  -> string
  -> method_info_int
  -> class_info_int
  -> bc_pattern_t option 


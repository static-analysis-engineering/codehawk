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

(* chlib *)
open CHPretty

(* jchlib *)
open JCHBasicTypesAPI
open JCHRawClass

exception No_class_found of string

type cp_unit_t = 
| Directory of string 
| JarFile of string * Zip.in_file 
| WarFile of string * Zip.in_file

type class_path_t = cp_unit_t list

val class_path : string -> cp_unit_t list
val close_class_path: cp_unit_t list -> unit

val get_classpath_units : string -> string list

val class_path_to_pretty: class_path_t -> pretty_t

val get_class : class_path_t -> < name : string; .. > -> java_class_or_interface_int
val has_summary_class: class_path_t -> < name:string ; .. > -> bool
val get_summary_class: class_path_t -> < name:string ; .. > -> string

val get_summary_manifest: cp_unit_t -> string

val apply_to_jar :
  ?xcludes:string list ->
  (raw_class_t -> unit) ->
  (Zip.in_file -> Zip.entry -> unit) -> string -> unit

val apply_to_xml_jar :
  (string -> string -> unit) -> (Zip.in_file -> Zip.entry -> unit) -> string -> unit

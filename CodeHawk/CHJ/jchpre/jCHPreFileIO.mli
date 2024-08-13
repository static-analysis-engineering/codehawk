(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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

(* chutil *)
open CHXmlDocument

(* jchlib *)
open JCHBasicTypesAPI


val has_stac_analysis_dir: unit -> bool
val get_stac_analysis_app_dir: unit -> string

val get_assumptions_filename: class_name_int -> string
val get_invariants_results_filename: class_name_int -> string

val make_class_file_name: string -> string -> string -> string
val get_jch_root: string -> xml_element_int
val get_taint_trails_filename: int -> string

val save_log_files: string -> unit
val save_dictionary: unit -> unit
val save_jt_dictionary: unit -> unit
val save_signature_file: unit -> unit
val save_callgraph_file: unit -> unit
val save_missing_items: unit -> unit
val save_taint_origins: unit -> unit

val save_classnames: class_name_int list -> unit
val save_timecost_diagnostics: xml_element_int -> unit

val read_dictionary: unit -> unit
val read_jt_dictionary: unit -> unit
val read_callgraph_file: unit -> unit
val read_taint_origins: unit -> unit
val read_excluded_methods: unit -> int list
val read_excluded_classes: unit -> unit

val save_xml_file: string -> xml_element_int -> string -> unit

val save_method_xml_file:
  class_method_signature_int -> xml_element_int -> string -> unit

val load_method_xml_file:
  class_method_signature_int -> string -> xml_element_int option

val save_class_xml_file:
  string
  -> class_name_int
  -> ?md5:string
  -> ?timestamp:string
  -> xml_element_int
  -> string
  -> unit

val load_class_xml_file:
  string
  -> class_name_int
  -> ?md5:string
  -> ?timestamp:string
  -> unit
  -> xml_element_int option

val apply_to_xml_jar:
  (string -> bool) -> (string -> string -> unit) -> string -> unit

val save_xml_user_class_template_file: class_name_int -> unit

val save_xml_cost_analysis_results:
  class_name_int -> xml_element_int -> string -> unit

val save_xml_atlas_cost_analysis_results:
  class_name_int -> xml_element_int -> string -> unit

val load_xml_cost_analysis_results: class_name_int -> xml_element_int option

val save_xml_cost_support_data: class_name_int -> xml_element_int -> string -> unit

val load_xml_cost_support_files: unit -> xml_element_int list

val save_xml_taint_support_data: class_name_int -> xml_element_int -> string -> unit

val load_user_class_files: unit -> unit

val load_defaultcostdata_file: unit -> unit

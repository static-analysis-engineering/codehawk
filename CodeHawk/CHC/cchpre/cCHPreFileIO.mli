(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Coprygith (c) 2023      Aarno Labs LLC

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
open CHLogger
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

(* cchpre *)
open CCHPreTypes

val get_xml_summaryresults_name: unit -> string

val save_cfile_logfile: logger_int -> string -> string -> unit
val save_logfile: logger_int -> string -> string -> unit
val append_to_logfile: logger_int -> string -> string -> unit

val read_cfile: unit -> file 

val read_cfile_dictionary: unit -> unit
val save_cfile_dictionary: unit -> unit

val read_cfile_assignment_dictionary: unit -> unit
val save_cfile_assignment_dictionary: unit -> unit

val read_cfile_predicate_dictionary: unit -> unit
val save_cfile_predicate_dictionary: unit -> unit

val read_cfile_interface_dictionary: unit -> unit
val save_cfile_interface_dictionary: unit -> unit

val read_cfile_contract: unit -> unit
val save_cfile_contract: unit -> unit

val read_cfile_context: unit -> unit
val save_cfile_context: unit -> unit

val read_function_semantics: string -> fundec

val save_chif: string -> pretty_t -> unit

val read_proof_files: string -> cfundeclarations_int -> unit
val save_proof_files: string -> unit
  
val save_api  : string -> unit
val read_api  : string -> cfundeclarations_int -> unit

val save_vars : string -> variable_manager_int -> unit
val read_vars : string -> cfundeclarations_int -> variable_manager_int

val save_invs : string -> invariant_io_int -> unit
val read_invs : string -> vardictionary_int -> invariant_io_int

val read_ppos : string -> unit

val get_src_directory: unit -> string
val get_target_files_name: unit -> string
val read_target_files: unit -> (int * string) list
val get_xml_cfile: string -> file

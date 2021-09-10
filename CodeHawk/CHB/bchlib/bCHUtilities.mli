(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021      Aarno Labs LLC

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

(* System-independent utilities *)

(* chlib *)
open CHPretty
open CHIntervals

(* chutil *)
open CHLogger

(* bchlib *)
open BCHLibTypes

val set_tracked_functions: string list -> unit

val track_function:
  ?iaddr:ctxt_iaddress_t                (* instruction address *)
  -> doubleword_int                     (* function address *)
  -> pretty_t -> unit

val get_date_and_time: unit -> string           (* raises Invalid_argument *)

val make_date_and_time_string: Unix.tm -> string (* raises Invalid_argument *)

val today:string

exception No_file_found of string

val initialize_activity_log: string -> unit
val initialize_results_log : string -> unit
val log_activity: pretty_t -> unit
val log_result  : pretty_t -> unit

val translation_log: logger_int
val disassembly_log: logger_int

val replace_dot  : string -> string
val replace_slash: string -> string
val open_path: string -> (string * Zip.in_file) option

val lookup_summary: string -> (string * Zip.in_file) -> string
val has_summary_file: (string * Zip.in_file) list -> string -> bool
val get_summary_file: (string * Zip.in_file) list -> string -> string

val get_file_from_jar: (string * Zip.in_file) list -> string -> string option

val apply_to_xml_jar:
  (string -> string -> unit)
  -> (Zip.in_file -> Zip.entry -> unit)
  -> Zip.in_file -> unit

val add_to_sumtype_tables:
  ('a,string) Hashtbl.t -> (string,'a) Hashtbl.t -> 'a -> string -> unit

val get_string_from_table : string -> ('a,string) Hashtbl.t -> 'a -> string
val get_sumtype_from_table: string -> (string,'a) Hashtbl.t -> string -> 'a
val is_string_of_sumtype  : (string,'a) Hashtbl.t -> string -> bool
val get_sumtype_table_keys: ('a,string) Hashtbl.t -> 'a list

val interval_compare : interval_t -> interval_t -> int

val list_compare: 'a list -> 'a list -> ('a -> 'a -> int) -> int

val optvalue_compare: 'a option -> 'a option -> ('a -> 'a -> int) -> int

val has_control_characters: string -> bool
val hex_string: string -> string

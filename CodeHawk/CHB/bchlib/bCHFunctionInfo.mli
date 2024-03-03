(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes


(** The principal access point for analysis results for an assembly function.

    It is the main access points for analysis results (invariants), call targets
    of instructions, jump targets of indirect jumps, function api, etc.
 *)


(** Proof obligation anchor.*)
type po_anchor_t =
| DirectAccess
| IndirectAccess of bterm_t

val po_anchor_compare: po_anchor_t -> po_anchor_t -> int

val po_anchor_to_pretty: po_anchor_t -> pretty_t

(** [load_function_info ~reload:reload dw] returns the function info associated with
    the assembly function at address [dw].

    Function retrieval is as follows:
    - if the function info already exists in the cache and [reload=false], the
      function-info from the cache is returned, otherwise
    - if a function-info xml file exists, the function-info is loaded from file,
      otherwise
    - a new function-info is created

    @raise [BCH_failure] if
    - an error occurs when loading a function-info from file, or
    - address [dw] is not known to be a function entry point
 *)
val load_function_info: ?reload:bool -> doubleword_int -> function_info_int


(** same as {!load_function_info} [~reload:false] *)
val get_function_info : doubleword_int -> function_info_int


(** Returns all function-infos present in the cache.*)
val get_function_infos: unit -> function_info_int list


(** Returns a list of (function-address, instruction-address, jni-index) of
    calls to JNI (java native method) functions.*)
val get_jni_calls: unit -> (doubleword_int * (ctxt_iaddress_t * int) list) list


(** [get_vars_metrics env] returns statistics on the variables present in the
    function symboltable [env].*)
val get_vars_metrics: function_environment_int -> vars_metrics_t

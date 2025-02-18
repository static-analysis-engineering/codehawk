(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2025 Henny B. Sipma

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
open CHUtils

class jsystem_t :
  object
    method add_stats : string -> pretty_t -> unit
    method get_call_graph_manager : JCHCallGraph.call_graph_manager_t
    method get_jproc_info : symbol_t -> JCHProcInfo.jproc_info_t
    method get_jproc_info_seq_no : int -> JCHProcInfo.jproc_info_t
    method get_not_analyzed_bad : IntCollections.set_t
    method get_not_analyzed_good : IntCollections.set_t
    method get_number_procs : int
    method get_original_chif : system_int
    method get_procedures : symbol_t list
    method get_stats : string -> pretty_t option
    method get_transformed_chif : system_int
    method not_analyzed_bad : int -> bool
    method not_analyzed : int -> bool
    method set : system_int -> unit
    method stats_to_pretty : pretty_t
    method toPretty : pretty_t
  end

val jsystem : jsystem_t

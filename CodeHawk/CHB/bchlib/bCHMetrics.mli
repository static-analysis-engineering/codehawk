(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes

val get_userdata_metrics: unit -> userdata_metrics_t
val get_vars_metrics: function_environment_int -> vars_metrics_t
val get_calls_metrics: function_info_int -> calls_metrics_t
val get_jumps_metrics: function_info_int -> jumps_metrics_t
val get_cc_metrics: function_info_int -> cc_metrics_t
val get_invs_metrics: invariant_io_int -> invs_metrics_t
val get_tinvs_metrics: type_invariant_io_int -> tinvs_metrics_t

val get_result_metrics:
  function_info_int
  -> memacc_metrics_t
  -> cfg_metrics_t
  -> result_metrics_t

val combine_results:
  int
  -> bool
  -> bool
  -> bool
  -> float
  -> function_results_t
  -> result_metrics_t
  -> function_results_t

val compute_totals: result_metrics_t list -> result_metrics_t

val compute_aggregate_metrics: result_metrics_t list -> aggregate_metrics_t

val file_metrics: file_metrics_int

val save_file_results: unit -> unit

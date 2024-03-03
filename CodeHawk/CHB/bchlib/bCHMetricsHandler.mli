(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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


val exports_metrics_handler: exports_metrics_t metrics_handler_int

val disassembly_metrics_handler: disassembly_metrics_t metrics_handler_int

val memacc_metrics_handler: memacc_metrics_t metrics_handler_int

val mk_prec_metrics_handler:
  memacc_metrics_t -> prec_metrics_t metrics_handler_int

val cfg_metrics_handler: cfg_metrics_t metrics_handler_int

val vars_metrics_handler: vars_metrics_t metrics_handler_int

val calls_metrics_handler: calls_metrics_t metrics_handler_int

val jumps_metrics_handler: jumps_metrics_t metrics_handler_int

val cc_metrics_handler: cc_metrics_t metrics_handler_int

val invs_metrics_handler: invs_metrics_t metrics_handler_int

val result_metrics_handler: result_metrics_t metrics_handler_int

val function_run_handler: function_run_t metrics_handler_int

val mk_function_results_handler: string -> function_results_t metrics_handler_int

val file_run_handler: file_run_t metrics_handler_int

val aggregate_metrics_handler: aggregate_metrics_t metrics_handler_int

val userdata_metrics_handler: userdata_metrics_t metrics_handler_int

val ida_data_handler: ida_data_t metrics_handler_int

val file_results_handler: file_results_t metrics_handler_int

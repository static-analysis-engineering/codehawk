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

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

val is_number: variable_t -> bool
val is_not_number: variable_t -> bool
val is_constant: variable_t -> bool
val is_loop_counter: variable_t -> bool
val is_exception: variable_t -> bool
val is_not_exception: variable_t -> bool
val is_return: variable_t -> bool
val is_not_exception_or_return: variable_t -> bool
val is_temp: variable_t -> bool
val is_register: variable_t -> bool
val is_length: variable_t -> bool
val is_stack: variable_t -> bool

val make_length: variable_t -> variable_t

val get_register_index: variable_t -> int
val get_signature_vars: procedure_int -> variable_t list
val get_signature_write_vars: procedure_int -> variable_t list
val get_signature_read_vars: procedure_int -> variable_t list

val get_return_var: procedure_int -> variable_t option
val get_num_return_var: procedure_int -> variable_t option

val add_cmds :
  cms:class_method_signature_int
  -> init_cmds:(code_int, cfg_int) command_t list
  -> final_cmds:(code_int, cfg_int) command_t list
  -> code:code_int -> code_int

val get_CFG : procedure_int -> cfg_int

val get_arg_var : string ->
  (string * variable_t * arg_mode_t) list -> variable_t
val get_arg_var_opt : string ->
  (string * variable_t * arg_mode_t) list -> variable_t option

val get_read_vars: ('a * 'b * arg_mode_t) list -> 'b list
val get_just_read_vars: ('a * 'b * arg_mode_t) list -> 'b list
val get_write_vars: ('a * 'b * arg_mode_t) list -> 'b list
val get_just_write_vars: ('a * 'b * arg_mode_t) list -> 'b list

val get_bytecode : symbol_t -> bytecode_int option
val copy_system  : system_int -> system_int

val get_first_and_last_in_state : method_info_int -> state_int -> int option * int
val get_prev_pcs : method_info_int -> cfg_int -> state_int -> int list

val start_timing: unit -> unit
val add_timing: string -> unit

val start_total_time: unit -> unit
val get_total_time: unit -> float
val start_time: unit -> unit
val get_time: unit -> float

val sym_to_pc: symbol_t -> int
val is_not_jdk_method: symbol_t -> bool

val start_profiling_time: int -> unit
val stop_profiling_time: int -> unit
val report_profiling_times: unit -> unit
val report_profiling_times_no_reset: unit -> unit

val print_warning_message: pretty_t -> unit
val print_exception_message: pretty_t -> unit

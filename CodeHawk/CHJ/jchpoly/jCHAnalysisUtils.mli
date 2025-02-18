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

open Big_int_Z

(* chlib *)
open CHAtlas
open CHIntervals
open CHLanguage
open CHNumerical
open CHUtils

(* jchlib *)
open JCHBasicTypesAPI


val set_current_proc_name : symbol_t -> unit
val get_current_proc_name : unit -> symbol_t
val get_current_jproc_info : unit -> JCHProcInfo.jproc_info_t

val get_exit_invariant : unit -> atlas_t option

val jch_op_semantics :
  invariant:atlas_t
  -> stable:bool
  -> fwd_direction:bool
  -> context:'a
  -> operation:operation_t
  -> atlas_t

exception JCH_num_analysis_failure of string

class numeric_run_params_t :
  object
    method analysis_level : int
    method analysis_failed : int -> string -> exn
    method check_time_limit : int
    method create_model : bool
    method get_analysis_status : int
    method get_analysis_failure_reason : string
    method get_system_use_intervals : bool
    method interval_array_size : int
    method is_good_coefficient : big_int -> bool
    method max_number_constraints : int
    method max_number_constraints_allowed : int
    method max_number_rays : int
    method max_number_vars_in_constraint_allowed : int
    method max_poly_coefficient : big_int
    method number_joins : int
    method reached_constraint_analysis_time_limit : bool
    method reached_numeric_analysis_time_limit : bool
    method record_number_constraints : int -> unit
    method reset : bool -> unit
    method reset_analysis_failure_status : unit
    method set_analysis_level : int -> unit
    method set_create_model : bool -> unit
    method set_constraint_analysis_time_limit : int -> unit
    method set_max_number_constraints_allowed : int -> unit
    method set_max_number_rays: int -> unit
    method set_max_number_vars_in_constraint_allowed  : int -> unit
    method set_max_poly_coefficient : int -> unit
    method set_number_joins : int -> unit
    method set_numeric_analysis_time_limit : int -> unit
    method set_system_use_intervals : bool -> unit
    method set_use_intervals : bool -> unit
    method set_use_lengths : bool -> unit
    method set_use_loop_counters : bool -> unit
    method set_use_overflow : bool -> unit
    method set_use_time_limits : bool -> unit
    method set_use_types : bool -> unit
    method start_numeric_analysis_time : unit
    method use_intervals : bool
    method use_lengths : bool
    method use_loop_counters : bool
    method use_overflow : bool
    method use_types : bool
  end

val numeric_params : numeric_run_params_t

val has_untranslated_caller : symbol_t -> bool
val get_slot_interval : logical_stack_slot_int -> interval_t

val is_numeric : JCHProcInfo.jproc_info_t -> variable_t -> bool
val is_collection : JCHProcInfo.jproc_info_t -> variable_t -> bool
val is_array : JCHProcInfo.jproc_info_t -> variable_t -> bool
val is_collection_or_array : JCHProcInfo.jproc_info_t -> variable_t -> bool

val float_to_interval : float -> numerical_t * numerical_t * interval_t

val get_length_vars :
  JCHProcInfo.jproc_info_t
  -> variable_t list
  -> variable_t list
     * variable_t list
     * variable_t CHUtils.VariableCollections.table_t

val include_length_vars :
  JCHProcInfo.jproc_info_t -> variable_t list -> variable_t list

val include_all_length_vars :
  JCHProcInfo.jproc_info_t
  -> variable_t list
  -> variable_t list
  -> variable_t VariableCollections.table_t
  -> variable_t list * variable_t list * int list

val integer_div : interval_t -> interval_t -> interval_t

(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
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
open CHDomain
open CHIntervals
open CHLanguage
open CHUtils

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

val set_instr_pc : int -> unit
val set_prev_pc_to_wto_pc : (int * int) list -> unit
  
val set_invs :
  JCHPolyIntervalArray.poly_interval_array_t IntCollections.table_t -> unit
  
val add_reachable : variable_t -> unit 
val is_reachable : variable_t -> bool
val get_changed_sym_params : unit -> variable_t list
val add_variable_to_field : variable_t -> instruction_info_int -> unit
  
val get_proc_info :
  unit
  -> VariableCollections.set_t
     * VariableCollections.set_t
     * VariableCollections.set_t
     * VariableCollections.set_t
     * VariableCollections.set_t
     * VariableCollections.set_t
     * VariableCollections.set_t
     * VariableCollections.set_t

val print_lost_info : unit -> unit
    
class poly_int_domain_no_arrays_t :
        JCHProcInfo.jproc_info_t
        -> JCHPolyIntervalArray.poly_interval_array_t
        -> variable_t list * (variable_t * variable_t) list
        -> domain_int

val get_poly_int_array : domain_int -> JCHPolyIntervalArray.poly_interval_array_t

val get_poly_dom : 
  JCHProcInfo.jproc_info_t
  -> JCHPolyIntervalArray.poly_interval_array_t
  -> bool
  -> bool
  -> poly_int_domain_no_arrays_t 

val get_interval: domain_int -> variable_t -> interval_t

val get_relational_exprs :
  bool -> poly_int_domain_no_arrays_t -> relational_expr_t list

val get_local_var_map :
  poly_int_domain_no_arrays_t -> (variable_t * variable_t) list

val get_poly_vars : poly_int_domain_no_arrays_t -> variable_t list

val bottom_poly_int_dom :
  JCHProcInfo.jproc_info_t -> poly_int_domain_no_arrays_t

val top_poly_int_dom :
  JCHProcInfo.jproc_info_t -> variable_t list -> poly_int_domain_no_arrays_t

val project_out_loop_counters :
  poly_int_domain_no_arrays_t -> poly_int_domain_no_arrays_t

val remove_duplicates :
  poly_int_domain_no_arrays_t -> poly_int_domain_no_arrays_t

val restrict_to_vars :
  poly_int_domain_no_arrays_t -> variable_t list -> poly_int_domain_no_arrays_t

val get_relational_exprs_vars_fields :
  poly_int_domain_no_arrays_t -> variable_t list -> relational_expr_t list

val dbg : bool ref



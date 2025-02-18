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
open CHSCC

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI


class wto_info_t :
  is_proc_wto:bool
  -> name:symbol_t
  -> wto:wto_component_t
  -> conds:symbol_t list
  -> exit_conds:symbol_t list
  -> proc:procedure_int
  -> cfg:cfg_int
  -> proc_wto:CHSCC.wto_component_t list
  -> object ('a)
       method add_inner_loop : 'a -> unit
       method get_conds : symbol_t list
       method get_cond_pcs : int list
       method get_exit_conds : symbol_t list
       method get_entry_pc : int
       method get_entry_incoming_pcs : int list
       method get_first_pc : int
       method get_index : int
       method get_inner_loops : 'a list
       method get_last_in_entry_state : int
       method get_last_pc : int
       method get_loop_info : unit -> loop_info_t
       method get_max_iterations : jterm_t list
       method get_name : symbol_t
       method get_outer_loops : 'a list
       method get_proc_wto : CHSCC.wto_component_t list
       method get_states : symbol_t list
       method get_var : variable_t
       method get_var_name : symbol_t
       method get_wto : CHSCC.wto_component_t
       method has_state : symbol_t -> bool
       method is_top : bool
       method is_unreachable : bool
       method set_max_iterations : jterm_t list -> unit
       method set_outer_loops : 'a list -> unit
       method set_unreachable : unit
       method toPretty : pretty_t
     end

val get_sccs_proc :
  procedure_int
  -> symbol_t
  -> (wto_info_t list) * (CHSCC.wto_component_t list) * int

val get_loop_infos : method_info_int -> loop_info_t list

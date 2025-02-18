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
open CHNumerical
open CHPretty
open CHUtils

(* jchlib *)
open JCHBasicTypesAPI


class jvar_info_t :
  variable:variable_t
  -> param_index:int
  -> is_phi:bool
  -> origins:int list
  -> pc_in_scope:int
  -> basic_num_vtype:value_type_t option
  -> vtypes:value_type_t list
  -> const:numerical_t option
  -> is_numeric:bool
  -> has_length:bool
  -> first_state:symbol_t
  -> last_states:symbol_t list
  -> read_states:symbol_t list
  -> read_vars:variable_t list
  -> return_pc_to_rvar:variable_t IntCollections.table_t option
  -> origin_operations:operation_t list
  -> local_indices:int list
  -> object
    method get_variable_from_length : variable_t option * bool
    method get_basic_num_type : value_type_t option
    method get_constant : numerical_t option
    method get_first_state : symbol_t
    method get_last_states : symbol_t list
    method get_length : variable_t option * bool
    method get_local_indices : int list
    method get_origins : int list
    method get_origin_operations : operation_t list
    method get_param_index : int option
    method get_pc_in_scope : int
    method get_read_states : symbol_t list
    method get_read_vars : variable_t list
    method get_return_pc_to_rvar : variable_t IntCollections.table_t
    method get_types : value_type_t list
    method get_variable : variable_t
    method has_length : bool
    method is_length : bool
    method is_local_var : bool
    method is_numeric : bool
    method is_parameter : bool
    method is_phi : bool
    method is_return : bool
    method set_has_length : bool -> unit
    method set_corresp_var : variable_t -> unit
    method set_corresp_length : variable_t -> unit
    method toPretty : pretty_t
  end

val make_jvar_infos :
  meth:method_int
  -> proc:procedure_int
  -> cfg:cfg_int
  -> lc_to_pc:(variable_t * int) list
  -> wto:CHSCC.wto_component_t list
  -> dom_info:JCHDominance.dominance_info_t
  -> aliases:JCHTransformUtils.alias_sets_t
  -> extra_assert_vars:SymbolCollections.set_t VariableCollections.table_t
  -> jvar_info_t VariableCollections.table_t
     * SymbolCollections.set_t VariableCollections.table_t VariableCollections.table_t
     * SymbolCollections.set_t VariableCollections.table_t VariableCollections.table_t
     * int
     * int
     * variable_t IntCollections.table_t IntCollections.table_t

val make_state_to_start_num_vars :
  jvar_info_t VariableCollections.table_t
  -> VariableCollections.set_t SymbolCollections.table_t

val make_state_to_done_num_vars :
  jvar_info_t VariableCollections.table_t
  -> VariableCollections.set_t SymbolCollections.table_t

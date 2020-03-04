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
open CHLanguage
open CHPretty
open CHUtils

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

class pc_analysis_results_t :
  object
    method get_invariants : relational_expr_t list
    method get_taint_origins : (variable_t * taint_origin_set_int) list
    method set_invariants : relational_expr_t list -> unit
    method set_taint_origins : (variable_t * taint_origin_set_int) list -> unit
    method toPretty : pretty_t
  end

class analysis_results_t :
  object
    method get_pc_analysis_results : pc_analysis_results_t IntCollections.table_t
    method get_return_origins : taint_origin_set_int option
    method set_invariants : int -> relational_expr_t list -> unit
    method set_taint_origins : int -> (variable_t * taint_origin_set_int) list -> unit
    method set_return_origins : taint_origin_set_int -> unit
    method toPretty : pretty_t
  end


class jproc_info_t :
  proc_name:symbol_t
  -> proc:procedure_int
  -> wto:CHSCC.wto_t 
  -> wto_infos:JCHLoopUtils.wto_info_t list
  -> loop_depth:int 
  -> pc_to_instr:(int -> int) 
  -> instr_to_pc:(int -> int)
  -> object
    method get_analysis_results : analysis_results_t
    method get_variable_from_length : variable_t -> variable_t option
    method get_bytecode : bytecode_int
    method get_count_number_vars : int 
    method get_count_numeric_vars : int 
    method get_cfg : cfg_int
    method get_instr_to_pc : int -> int
    method get_jvar_info : variable_t -> JCHVarInfo.jvar_info_t 
    method get_jvar_infos : JCHVarInfo.jvar_info_t VariableCollections.table_t
    method get_length : variable_t -> variable_t option
    method get_loop_depth : int
    method get_loop_number : int
    method get_method : method_int
    method get_method_info : method_info_int
    method get_name : symbol_t
    method get_opcodes : opcodes_int
    method get_pc_to_instr : int -> int
    method get_procedure : procedure_int
    method get_source_origin : string
    method get_var_table : (int * int * string * value_type_t list * int) list
    method get_var_to_var_to_eqs :
             SymbolCollections.set_t VariableCollections.table_t VariableCollections.table_t
    method get_var_to_var_to_ineqs :
             SymbolCollections.set_t VariableCollections.table_t VariableCollections.table_t
    method get_variables : variable_t list
    method get_wto_infos : JCHLoopUtils.wto_info_t list 
    method get_wto_prev_pc_to_entry_pcs : (int * int) list
    method get_wto : CHSCC.wto_t
    method has_orig_var_table : bool
         
    method make_var_table : 
      aliases:JCHTransformUtils.alias_sets_t
      -> rvar_to_pc_to_versions:VariableCollections.set_t IntCollections.table_t
                                VariableCollections.table_t
      -> orig_phi_to_vars:VariableCollections.set_t VariableCollections.table_t
      -> local_var_index_to_pc_to_var:variable_t IntCollections.table_t IntCollections.table_t
      -> unit
         
    method set_var_infos :
             chif:system_int
             -> dom_info:JCHDominance.dominance_info_t
             -> aliases:JCHTransformUtils.alias_sets_t
             -> extra_assert_vars:SymbolCollections.set_t VariableCollections.table_t
             -> variable_t IntCollections.table_t IntCollections.table_t
         
    method set_var_table : (int * int * string * value_type_t list * int) list -> unit
    method toPretty : pretty_t
  end

val make_jproc_info : 
  chif:system_int
  -> proc_name:symbol_t
  -> proc:procedure_int
  -> wto:CHSCC.wto_t
  -> wto_infos:JCHLoopUtils.wto_info_t list
  -> loop_depth:int
  -> dom_info:JCHDominance.dominance_info_t
  -> aliases:JCHTransformUtils.alias_sets_t
  -> rvar_to_pc_to_versions:VariableCollections.set_t IntCollections.table_t VariableCollections.table_t
  -> orig_phi_to_vars:VariableCollections.set_t VariableCollections.table_t
  -> extra_assert_vars:SymbolCollections.set_t VariableCollections.table_t
  -> jproc_info_opt:jproc_info_t option
  -> jproc_info_t 


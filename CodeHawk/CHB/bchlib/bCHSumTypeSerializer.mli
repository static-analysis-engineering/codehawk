(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
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

(* chutil *)
open CHSumTypeSerializer

(* bchlib *)
open BCHLibTypes


val calling_convention_mfts: calling_convention_t mfts_int
val arithmetic_op_mfts: arithmetic_op_t mfts_int
val g_arithmetic_op_mfts: g_arithmetic_op mfts_int
val relational_op_mfts: relational_op_t mfts_int

val arg_io_mfts: arg_io_t mfts_int
val formatstring_type_mfts: formatstring_type_t mfts_int

(** {1 Architecture-related} *)

(** {2 x86} *)

val eflag_mfts: eflag_t mfts_int
val arm_cc_flag_mfts: arm_cc_flag_t mfts_int
val cpureg_mfts: cpureg_t mfts_int
val segment_mfts: segment_t mfts_int

(** {2 mips} *)

val mips_reg_mfts: mips_reg_t mfts_int
val mips_special_reg_mfts: mips_special_reg_t mfts_int

(** {2 arm} *)

val arm_reg_mfts: arm_reg_t mfts_int
val arm_special_reg_mfts: arm_special_reg_t mfts_int
val arm_extension_reg_type_mfts: arm_extension_reg_type_t mfts_int

(** {2 power32} *)

val pwr_spr_mfts: pwr_special_reg_t mfts_int
val pwr_crf_mfts: pwr_register_field_t mfts_int

(** {2 Generic} *)

val flag_mcts: flag_t mfts_int
val register_mcts: register_t mfts_int

(** {1 Interface types} *)

val pld_position_mcts: pld_position_t mfts_int
val parameter_location_mcts: parameter_location_t mfts_int
val bterm_mcts: bterm_t mfts_int
val gterm_mcts: gterm_t mfts_int

val function_stub_mcts: function_stub_t mfts_int
val call_target_mcts: call_target_t mfts_int
val c_struct_constant_mcts: c_struct_constant_t mfts_int
val xxpredicate_mcts: xxpredicate_t mfts_int
val xpo_predicate_mcts: xpo_predicate_t mfts_int

(** {1 Type inference} *)

val type_base_variable_mcts: type_base_variable_t mfts_int
val type_cap_label_mcts: type_cap_label_t mfts_int
val type_constant_mcts: type_constant_t mfts_int
val type_term_mcts: type_term_t mfts_int
val type_constraint_mcts: type_constraint_t mfts_int

(** {1 Memory references and variables} *)

val memory_base_mcts: memory_base_t mfts_int
val memory_offset_mcts: memory_offset_t mfts_int
val assembly_variable_denotation_mcts: assembly_variable_denotation_t mfts_int
val constant_value_variable_mcts: constant_value_variable_t mfts_int
val stack_access_mcts: stack_access_t mfts_int

val jump_target_mcts: jump_target_t mfts_int

val non_relational_value_mcts: non_relational_value_t mfts_int
val invariant_fact_mcts: invariant_fact_t mfts_int
val var_invariant_fact_mcts: var_invariant_fact_t mfts_int

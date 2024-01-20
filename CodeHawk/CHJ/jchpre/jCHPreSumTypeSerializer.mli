(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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

(* chutil *)
open CHSumTypeSerializer

(* jchlib *)
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI


val binopcode_mcts: opcode_t mfts_int

val converteropcode_mcts: opcode_t mfts_int

val variable_type_mfts: variable_type_t mfts_int

val non_virtual_target_type_mfts: non_virtual_target_type_t mfts_int

val call_targets_mcts: call_targets_t mfts_int

val taint_origin_type_mcts: taint_origin_type_t mfts_int

val taint_node_type_mcts: taint_node_type_t mfts_int

val bc_basicvalue_mcts: bc_basicvalue_t mfts_int

val bc_objectvalue_mcts: bc_objectvalue_t mfts_int

val bc_action_mcts: bc_action_t mfts_int

val bc_pattern_mcts: bc_pattern_t mfts_int

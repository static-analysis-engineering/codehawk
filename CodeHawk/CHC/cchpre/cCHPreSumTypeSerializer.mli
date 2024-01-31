(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHPEPRTypes

(* chutil *)
open CHSumTypeSerializer

(* cchpre *)
open CCHPreTypes


val bound_type_mfts: bound_type_t mfts_int

val dependencies_mcts: dependencies_t mfts_int

val po_status_mfts: po_status_t mfts_int

val address_type_mfts: address_type_t mfts_int

val assignment_mcts: assignment_t mfts_int

val global_value_mcts: global_value_t mfts_int

val po_predicate_mcts: po_predicate_t mfts_int

val assumption_type_mcts: assumption_type_t mfts_int

val ppo_type_mcts: ppo_type_t mfts_int

val spo_type_mcts: spo_type_t mfts_int

val memory_base_mcts: memory_base_t mfts_int

val constant_value_variable_mcts: constant_value_variable_t mfts_int

val c_variable_denotation_mcts: c_variable_denotation_t mfts_int

val non_relational_value_mcts: non_relational_value_t mfts_int

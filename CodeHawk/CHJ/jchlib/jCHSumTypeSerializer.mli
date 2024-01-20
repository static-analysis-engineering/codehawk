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

(* chutil *)
open CHSumTypeSerializer

(* jchlib *)
open JCHBasicTypesAPI


val java_basic_type_mfts: java_basic_type_t mfts_int

val reference_kind_mfts: reference_kind_t mfts_int

val object_type_mcts: object_type_t mfts_int

val value_type_mcts: value_type_t mfts_int

val constant_value_mcts: constant_value_t mfts_int

val descriptor_mcts: descriptor_t mfts_int

val method_handle_type_mcts: method_handle_type_t mfts_int

val constant_mcts: constant_t mfts_int

val bootstrap_argument_mcts: bootstrap_argument_t mfts_int

val opcode_mcts: opcode_t mfts_int

val arithmetic_op_mfts: arithmetic_op_t mfts_int

val relational_op_mfts: relational_op_t mfts_int

val jterm_mcts: jterm_t mfts_int

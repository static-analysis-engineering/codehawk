(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs, LLC

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

(* bchlibarm32 *)
open BCHARMTypes


val dmb_option_mfts: dmb_option_t mfts_int

val shift_rotate_type_mfts: shift_rotate_type_t mfts_int

val vfp_datatype_mcts: vfp_datatype_t mfts_int

val register_shift_rotate_mcts: register_shift_rotate_t mfts_int

val arm_opkind_mcts: arm_operand_kind_t mfts_int

val arm_opcode_cc_mfts: arm_opcode_cc_t mfts_int

val arm_memory_offset_mcts: arm_memory_offset_t mfts_int

val arm_simd_writeback_mcts: arm_simd_writeback_t mfts_int

val arm_simd_list_element_mcts: arm_simd_list_element_t mfts_int

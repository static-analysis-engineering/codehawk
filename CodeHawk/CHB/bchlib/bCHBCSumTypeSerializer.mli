(* =============================================================================
   CodeHawk Binary Analyzer C Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs LLC

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
open BCHBCTypes


val ikind_mfts: ikind_t mfts_int

val fkind_mfts: fkind_t mfts_int

val signedness_mfts: signedness_t mfts_int

val storage_mfts: bstorage_t mfts_int
val frepresentation_mfts: frepresentation_t mfts_int
val unop_mfts: unop_t mfts_int
val binop_mfts: binop_t mfts_int

val tname_mcts: tname_t mfts_int
val typ_mcts: btype_t mfts_int
val exp_mcts: bexp_t mfts_int
val constant_mcts: bconstant_t mfts_int
val offset_mcts: boffset_t mfts_int

val attrparam_mcts: b_attrparam_t mfts_int
val typsig_mcts: btypsig_t mfts_int

val label_mcts: blabel_t mfts_int
val stmtkind_mcts: bstmtkind_t mfts_int
val instr_mcts: binstr_t mfts_int

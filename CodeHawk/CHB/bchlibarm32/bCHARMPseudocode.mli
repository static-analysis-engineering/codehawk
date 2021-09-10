(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs, LLC

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


(* Documentation reference:
 * ========================
 * ARM Architecture Reference Manual
 * ARMv7-A and ARMv7-R edition, March 29, 2018
 *)

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes

val align: int -> int -> int

val get_dmb_option: int -> dmb_option_t

val get_opcode_cc: int -> arm_opcode_cc_t
val get_arm_reg: int -> arm_reg_t
val get_reglist_from_int: int -> int -> arm_reg_t list

val decode_imm_shift: int -> int -> shift_rotate_type_t * int
val decode_reg_shift: int -> shift_rotate_type_t

val sign_extend: int -> int -> int -> int
val arm_expand_imm_c: int -> int -> int -> (int * int)
val arm_expand_imm: int -> int -> int   (* rotate [ 11:8], imm[7:1] *)

val thumb_expand_imm_c: int -> int -> (int * int)
val thumb_expand_imm: int -> int -> int

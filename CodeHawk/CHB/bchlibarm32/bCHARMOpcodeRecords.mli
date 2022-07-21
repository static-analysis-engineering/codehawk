(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs, LLC

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
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


val get_cond_mnemonic_extension: arm_opcode_cc_t -> string

val get_arm_opcode_name: arm_opcode_t -> string

val is_cond_conditional: arm_opcode_cc_t -> bool

val is_opcode_conditional: arm_opcode_t -> bool

val get_arm_opcode_condition: arm_opcode_t -> arm_opcode_cc_t option

val get_arm_operands: arm_opcode_t -> arm_operand_int list

val get_arm_flags_set: arm_opcode_t -> arm_cc_flag_t list

val get_arm_flags_used: arm_opcode_t -> arm_cc_flag_t list

val arm_opcode_to_string: ?width:int -> arm_opcode_t -> string

val get_operands_written: arm_opcode_t -> arm_operand_int list

val get_operands_read: arm_opcode_t -> arm_operand_int list

(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSTypes

val select_mips_reg: int -> mips_reg_t
val decompose_instr: doubleword_int -> mips_instr_format_t
val instr_format_to_string: mips_instr_format_t -> string

val code_to_mips_fp_format: int -> mips_fp_format_t

val get_conditional_jump_expr: floc_int -> mips_opcode_t -> xpr_t 
val get_direct_jump_target_address: mips_opcode_t -> doubleword_int

val is_conditional_jump_instruction: mips_opcode_t -> bool
val is_fp_conditional_jump_instruction: mips_opcode_t -> bool
val is_direct_jump_instruction: mips_opcode_t -> bool
val is_indirect_jump_instruction: mips_opcode_t -> bool
val is_jump_instruction: mips_opcode_t -> bool
val is_halt_instruction: mips_opcode_t -> bool
val is_return_instruction: mips_opcode_t -> bool

val is_direct_call_instruction: mips_opcode_t -> bool
val is_indirect_call_instruction: mips_opcode_t -> bool
val get_direct_call_target_address: mips_opcode_t -> doubleword_int
val get_indirect_jump_instruction_register: mips_opcode_t -> mips_reg_t

val get_string_reference: floc_int -> xpr_t -> string option

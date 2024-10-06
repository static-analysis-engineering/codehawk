(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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

(* chlib *)
open CHNumerical

(* bchlib *)
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSTypes


(** The implementation of the assembly instruction operand type.*)


val mips_operand_mode_to_string: mips_operand_mode_t -> string
  
val mips_hi_op: mips_operand_mode_t -> mips_operand_int
val mips_lo_op: mips_operand_mode_t -> mips_operand_int
  
val mips_register_op: mips_reg_t -> mips_operand_mode_t -> mips_operand_int
  
val mips_fp_register_op: int -> mips_operand_mode_t -> mips_operand_int
  
val mips_indirect_register_op:
  mips_reg_t
  -> numerical_t
  -> mips_operand_mode_t
  -> mips_operand_int
  
val mips_immediate_op:
  bool  (* signed *)
  -> int (* size in bytes *)
  -> numerical_t   (* value *)
  -> mips_operand_int


val mips_absolute_op: doubleword_int -> mips_operand_mode_t -> mips_operand_int


(** [mk_mips_target_op ~delay iaddr imm] returns an absolute-address operand 
    with address value [iaddr + ((4 * imm) + delay)].*)
val mk_mips_target_op:
  ?delay:int
  -> doubleword_int
  -> int
  -> mips_operand_int


(** [mk_mips_absolute_target_op ?delay iaddr imm] returns an absolute-address
    operand with address value [4 * imm] added to [iaddr mod 2^28] where 
    [iaddr] is the instruction address. A [delay] value may be added if the
    base instruction address must be the delay slot. The resulting address
    value is in the same [256 MB] region as the instruction.*)
val mk_mips_absolute_target_op:
  ?delay:int
  -> doubleword_int
  -> int
  -> mips_operand_int

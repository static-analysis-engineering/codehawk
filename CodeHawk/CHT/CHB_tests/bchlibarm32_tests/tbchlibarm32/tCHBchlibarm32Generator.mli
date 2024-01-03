(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* tchlib *)
open TCHTestApi

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


val dmb_option: dmb_option_t generator_t


val dmb_option_operand: arm_operand_int generator_t


val ifthen_xyz: string generator_t


val arm_opcode_cc: arm_opcode_cc_t generator_t


val lsb_width_msb: (int * int * int) generator_t


val arm_reg: int generator_t -> arm_reg_t generator_t


val arm_reg_op:
  int generator_t -> arm_operand_mode_t -> arm_operand_int generator_t


val arm_imm_shift_reg_op:
  int generator_t -> arm_operand_mode_t -> arm_operand_int generator_t


val arm_rotated_reg_op:
  int generator_t -> arm_operand_mode_t -> arm_operand_int generator_t


val arm_reg_bit_sequence_op:
  int generator_t -> arm_operand_mode_t -> arm_operand_int generator_t


val arm_reglist_op: arm_operand_mode_t -> arm_operand_int generator_t


val arm_xsingle_reg_op: arm_operand_mode_t -> arm_operand_int generator_t


val arm_dual_xsingle_reg_op:
  arm_operand_mode_t
  -> (arm_operand_int * arm_operand_int * arm_operand_int) generator_t


val arm_xdouble_reg_op: arm_operand_mode_t -> arm_operand_int generator_t


val arm_xquad_reg_op: arm_operand_mode_t -> arm_operand_int generator_t


val arm_xsingle_reglist_op: arm_operand_mode_t -> arm_operand_int generator_t


val arm_xdouble_reglist_op: arm_operand_mode_t -> arm_operand_int generator_t


val arm_vfp_signed_unsigned_int_dt: vfp_datatype_t generator_t


val arm_vfp_op: bool -> arm_operand_mode_t -> arm_operand_int generator_t


val arm_expand_imm_int: int generator_t


val arm_literal_op: doubleword_int -> int -> arm_operand_int generator_t


val arm_absolute_op: arm_operand_mode_t -> arm_operand_int generator_t


val arm_imm_offset_address_op:
  arm_reg_t -> int -> arm_operand_mode_t -> arm_operand_int generator_t


val arm_index_offset_address_op:
  arm_reg_t -> arm_reg_t -> arm_operand_mode_t -> arm_operand_int generator_t


val arm_dual_index_offset_addresses_op:
  arm_reg_t
  -> arm_reg_t
  -> arm_operand_mode_t
  -> (arm_operand_int * arm_operand_int) generator_t


val arm_shifted_index_offset_address_op:
  arm_reg_t -> arm_reg_t -> arm_operand_mode_t -> arm_operand_int generator_t

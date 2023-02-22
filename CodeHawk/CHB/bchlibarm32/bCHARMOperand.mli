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

(* chlib *)
open CHPretty
open CHNumerical
open CHLanguage

(* chutil *)
open CHTraceResult
open CHXmlDocument

(* xprlib *)
open Xprt

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


val vfp_datatype_to_string: vfp_datatype_t -> string

val arm_operand_mode_to_string: arm_operand_mode_t -> string

val arm_index_offset: ?offset:int -> arm_reg_t -> arm_memory_offset_t

val arm_shifted_index_offset:
  ?offset:int -> arm_reg_t -> register_shift_rotate_t -> arm_memory_offset_t

val arm_dmb_option_op: dmb_option_t -> arm_operand_int

val arm_dmb_option_from_int_op: int -> arm_operand_int
  
val arm_register_op: arm_reg_t -> arm_operand_mode_t -> arm_operand_int

val arm_writeback_register_op:
  ?issingle:bool
  -> arm_reg_t
  -> int option
  -> arm_operand_mode_t
  -> arm_operand_int

val arm_special_register_op:
  arm_special_reg_t -> arm_operand_mode_t -> arm_operand_int

val arm_extension_register_op:
  arm_extension_reg_type_t -> int -> arm_operand_mode_t -> arm_operand_int

val arm_extension_register_element_op:
  arm_extension_reg_type_t
  -> int  (* register index *)
  -> int  (* element index *)
  -> int  (* element size *)
  -> arm_operand_mode_t
  -> arm_operand_int

val arm_register_list_op: arm_reg_t list -> arm_operand_mode_t -> arm_operand_int

val arm_extension_register_list_op:
  arm_extension_reg_type_t -> int -> int -> arm_operand_mode_t -> arm_operand_int

val arm_simd_reg_list_op:
  arm_extension_reg_type_t -> int list -> arm_operand_mode_t -> arm_operand_int

val arm_simd_reg_elt_list_op:
  arm_extension_reg_type_t
  -> int list   (* extension register indices *)
  -> int        (* element index *)
  -> int        (* element size *)
  -> arm_operand_mode_t
  -> arm_operand_int


val arm_simd_reg_rep_elt_list_op:
  arm_extension_reg_type_t
  -> int list   (* extension register indices *)
  -> int        (* element data size (in bytes *)
  -> int        (* element count *)
  -> arm_operand_mode_t
  -> arm_operand_int

val arm_immediate_op: immediate_int -> arm_operand_int

val arm_fp_constant_op: float -> arm_operand_int

val arm_absolute_op: doubleword_int -> arm_operand_mode_t -> arm_operand_int

val arm_literal_op:
  ?align:int
  -> ?is_add:bool
  -> doubleword_int    (* pc addr *)
  -> int               (* immediate offset *)
  -> arm_operand_int


val mk_arm_simd_address_op:
  arm_reg_t   (* base register *)
  -> int      (* alignment *)
  -> arm_simd_writeback_t
  -> arm_operand_mode_t
  -> arm_operand_int


val mk_arm_imm_shifted_register_op:
  arm_reg_t
  -> int (* shifttype *)
  -> int (* shiftamount *)
  -> arm_operand_mode_t
  -> arm_operand_int

val mk_arm_reg_shifted_register_op:
  arm_reg_t
  -> int   (* shifttype *)
  -> arm_reg_t  (* lowest byte is shift amount *)
  -> arm_operand_mode_t
  -> arm_operand_int

val mk_arm_rotated_register_op:
  arm_reg_t
  -> int (* rotation *)
  -> arm_operand_mode_t
  -> arm_operand_int

val mk_arm_reg_bit_sequence_op:
  arm_reg_t
  -> int  (* <lsb> bit number of least significant bit in the range 0-31 *)
  -> int  (* <widthm1> width-1 of the field, in the range 0 to 31-<lsb> *)
  -> arm_operand_mode_t
  -> arm_operand_int

val mk_arm_immediate_op:
  bool (* signed *)
  -> int (* size in bytes *)
  -> numerical_t (* value *)
  -> arm_operand_int traceresult

val mk_arm_absolute_target_op:
  doubleword_int
  -> int
  -> arm_operand_mode_t
  -> arm_operand_int

val mk_arm_offset_address_op:
  ?align:int    (* alignment of value in arm_reg *)
  -> ?size:int     (* size in bytes of the addressed object *)
  -> arm_reg_t
  -> arm_memory_offset_t   (* nonnegative offset *)
  -> isadd:bool
  -> iswback:bool
  -> isindex:bool
  -> arm_operand_mode_t
  -> arm_operand_int

val mk_arm_mem_multiple_op:
  ?align: int
  -> ?size: int
  -> arm_reg_t
  -> int
  -> arm_operand_mode_t
  -> arm_operand_int

val sp_r: arm_operand_mode_t -> arm_operand_int

val pc_r: arm_operand_mode_t -> arm_operand_int

val arm_sp_deref:
  ?with_offset:int
  -> arm_operand_mode_t
  -> arm_operand_int

val arm_reg_deref:
  ?with_offset:int
  -> arm_reg_t
  -> arm_operand_mode_t
  -> arm_operand_int

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
open BCHCPURegisters
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMPseudocode
open BCHARMTypes

module G = TCHGenerator
module U = TCHUtils

module BG = TCHBchlibGenerator

module TR = CHTraceResult


let e8   = 256
let e16  = e8 * e8


let operand_to_string = (fun op -> op#toString)


let dmb_option: dmb_option_t generator_t =
  ((fun r ->
    let v = (fst (G.select_int [2; 3; 6; 7; 10; 11; 14; 15])) r in
    get_dmb_option v), dmb_option_to_string)


let dmb_option_operand: arm_operand_int generator_t =
  ((fun r ->
    let option = (fst dmb_option) r in
    arm_dmb_option_op option),
   (fun op -> op#toString))


let ifthen_xyz: string generator_t =
  ((fun r ->
    let gen_c = G.select_letter ['T'; 'E'] in
    let gen_l = G.make_int 0 4 in
    let gen_s = G.string gen_l gen_c in
    (fst gen_s) r), U.string_of_string)


let lsb_width_msb: (int * int * int) generator_t =
  ((fun r ->
    let lsb = (fst (G.make_int 0 32)) r in
    let msb = (fst (G.make_int lsb 32)) r in
    let width = (msb - lsb) + 1 in
    (lsb, width, msb)),
   (fun (l, w, m) ->
     (string_of_int l) ^ ", " ^ (string_of_int w) ^ ", " ^ (string_of_int m)))


let arm_opcode_cc: arm_opcode_cc_t generator_t =
  ((fun r ->
    let wbool = (fst (G.make_bool 8 2)) r in
    if wbool then
      ACCAlways
    else
      get_opcode_cc ((fst (G.make_int 0 13)) r)),
   get_cond_mnemonic_extension)


let arm_reg (gen_i: int generator_t): arm_reg_t generator_t =
  ((fun r ->
    let index = (fst gen_i) r in
    get_arm_reg index), armreg_to_string)


let arm_reg_op
      (gen_i: int generator_t)
      (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let reg = (fst (arm_reg gen_i)) r in
    arm_register_op reg mode), operand_to_string)


let arm_imm_shift_reg_op
      (gen_i: int generator_t)
      (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let reg = (fst (arm_reg gen_i)) r in
    let ty = Random.State.int r 4 in
    let imm = Random.State.int r 32 in
    mk_arm_imm_shifted_register_op reg ty imm mode), operand_to_string)


let arm_rotated_reg_op
      (gen_i: int generator_t)
      (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let reg = (fst (arm_reg gen_i)) r in
    let rot = Random.State.int r 4 in
    let rotation = 8 * rot in
    mk_arm_rotated_register_op reg rotation mode), operand_to_string)


let arm_reg_bit_sequence_op
      (gen_i: int generator_t)
      (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let reg = (fst (arm_reg gen_i)) r in
    let lsb = Random.State.int r 32 in
    let widthm1 = fst (G.make_int 1 (32 - lsb)) r in
    mk_arm_reg_bit_sequence_op reg lsb widthm1 mode), operand_to_string)


let arm_reglist_op (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let spec = (fst (G.make_int 1 e16)) r in
    let rl = get_reglist_from_int 16 spec in
    arm_register_list_op rl mode), operand_to_string)


let arm_xsingle_reg_op (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let pbit = Random.State.int r 2 in
    let pval = Random.State.int r 16 in
    let d = postfix_bit pbit pval in
    let vd = arm_extension_register_op XSingle d in
    vd mode), operand_to_string)


let arm_dual_xsingle_reg_op (mode: arm_operand_mode_t):
      (arm_operand_int * arm_operand_int * arm_operand_int) generator_t =
  ((fun r ->
    let pbit = Random.State.int r 2 in
    let pval = Random.State.int r 15 in
    let d = postfix_bit pbit pval in
    let vd1 = arm_extension_register_op XSingle d mode in
    let vd2 = arm_extension_register_op XSingle (d+1) mode in
    let vdd = arm_double_extension_register_op XSingle d (d+1) mode in
    (vd1, vd2, vdd)),
   (fun (d1, d2, dd) ->
     "(" ^ d1#toString ^ ", " ^ d2#toString ^ ", " ^ dd#toString ^ ")"))


let arm_xdouble_reg_op (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let pbit = Random.State.int r 2 in
    let pval = Random.State.int r 16 in
    let d = prefix_bit pbit pval in
    let vd = arm_extension_register_op XDouble d in
    vd mode), operand_to_string)


let arm_xquad_reg_op (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let pbit = Random.State.int r 2 in
    let pval = Random.State.int r 16 in
    let d = prefix_bit pbit pval in
    let vd = arm_extension_register_op XQuad (d / 2) in
    vd mode), operand_to_string)


let arm_xsingle_reglist_op (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let pbit = Random.State.int r 2 in
    let pval = Random.State.int r 16 in
    let d = postfix_bit pbit pval in
    let maxregs = min 16 (32 - d) in
    let regs = Random.State.int r (maxregs + 1) in
    arm_extension_register_list_op XSingle d regs mode), operand_to_string)


let arm_xdouble_reglist_op (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let pbit = Random.State.int r 2 in
    let pval = Random.State.int r 15 in
    let d = prefix_bit pbit pval in
    let maxregs = min 16 (32 - d) in
    let regs = Random.State.int r (maxregs + 1) in
    arm_extension_register_list_op XDouble d regs mode), operand_to_string)


let arm_vfp_signed_unsigned_int_dt =
  ((fun r ->
    let signed = Random.State.bool r in
    let size = 8 lsl (Random.State.int r 3) in
    let dt = if signed then VfpSignedInt size else VfpUnsignedInt size in
    dt), vfp_datatype_to_string)


let arm_vfp_op
      (dp: bool) (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let reg = Random.State.int r 16 in
    let bit = Random.State.int r 2 in
    let vreg = if dp then prefix_bit bit reg else postfix_bit bit reg in
    let xtype = if dp then XDouble else XSingle in
    arm_extension_register_op xtype vreg mode), operand_to_string)


let arm_expand_imm_int: int generator_t =
  ((fun r ->
    let rot4 = Random.State.int r 15 in
    let imm8 = Random.State.int r 256 in
    arm_expand_imm rot4 imm8), string_of_int)


let arm_literal_op (base: doubleword_int) (imm: int): arm_operand_int generator_t =
  ((fun r ->
    let is_add = Random.State.bool r in
    arm_literal_op ~is_add (base#add_int 8) imm), operand_to_string)


let arm_absolute_op (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let dw = (fst BG.doubleword) r in
    arm_absolute_op dw mode), operand_to_string)


let arm_imm_offset_address_op
      (reg: arm_reg_t)
      (imm: int)
      (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let offset = ARMImmOffset imm in
    let isadd = Random.State.bool r in
    let iswback = Random.State.bool r in
    let isindex = Random.State.bool r in
    mk_arm_offset_address_op reg offset ~isadd ~isindex ~iswback mode),
   operand_to_string)


let arm_index_offset_address_op
      (basereg: arm_reg_t)
      (indexreg: arm_reg_t)
      (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let isadd = Random.State.bool r in
    let iswback = Random.State.bool r in
    let isindex = Random.State.bool r in
    let offset = arm_index_offset indexreg in
    mk_arm_offset_address_op basereg offset ~isadd ~isindex ~iswback mode),
   operand_to_string)


let arm_dual_index_offset_addresses_op
      (basereg: arm_reg_t)
      (indexreg: arm_reg_t)
      (mode: arm_operand_mode_t): (arm_operand_int * arm_operand_int) generator_t =
  ((fun r ->
    let isadd = Random.State.bool r in
    let iswback = Random.State.bool r in
    let isindex = Random.State.bool r in
    let offset = arm_index_offset indexreg in
    let offset2 = arm_index_offset ~offset:4 indexreg in
    let mem =
      mk_arm_offset_address_op basereg offset ~isadd ~isindex ~iswback mode in
    let mem2 =
      mk_arm_offset_address_op basereg offset2 ~isadd ~isindex ~iswback mode in
    (mem, mem2)), (fun (op1, op2) -> "(" ^ op1#toString ^ ", " ^ op2#toString ^ ")"))


let arm_shifted_index_offset_address_op
      (basereg: arm_reg_t)
      (indexreg: arm_reg_t)
      (mode: arm_operand_mode_t): arm_operand_int generator_t =
  ((fun r ->
    let isadd = Random.State.bool r in
    let iswback = Random.State.bool r in
    let isindex = Random.State.bool r in
    let shift_tb = Random.State.int r 4 in
    let shift_nb = Random.State.int r 32 in
    let (shift_t, shift_n) = decode_imm_shift shift_tb shift_nb in
    let regsrt = ARMImmSRT (shift_t, shift_n) in
    let offset = arm_shifted_index_offset indexreg regsrt in
    mk_arm_offset_address_op basereg offset ~isadd ~isindex ~iswback mode),
   operand_to_string)

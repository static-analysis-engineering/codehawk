(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023 Aarno Labs, LLC

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

(* bchlib *)
open CHPretty
open CHNumerical

(* chutil *)
open CHLogger
open CHPrettyUtil

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHDoubleword
open BCHImmediate
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings

(* bchlibarm32 *)
open BCHARMDisassemblyUtils
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMPseudocode
open BCHARMTypes

module B = Big_int_Z
module TR = CHTraceResult


(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16

let stri = string_of_int


let parse_data_proc_reg_misc (instr: doubleword_int) (cond: int) =
  (* bits 27 - 25: 000, bits 11 - 7: 1001 *)
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let c = get_opcode_cc cond in
  let rx = b 19 16 in
  let ry = b 15 12 in
  let rz = b 11 8 in
  let rt = b 3 0 in
  let r19 = arm_register_op (get_arm_reg rx) in
  let r15 = arm_register_op (get_arm_reg ry) in
  let r11 = arm_register_op (get_arm_reg rz) in
  let r3 = arm_register_op (get_arm_reg rt) in
  let setflags = (bv 20) = 1 in

  match (b 24 21) with
  (* <cc><0>0000s<rd>< 0><rm>1001<rn> *)    (* MUL - A1 *)
  | 0 when ry = 0 ->
     let rd = r19 WR in
     let rm = r11 RD in
     let rn = r3 RD in
     (* MUL{S}<c> <Rd>, <Rn>, <Rm> *)
     Multiply (setflags, c, rd, rn, rm)

  (* <cc><0>0001s<rd><ra><rm>1001<rn> *)   (* MLA - A1 *)
  | 1 ->
     let rd = r19 WR in
     let ra = r15 RD in
     let rm = r11 RD in
     let rn = r3 RD in
     (* MLA{S}<c> <Rd>, <Rn>, <Rm>, <Ra> *)
     MultiplyAccumulate (setflags, c, rd, rn, rm, ra)

  (* <cc><0>00110<rd><ra><rm>1001<rn> *)   (* MLS - A1 *)
  | 3 ->
     let rd = r19 WR in
     let ra = r15 RD in
     let rm = r11 RD in
     let rn = r3 RD in
     (* MLS<c> <Rd>, <Rn>, <Rm>, <Ra> *)
     MultiplySubtract (c, rd, rn, rm, ra)

  (* <cc><0>0100s<hi><lo><rm>1001<rn> *)   (* UMULL - A1   *)
  | 4 ->
     let rdhi = r19 WR in
     let rdlo = r15 WR in
     let rm = r11 RD in
     let rn = r3 RD in
     (* UMULL{S}<c> <RdLo>, <RdHi>, <Rn>, <Rm> *)
     UnsignedMultiplyLong (setflags, c, rdlo, rdhi, rn, rm)

  (* <cc><0>0110s<hi><lo><rm>1001<rn> *)   (* SMULL - A1 *)
  | 6 ->
     let rdhi = r19 WR in
     let rdlo = r15 WR in
     let rm = r11 RD in
     let rn = r3 RD in
     (* SMULL{S} <RdLo>, <RdHi>, <Rn>, <Rm> *)
     SignedMultiplyLong (setflags, c, rdlo, rdhi, rn, rm)

  (* <cc><0>0111s<hi><lo><rm>1001<rn> *)   (* SMLAL - A1 *)
  | 7 ->
     let rdhi = r19 WR in
     let rdlo = r15 WR in
     let rm = r11 RD in
     let rn = r3 RD in
     (* SMLAL{S} <RdLo>, <RdHi>, <Rn>, <Rm> *)
     SignedMultiplyAccumulateLong (setflags, c, rdlo, rdhi, rn, rm)

  (* <cc><0>10000<rn><rt>< 0>1001<rt> *)   (* SWP - A1 (deprecated) *)
  | 8 when (rz = 0) && (bv 20) = 0 ->
     let rnreg = get_arm_reg rx in
     let rt = r15 in
     let rt2 = r3 in
     let offset = ARMImmOffset 0 in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:false ~iswback:false in
     (* SWP{B}<c> <Rt>, <Rt2>, [<Rn>] *)
     Swap (c, rt WR, rt2 WR, mem WR)

  (* <cc><0>10100<rn><rt>< 0>1001<rt> *)   (* SWPB - A1 (deprecated) *)
  | 10 when (rz = 0) && (bv 20) = 0 ->
     let rnreg = get_arm_reg rx in
     let rt = r15 in
     let rt2 = r3 in
     let offset = ARMImmOffset 0 in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:false ~iswback:false in
     (* SWP{B}<c> <Rt>, <Rt2>, [<Rn>] *)
     SwapByte (c, rt WR, rt2 WR, mem WR)

  (* <cc><0>11000<rn><rn><15>1001<rt> *)    (* STREX - A1 *)
  | 12 when (rz = 15) && (bv 20) = 0 ->
     let rn = r19 in
     let rnreg = get_arm_reg rx in
     let rd = r15 in
     let rt = r3 in
     let offset = ARMImmOffset 0 in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:false ~iswback:false in
     (* STREX<c> <Rd>, <Rt>, [<Rn>] *)
     StoreRegisterExclusive (c, rd WR, rt RD, rn RD, mem WR)

  (* <cc><0>11001<rn><rt><15>1001<15> *)    (* LDREX - A1 *)
  | 12 when (rz = 15) && (rt = 15) && (bv 20) = 1 ->
     let rt = r15 in
     let rn = r19 in
     let rnreg = get_arm_reg rx in
     let offset = ARMImmOffset 0 in
     let immop = mk_arm_immediate_op false 4 numerical_zero in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:false ~iswback:false in
     (* LDREX<c> <Rt>, [<Rn>] *)
     LoadRegisterExclusive (c, rt WR, rn RD, immop, mem RD)

  | opc ->
     NotRecognized ("parse_data_proc_reg_misc:" ^ (stri opc), instr)


let parse_data_proc_reg_load_stores (instr: doubleword_int) (cond: int) =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  (* <cc><0>.................1..1.... *)  (* bit 7 = 1, bit 4 = 1 *)
  let c = get_opcode_cc cond in
  let p = bv 24 in
  let u = bv 23 in
  let w = bv 21 in
  let isindex = (p = 1) in
  let isadd = (u = 1) in
  let iswback = (w = 1) || (p = 0) in
  let rx = b 19 16 in
  let ry = b 15 12 in
  let rz = b 11 8 in
  let rv = b 3 0 in
  let r15 = arm_register_op (get_arm_reg ry) in

  let get_imm32 imm4H imm4L = (imm4H lsl 4) + imm4L in
  let selector = (bv 22, bv 20, b 6 5) in

  match selector with

  (* <cc><0>pu0w0<rn><rt>< 0>1011<rm> *)   (* STRH (register) - A1 *)
  | (0, 0, 1) when rz = 0 ->
     let rt = r15 RD in
     let rnreg = get_arm_reg rx in
     let rmreg = get_arm_reg rv in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = arm_index_offset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback WR in
     (* STRH{<c>} <Rt>, [<Rn>, +/-<Rm>]{!}    Pre-x : (index,wback) = (T,T/F)
      * STRH{<c>} <Rt>, [<Rn>], +/-<Rm>       Post-x: (index,wback) = (F,T) *)
     StoreRegisterHalfword (c, rt, rn, rm, mem, false)

  (* <cc><0>pu0w0<rn><rt>< 0>1101<rm> *)   (* LDRD (register) - A1 *)
  | (0, 0, 2) when rz = 0 ->
     let rt = r15 WR in
     let rt2 = arm_register_op (get_arm_reg (ry + 1)) WR in
     let rnreg = get_arm_reg rx in
     let rmreg = get_arm_reg rv in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = arm_index_offset rmreg in
     let offset2 = arm_index_offset ~offset:4 rmreg in
     let mem =
       mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     let mem2 =
       mk_arm_offset_address_op rnreg offset2 ~isadd ~isindex ~iswback RD in
     (* LDRD{<c>} <Rt>, <Rt2>, [<Rn>, +/-<Rm>]{!}  Pre-x : (index,wback) = (T,T/F)
      * LDRD{<c>} <Rt>, <Rt2>, [<Rn>], +/-<Rm>     Post-x: (index,wback) = (F,T) *)
     LoadRegisterDual (c, rt, rt2, rn, rm, mem, mem2)

  (* <cc><0>pu0w0<rn><rt>< 0>1111<rm> *)   (* STRD (register) - A1 *)
  | (0, 0, 3) when rz = 0 ->
     let rt = r15 RD in
     let rt2 = arm_register_op (get_arm_reg (ry + 1)) RD in
     let rnreg = get_arm_reg rx in
     let rmreg = get_arm_reg rv in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = arm_index_offset rmreg in
     let offset2 = arm_index_offset ~offset:4 rmreg in
     let mem =
       mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback WR in
     let mem2 =
       mk_arm_offset_address_op rnreg offset2 ~isadd ~isindex ~iswback WR in
     (* STRD<c> <Rt>, <Rt2>, [<Rn>, +/-<Rm>]{!}   Pre-x : (index,wback) = (T,T/F)
      * STRD<c> <Rt>, <Rt2>, [<Rn>], +/-<Rm>      Post-x: (index,wback) = (F,T)  *)
     StoreRegisterDual (c, rt, rt2, rn, rm, mem, mem2)

  (* <cc><0>pu0w1<rn><rt>< 0>1011<rm> *)   (* LDRH (register) - A1 *)
  | (0, 1, 1) when rz = 0 ->
     let rt = r15 WR in
     let rnreg = get_arm_reg rx in
     let rmreg = get_arm_reg rv in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = arm_index_offset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRH<c> <Rt>, [<Rn>, +/-<Rm>]{!}  Pre-x : (index,wback) = (T,T/F)
      * LDRH<c> <Rt>, [<Rn>], +/-<Rm>     Post-x: (index,wback) = (F,T)  *)
     LoadRegisterHalfword (c, rt, rn, rm, mem, false)

  (* <cc><0>pu0w1<rn><rt>< 0>1101<rm> *)   (* LDRSB (register) - A1 *)
  | (0, 1, 2) when rz = 0 ->
     let rt = r15 WR in
     let rnreg = get_arm_reg rx in
     let rmreg = get_arm_reg rv in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = arm_index_offset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRSB<c> <Rt>, [<Rn>,+/-<Rm>]{!}
      * LDRSB<c> <Rt>, [<Rn>],+/-<Rm> *)
     LoadRegisterSignedByte (c, rt, rn, rm, mem, false)

  (* <cc><0>pu0w1<rn><rt>< 0>1111<rm> *)   (* LDRSH (register) - A1 *)
  | (0, 1, 3) when rz = 0 ->
     let rt = r15 WR in
     let rnreg = get_arm_reg rx in
     let rmreg = get_arm_reg rv in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = arm_index_offset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRSH<c> <Rt>, [<Rn>,+/-<Rm>]{!} *)
     (* LDRSH<c> <Rt>, [<Rn>],+/-<rm> *)
     LoadRegisterSignedHalfword (c, rt, rn, rm, mem, false)

  (* <cc><0>pu1w0<rn><rt><iH>1011<iL> *)   (* STRH (immediate) - A1 *)
  | (1, 0, 1) ->
     let rt = r15 RD in
     let rnreg = get_arm_reg rx in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 rz rv in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int imm32)) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback WR in
     (* STRH<c> <Rt>, [<Rn>{, #+/-<imm8>}]      Offset: (index,wback) = (T,F)
      * STRH<c> <Rt>, [<Rn>, #+/-<imm>]!        Pre-x : (index,wback) = (T,T)
      * STRH<c> <Rt>, [<Rn>], #+/-<imm>         Post-x: (index,wback) = (F,T) *)
     StoreRegisterHalfword (c, rt, rn, imm, mem, false)

  (* <cc><0>pu1w0<rn><rt><iH>1101<iL> *)   (* LDRD (immediate) - A1 *)
  (* <cc><0>1u1001111<rt><iH>1101<iL> *)   (* LDRD-(literal) - A1 *)
  | (1, 0, 2) ->
     let rt = r15 WR in
     let rt2 = arm_register_op (get_arm_reg (ry + 1)) WR in
     let rnreg = get_arm_reg rx in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 rz rv in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int imm32)) in
     let offset = ARMImmOffset imm32 in
     let offset2 =
       if isadd then
         ARMImmOffset (imm32 + 4)
       else
         ARMImmOffset (imm32 - 4) in
     let mem =
       mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     let mem2 =
       mk_arm_offset_address_op rnreg offset2 ~isadd ~isindex ~iswback RD in
     (* LDRD<c> <Rt>, <Rt2>, [<Rn>{, #+/-<imm>}]   Offset: (index,wback) = (T,F)
      * LDRD<c> <Rt>, <Rt2>, [<Rn>, #+/-<imm>]!    Pre-x : (index,wback) = (T,T)
      * LDRD<c> <Rt>, <Rt2>, [<Rn>], #+/-<imm>     Post-x: (index,wback) = (F,T) *)
     LoadRegisterDual (c, rt, rt2, rn, imm, mem, mem2)

  (* <cc><0>pu1w0<rn><rt><iH>1111<iL> *)   (* STRD (immediate) - A1 *)
  | (1, 0, 3) ->
     let rt = r15 RD in
     let rt2 = arm_register_op (get_arm_reg (ry + 1)) RD in
     let rnreg = get_arm_reg rx in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 rz rv in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int imm32)) in
     let offset = ARMImmOffset imm32 in
     let offset2 =
       if isadd then
         ARMImmOffset (imm32 + 4)
       else
         ARMImmOffset (imm32 - 4) in
     let mem =
       mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback WR in
     let mem2 =
       mk_arm_offset_address_op rnreg offset2 ~isadd ~isindex ~iswback WR in
     (* STRD<c> <Rt>, <Rt2>, [<Rn>{, #+/-<imm>}]  Offset: (index,wback) = (T,F)
      * STRD<c> <Rt>, <Rt2>, [<Rn>, #+/-<imm>]!   Pre-x : (index,wback) = (T,T)
      * STRD<c> <Rt>, <Rt2>, [<Rn>], #+/-<imm>    Post-x: (index,wback) = (F,T) *)
     StoreRegisterDual (c, rt, rt2, rn, imm, mem, mem2)

  (* <cc><0>pu1w1<rn><rt><iH>1011<iL> *)   (* LDRH (immediate) - A1 *)
  (* <cc><0>pu1w11111<rt><iH>1011<iL> *)   (* LDRH-(literal) - A1 *)
  | (1, 1, 1) ->
     let rt = r15 WR in
     let rnreg = get_arm_reg rx in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 rz rv in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int imm32)) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRH<c> <Rt>, [<Rn>{, #+/-<imm>}]       Offset: (index,wback) = (T,F)
      * LDRH<c> <Rt>, [<Rn>, #+/-<imm>]!        Pre-x : (index,wback) = (T,T)
      * LDRH<c> <Rt>, [<Rn>], #+/-<imm>         Post-x: (index,wback) = (F,T) *)
     LoadRegisterHalfword (c, rt, rn, imm, mem, false)

  (* <cc><0>pu1w1<rn><rt><iH>1101<iL> *)   (* LDRSB (immediate) - A1 *)
  | (1, 1, 2) ->
     let rt = r15 WR in
     let rnreg = get_arm_reg rx in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 rz rv in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int imm32)) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRSB<c> <Rt>, [<Rn>{, #+/-<imm8>}]
      * LDRSB<c> <Rt>, [<Rn>], #+/-<imm8>
      * LDRSB<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     LoadRegisterSignedByte (c, rt, rn, imm, mem, false)

  (* <cc><0>pu1w1<rn><rt><iH>1111<iL> *)   (* LDRSH (immediate) - A1 *)
  | (1, 1, 3) ->
     let rt = r15 WR in
     let rnreg = get_arm_reg rx in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 rz rv in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int imm32)) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRSH<c> <Rt>, [<Rn>{, #+/-<imm8>}]
      * LDRSH<c> <Rt>, [<Rn>], #+/-<imm8>
      * LDRSH<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     LoadRegisterSignedHalfword (c, rt, rn, imm, mem, false)

  | (k, l, m) ->
     NotRecognized
       ("data_proc_reg_load_stores:"
        ^ (stri k)
        ^ "_"
        ^ (stri l)
        ^ "_"
        ^ (stri m),
        instr)


let parse_data_proc_reg_type (instr: doubleword_int) (cond: int) =
  (* not (bit 7 = 1 and bit 4 = 1) *)
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let c = get_opcode_cc cond in
  let mk_imm_shift_reg r ty imm mode =
    mk_arm_imm_shifted_register_op (get_arm_reg r) ty imm mode in
  let mk_reg_shift_reg r ty reg mode =
    mk_arm_reg_shifted_register_op (get_arm_reg r) ty (get_arm_reg reg) mode in
  let rx = b 19 16 in
  let ry = b 15 12 in
  let rz = b 11 8 in
  let rt = b 3 0 in
  let b4 = bv 4 in
  let r19 = arm_register_op (get_arm_reg rx) in
  let r15 = arm_register_op (get_arm_reg ry) in
  let r11 = arm_register_op (get_arm_reg rz) in
  let r3 = arm_register_op (get_arm_reg rt) in
  let setflags = (b 20 20) = 1 in
  let opc = b 24 21 in

  match opc with
  (* <cc><0>< 0>s<rn><rd><imm>ty0<rm> *)   (* AND (register) - A1 *)
  | 0 when (b4 = 0) ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* AND{S}<c> <Rd>, <Rn>{, <shift>} *)
     BitwiseAnd (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 0>s<rn><rd><rs>0ty1<rm> *) (* AND (register-shifted register) - A1 *)
  | 0 when (b4 = 1) ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* AND{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     BitwiseAnd (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 1>s<rn><rd><imm>ty0<rm> *)   (* EOR (register) - A1 *)
  | 1 when (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* EOR{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseExclusiveOr (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 1>s<rn><rd><rs>0ty1<rm> *) (* EOR (register-shifted register) - A1 *)
  | 1 when (b4 = 1) && (b 7 7) = 0 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* EOR{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     BitwiseExclusiveOr (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 2>s<rn><rd><imm>ty0<rm> *)    (* SUB (register) - A1 *)
  | 2 when (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* SUB{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     Subtract (setflags, c, rd, rn, rm, false, false)

  (* <cc><0>< 2>s<rn><rd><rs>0ty1<rm> *) (* SUB (register-shifted register) - A1 *)
  | 2 when (b4 = 1) && (b 7 7) = 0 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* SUB{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     Subtract (setflags, c, rd, rn, rm, false, false)

  (* <cc><0>< 3>s<rn><rd><imm>ty0<rm> *)   (* RSB (register) - A1 *)
  | 3 when (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* RSB{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     ReverseSubtract(setflags, c, rd, rn, rm, false)

  (* <cc><0>< 3>s<rn><rd><rs>0ty1<rm> *) (* RSB (register-shifted register) - A1 *)
  | 3 when (b4 = 1) && (b 7 7) = 0 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* RSB{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     ReverseSubtract(setflags, c, rd, rn, rm, false)

  (* <cc><0>< 4>s<rn><rd><imm>ty0<rm> *)   (* ADD (register) - A1 *)
  | 4 when (not ((ry = 15) && setflags)) && (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* ADD{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     Add (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 4>s<rn><rd><rs>0ty1<rm> *) (* ADD (register-shifted register) - A1 *)
  | 4 when (b 7 7) = 0 && (b4 = 1) ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* ADD{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     Add (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 5>s<rn><rd><imm>ty0<rm> *)   (* ADC (register) - A1 *)
  | 5 when (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* ADC{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     AddCarry (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 5>s<rn><rd><rs>0ty1<rm> *) (* ADC (register-shifted register) - A1 *)
  | 5 when (b4 = 1) && (b 7 7) = 0 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* ADC{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     AddCarry (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 6>s<rn><rd><imm>ty0<rm> *)   (* SBC (register) - A1 *)
  | 6 when (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* SBC{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     SubtractCarry (setflags, c, rd, rn, rm, false)

  (* <cc><0>< 7>s<rn><rd><imm>ty0<rm> *)   (* RSC (register) - A1 *)
  | 7 when (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* RSC{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     ReverseSubtractCarry (setflags, c, rd, rn, rm)

  (* <cc><0>< 7>s<rn><rd><rs>0ty1<rm> *) (* RSC (register-shifted register) - A1 *)
  | 7 when (b4 = 1) && (b 7 7) = 0 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* ADC{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     ReverseSubtractCarry (setflags, c, rd, rn, rm)

  (* <cc><0>< 8>1<rn>< 0><imm>ty0<rm> *)   (* TST (register) - A1 *)
  | 8 when setflags && (ry = 0) && (b4 = 0) ->
     let rn = r19 RD in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* TST<c> <Rn>, <Rm>{, <shift>} *)
     Test (c, rn, rm)

  (* <cc><0>< 8>1<rn>< 0><rs>0ty1<rm> *) (* TST (register-shifted register) - A1 *)
  | 8 when setflags && (ry = 0) && (b 7 7) = 0 && (b4 = 1) ->
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* TST<c> <Rn>, <Rm>, <type> <Rs> *)
     Test (c, rn, rm)

  (* <cc><0>< 9>0<15><15><15>0001<rm> *)   (* BX - A1 *)
  | 9 when (not setflags) && (rx = 15) && (ry = 15) && (rz = 15) && (b 7 4) = 1 ->
     (* BX<c> <Rm> *)
     BranchExchange(c, r3 RD)

  (* <cc><0>< 9>0<15><15><15>0011<rm> *)   (* BLX (register) - A1 *)
  | 9 when (not setflags) && (rx = 15) && (ry = 15) && (rz = 15) && (b 7 4) = 3 ->
     (* BLX<c> <Rm> *)
     BranchLinkExchange(c, r3 RD)

  (* <cc><0>< 9>1<rn>< 0><imm>ty0<rm> *)   (* TEQ (register) - A1 *)
  | 9 when setflags && (ry = 0) && (b4 = 0) ->
     let rn = r19 RD in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* TEQ<c> <Rn>, <Rm>{, <shift>} *)
     TestEquivalence (c, rn, rm)

  (* <cc><0>< 9>1<rn>< 0><rs>0ty1<rm> *) (* TEQ (register-shifted register) - A1 *)
  | 9 when setflags && (ry = 0) && (b4 = 1) && (b 7 7) = 0 ->
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* TEQ<c> <Rn>, <Rm>, <type> <Rs> *)
     TestEquivalence (c, rn, rm)

  (* <cc><0><10>1<rn>< 0><imm>ty0<rm> *)   (* CMP (register) - A1 *)
  | 10 when setflags && (ry = 0) && (b4 = 0) ->
     let rn = r19 RD in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* CMP<c> <Rn>, <Rm>{, <shift>} *)
     Compare (c, rn, rm, false)

  (* <cc><0><10>1<rn>< 0><rs>0ty1<rm> *) (* CMP (register-shifted register) - A1 *)
  | 10 when setflags && (ry = 0) && (b4 = 1) && (b 7 7) = 0 ->
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* CMP<c> <Rn>, <Rm>, <type> <Rs> *)
     Compare (c, rn, rm, false)

  (* <cc><0><11>0<15><rd><15>0001<rm> *)   (* CLZ - A1 *)
  | 11 when (not setflags) && rx = 15 && rz = 15 && (b 7 4) = 1 ->
     let rd = r15 WR in
     let rm = r3 RD in
     (* CLZ<c> <Rd>, <Rm> *)
     CountLeadingZeros (c, rd, rm)

  (* <cc><0><11>1<rn>< 0><imm>ty0<rm> *)   (* CMN (register) - A1 *)
  | 11 when setflags && (ry = 0) && (b4 = 0) ->
     let rn = r19 RD in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* CMM<c> <Rn>, <Rm>{, <shift>} *)
     CompareNegative (c, rn, rm)

  (* <cc><0><11>1<rn>< 0><rs>0ty1<rm> *) (* CMN (register-shifted register) - A1 *)
  | 11 when setflags && (ry = 0) && (b4 = 1) && (b 7 7) = 0 ->
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* CMN<c> <Rn>, <Rm>, <type> <Rs> *)
     CompareNegative (c, rn, rm)

  (* <cc><0><12>s<rn><rd><imm>ty0<rm> *)   (* ORR (register) - A1 *)
  | 12 when (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* ORR{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseOr (setflags, c, rd, rn, rm, false)

  (* <cc><0><12>s<rn><rd><rs>0ty1<rm> *) (* ORR (register-shifted register) - A1 *)
  | 12 when (b4 = 1) && (b 7 7) = 0 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* ORR{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     BitwiseOr (setflags, c, rd, rn, rm, false)

  (* <cc><0><13>s< 0><rd>< 0>0000<rm> *)   (* MOV (register) A1 *)
  | 13 when (rx = 0) && (b 11 4) = 0 ->
     let rd = r15 WR in
     let rm = r3 RD in
     (* MOV{S}<c> <Rd>, <Rm> *)
     Move (setflags, c, rd, rm, false, false)

  (* <cc><0><13>s< 0><rd><imm>000<rm> *)   (* LSL (immediate) - A1 *)
  | 13 when (rx = 0) && (b 6 4) = 0 ->
     let rd = r15 WR in
     let rm = r3 RD in
     let (_,imm) = decode_imm_shift 0 (b 11 7) in
     let imm = mk_arm_immediate_op false 4 (mkNumerical imm) in
     (* LSL{S}<c> <Rd>, <Rm>, #<imm> *)
     LogicalShiftLeft (setflags, c, rd, rm, imm, false)

  (* <cc><0><13>s< 0><rd><rm>0001<rn> *)   (* LSL (register) - A1 *)
  |13 when (rx = 0) && (b 7 4) = 1 ->
     let rd = r15 WR in
     let rm = r11 RD in
     let rn = r3 RD in
     (* LSL{S}<c> <Rd>, <Rn>, <Rm> *)
     LogicalShiftLeft (setflags, c, rd, rn, rm, false)

  (* <cc><0><13>s< 0><rd><imm>010<rm> *)   (* LSR (immediate) - A1 *)
  | 13 when (rx = 0) && (b 6 4) = 2 ->
     let rd = r15 WR in
     let rm = r3 RD in
     let (_,imm) = decode_imm_shift 1 (b 11 7) in
     let imm = mk_arm_immediate_op false 4 (mkNumerical imm) in
     (* LSR{S}<c> <Rd>, <Rm>, #<imm> *)
     LogicalShiftRight (setflags, c, rd, rm, imm, false)

  (* <cc><0><13>s< 0><rd><rm>0011<rn> *)   (* LSR (register) - A1 *)
  | 13 when (rx = 0) && (b 7 4) = 3 ->
     let rd = r15 WR in
     let rm = r11 RD in
     let rn = r3 RD in
     (* LSR{S}<c> <Rd>, <Rn>, <Rm> *)
     LogicalShiftRight (setflags, c, rd, rn, rm, false)

  (* <cc><0><13>s< 0><rd><imm>100<rm> *)   (* ASR (immediate) - A1 *)
  | 13 when (rx = 0) && (b 6 4) = 4 ->
     let rd = r15 WR in
     let rm = r3 RD in
     let (_,imm) = decode_imm_shift 2 (b 11 7) in
     let imm = mk_arm_immediate_op false 4 (mkNumerical imm) in
     (* ASR{S}<c> <Rd>, <Rm>, #<imm> *)
     ArithmeticShiftRight (setflags, c, rd, rm, imm, false)

  (* <cc><0><13>s< 0><rd><rm>0101<rn> *)   (* ASR (register) - A1 *)
  | 13 when (rx = 0) && (b 7 4) = 5 ->
     let rd = r15 WR in
     let rm = r11 RD in
     let rn = r3 RD in
     (* ASR{S}<c> <Rd>, <Rn>, <Rm> *)
     ArithmeticShiftRight (setflags, c, rd, rn, rm, false)

  (* <cc><0><13>s< 0><rd>< 0>0110<rm> *)   (* RRX - A1 *)
  | 13 when (rx = 0) && (b 11 4) = 6 ->
     let rd = r15 WR in
     let rm = r3 RD in
     (* RRX{S}<c> <Rd>, <Rm> *)
     RotateRightExtend (setflags, c, rd, rm)

  (* <cc><0><13>s< 0><rd><imm>110<rm> *)   (* ROR (immediate) - A1 *)
  | 13 when (rx = 0) && (b 6 4) = 6 ->
     let rd = r15 WR in
     let rm = r3 RD in
     let (_,imm) = decode_imm_shift 2 (b 11 7) in
     let imm = mk_arm_immediate_op false 4 (mkNumerical imm) in
     (* ROR{S}<c> <Rd>, <Rm>, #<imm> *)
     RotateRight (setflags, c, rd, rm, imm)

  (* <cc><0><13>s< 0><rd><rm>0111<rn> *)   (* ROR (register) - A1 *)
  | 13 when (rx = 0) && (b 7 4) = 7 ->
     let rd = r15 WR in
     let rm = r11 RD in
     let rn = r3 RD in
     (* ROR{S}<c> <Rd>, <Rn>, <Rm> *)
     RotateRight (setflags, c, rd, rn, rm)

  (* <cc><0><14>s<rn><rd><imm>ty0<rm> *)   (* BIC (register) - A1 *)
  | 14 when (b4 = 0) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* BIC{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseBitClear (setflags, c, rd, rn, rm, false)

  (* <cc><0><14>s<rn><rd><rs>0ty1<rm> *) (* BIC (register-shifted register) - A1 *)
  | 14 when (b4 = 1) && (b 7 7) = 0 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* BIC{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     BitwiseBitClear (setflags, c, rd, rn, rm, false)

  (* <cc><0><15>s< 0><rd><imm>ty0<rm> *)   (* MVN (register) - A1 *)
  | 15 when (rx = 0) && (b4 = 0) ->
     let rd = r15 WR in
     let rm = mk_imm_shift_reg rt (b 6 5) (b 11 7) RD in
     (* MVN{S}<c> <Rd>, <Rm>{, <shift>} *)
     BitwiseNot (setflags, c, rd, rm, false)

  (* <cc><0><15>s< 0><rd><rs>0ty1<rm> *) (* MVN (register-shifted register) - A1 *)
  | 15 when (rx = 0) && (b4 = 1) && (b 7 7) = 0 ->
     let rd = r15 WR in
     let rm = mk_reg_shift_reg rt (b 6 5) rz RD in
     (* MVN{S}<c> <Rd>, <Rm>, <type> <Rs> *)
     BitwiseNot (setflags, c, rd, rm, false)

  | _ ->
     NotRecognized ("data_proc_reg_type:" ^ (stri opc), instr)


let parse_data_proc_imm_type
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int)
      (cond: int) =
  let b = instr#get_segval in
  let opc = b 24 21 in
  let c = get_opcode_cc cond in
  let mk_imm (rotate: int) (imm: int) =
    let imm32 = arm_expand_imm rotate imm in
    let imm32 = TR.tget_ok (make_immediate false 4 (B.big_int_of_int imm32)) in
    arm_immediate_op imm32 in
  let mk_imm16 (imm4: int) (rotate: int) (imm: int) =
    (imm4 lsl 12) + (rotate lsl 8) + imm in
  let setflags = (b 20 20) = 1 in
  let rx = b 19 16 in
  let ry = b 15 12 in
  let r19 = arm_register_op (get_arm_reg rx) in
  let r15 = arm_register_op (get_arm_reg ry) in

  match opc with
  (* <cc><1>< 0>s<rn><rd><--imm12---> *)   (* AND (immediate) - A1 *)
  | 0 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* AND{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseAnd (setflags, c, rd, rn, imm, false)

  (* <cc><1>< 1>s<rn><rd><--imm12---> *)   (* EOR (immediate) - A1 *)
  | 1 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* EOR{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseExclusiveOr (setflags, c, rd, rn, imm, false)

  (* <cc><1>< 2>0<15><rd><--imm12---> *)   (* ADR - A2 *)
  | 2 when rx = 15 && (not setflags) ->
     let rd = r15 WR in
     let imm32 = arm_expand_imm (b 11 8) (b 7 0) in
     (try
        let base = iaddr#add_int 8 in
        let imm = mk_arm_absolute_target_op base (-imm32) RD in
        (* ADR<c> <Rd>, <label> *)
        Adr (c, rd, imm)
      with
      | Invalid_argument s ->
         NotRecognized ("error in ADR (A2): " ^ s, instr))

  (* <cc><1>< 2>s<rn><rd><--imm12---> *)   (* SUB (immediate) - A1 *)
  | 2 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* SUB{S}<c> <Rd>, <Rn>, #<const> *)
     Subtract (setflags, c, rd, rn, imm, false, false)

  (* <cc><1>< 3>s<rn><rd><--imm12---> *)   (* RSB (immediate) - A1 *)
  | 3 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* RSB{S}<c> <Rd>, <Rn>, #<const> *)
     ReverseSubtract (setflags, c, rd, rn, imm, false)

  (* <cc><1>< 4>0<15><rd><--imm12---> *)   (* ADR - A1 *)
  | 4 when rx = 15 && (not setflags) ->
     let rd = r15 WR in
     let imm32 = arm_expand_imm (b 11 8) (b 7 0) in
     (try
        let imm = mk_arm_absolute_target_op iaddr imm32 RD in
        (* ADR<c> <Rd>, <label> *)
        Adr (c, rd, imm)
      with
      | Invalid_argument s ->
         NotRecognized ("error in ADR (A1): " ^ s, instr))

  (* <cc><1>< 4>s<rn><rd><--imm12---> *)   (* ADD (immediate) - A1 *)
  | 4 ->
     let rd = r15 WR in
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* ADD{S}<c> <Rd>, <Rn>, #<const> *)
     Add (setflags, c, rd, rn, imm, false)

  (* <cc><1>< 5>s<rn><rd><--imm12---> *)   (* ADC (immediate) - A1 *)
  | 5 when not (ry = 15 && setflags) ->
     let rd = r15 WR in
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* ADC{S}<c> <Rd>, <Rn>, #<const> *)
     AddCarry (setflags, c, rd, rn, imm, false)

  (* <cc><1>< 6>s<rn><rd><--imm12---> *)   (* SBC (immediate) - A1 *)
  | 6 when not (ry = 15 && setflags) ->
     let rd = r15 WR in
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* SBC{S}<c> <Rd>, <Rn>, #<const> *)
     SubtractCarry (setflags, c, rd, rn, imm, false)

  (* <cc><1>< 7>s<rn><rd><--imm12---> *)   (* RSC (immediate) - A1 *)
  | 7 when not (ry = 15 && setflags) ->
     let rd = r15 WR in
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* RSC{S}<c> <Rd>, <Rn>, #<const> *)
     ReverseSubtractCarry (setflags, c, rd, rn, imm)

  (* <cc><1>< 8>0<i4><rd><--imm12---> *)   (* MOVW (immediate) - A2 *)
  | 8 when not setflags ->
     let rd = r15 WR in
     let immval = ((b 19 16) lsl 12) + ((b 11 8) lsl 8) + (b 7 0) in
     let imm32 = TR.tget_ok (make_immediate false 4 (B.big_int_of_int immval)) in
     let imm = arm_immediate_op imm32 in
     (* MOVW<c> <Rd>, #<imm16> *)
     Move (false, c, rd, imm, false, true)

  (* <cc><1>< 8>1<rn>< 0><--imm12---> *)   (* TST (immediate) - A1 *)
  | 8 when setflags && (ry = 0) ->
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* TST<c> <Rn>, #<const> *)
     Test (c, rn, imm)

  (* <cc><1>< 9>0< 0><15><--imm12:0-> *)   (* NOP - A1 *)
  | 9 when not setflags && (rx = 0) && (ry = 15) && (b 11 0) = 0 ->
     (* NOP<c> *)
     NoOperation c

  (* <cc><1>< 9>1<rn>< 0><--imm12---> *)   (* TEQ (immediate) - A1 *)
  | 9 when setflags && (ry = 0) ->
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* TEQ<c> <Rn>, #<const> *)
     TestEquivalence (c, rn, imm)

  (* <cc><1><10>0<i4><rd><--imm12---> *)   (* MOVT - A1    *)
  | 10 when not setflags ->
     let rd = r15 WR in
     let imm16 = mk_imm16 (b 19 16) (b 11 8) (b 7 0) in
     let imm16 = TR.tget_ok (make_immediate false 2 (B.big_int_of_int imm16)) in
     let imm = arm_immediate_op imm16 in
     (* MOVT<c> <Rd>, #<imm16> *)
     MoveTop (c, rd, imm)

  (* <cc><1><10>1<rn>< 0><--imm12---> *)   (* CMP (immediate) - A1 *)
  | 10 when setflags && (ry = 0) ->
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* CMP<c> <Rn>, #<const> *)
     Compare (c, rn, imm, false)

  (* <cc><1><11>1<rn>< 0><--imm12---> *)   (* CMN (immediate) - A1 *)
  | 11 when setflags && (ry = 0) ->
     let rn = r19 RD in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* CMN<c> <Rn>, #<const> *)
     CompareNegative (c, rn, imm)

  (* <cc><1><12>s<rn><rd><--imm12---> *)   (* ORR (immediate) - A1 *)
  | 12 when not (setflags && (ry = 15)) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* ORR{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseOr (setflags, c, rd, rn, imm, false)

  (* <cc><1><13>s< 0><rd><--imm12---> *)   (* MOV (immediate) - A1 *)
  | 13 when not (setflags && (ry = 15)) ->
     let rd = r15 WR in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* MOV{S}<c> <Rd>, #<const> *)
     Move (setflags, c, rd, imm, false, false)

  (* <cc><1><14>s<rn><rd><--imm12---> *)   (* BIC (immediate) - A1 *)
  | 14 when not (setflags && (ry = 15)) ->
     let rn = r19 RD in
     let rd = r15 WR in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* BIC{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseBitClear (setflags, c, rd, rn, imm, false)

  (* <cc><1><15>s< 0><rd><--imm12---> *)   (* MVN (immediate) - A1 *)
  | 15 when rx = 0 ->
     let rd = r15 WR in
     let imm = mk_imm (b 11 8) (b 7 0) in
     (* MVN{S}<c> <Rd>, #<const> *)
     BitwiseNot (setflags, c, rd, imm, false)

  | _ ->
     NotRecognized ("data_proc_imm_type:" ^ (stri opc), instr)


let parse_load_store_imm_type
      (iaddr: doubleword_int) (instr: doubleword_int) (cond: int) =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let c = get_opcode_cc cond in
  let p = (bv 24) = 1 in
  let u = (bv 23) = 1 in
  let w = (bv 21) = 1 in
  let isadd = u in
  let iswback = (not p) || w in
  let isindex = p in
  let rnval = b 19 16 in
  let rnreg = get_arm_reg rnval in
  let rn = arm_register_op rnreg (if iswback then RW else RD) in
  let rt = arm_register_op (get_arm_reg (b 15 12)) in
  let imm12 = b 11 0 in
  let imm = mk_arm_immediate_op false 4 (mkNumerical imm12) in
  let offset = ARMImmOffset imm12 in
  let mk_mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
  match (b 22 22, b 20 20, (rnval, p, u, w, imm12)) with

  (* <cc><2>10010<13><rt><--imm12:4-> *)   (* PUSH - A2 *)
  | (0, 0, (13, true, false, true, 4)) ->
     let rl = arm_register_list_op [get_arm_reg (b 15 12)] RD in
     (* PUSH<c> <registers> *)
     Push (c, rn, rl, false)

  (* <cc><2>pu0w0<rn><rt><--imm12---> *)   (* STR (immediate) - A1 *)
  | (0, 0, _) ->
     let mem = mk_mem WR in
     (* STR<c> <Rt>, [<Rn>{, #+/-<imm12>}]       Offset: (index,wback) = (T,F)
      * STR<c> <Rt>, [<Rn>, #+/-<imm12>]!        Pre-x : (index,wback) = (T,T)
      * STR<c> <Rt>, [<Rn>], #+/-<imm12>         Post-x: (index,wback) = (F,T) *)
     StoreRegister (c, rt RD ,rn, imm, mem, false)

  (* <cc><2>01001<13><rt><-imm12:4--> *)   (* POP - A2 *)
  | (0, 1, (13, false, true, false, 4)) ->
     let rl = arm_register_list_op [(get_arm_reg (b 15 12))] WR in
     (* POP<c> <registers> *)
     Pop (c, rn, rl, false)

  (* <cc><2>pu011<15><rt><--imm12---> *)   (* LDR (literal) - A1 *)
  | (0, 1, (15, _, _, _, _)) ->
     let addrop = arm_literal_op ~is_add:isadd (iaddr#add_int 8) imm12 in
     (* LDR<c> <Rt>, <label> *)
     LoadRegister (c, rt WR, rn, imm, addrop, false)

  (* <cc><2>pu0w1<rn><rt><--imm12---> *)   (* LDR (immediate) - A1 *)
  | (0, 1, _) ->
     let mem = mk_mem RD in
     (* LDR<c> <Rt>, [<Rn>{, #+/-<imm12>}]       Offset: (index,wback) = (T,F)
      * LDR<c> <Rt>, [<Rn>, #+/-<imm12>]!        Pre-x : (index,wback) = (T,T)
      * LDR<c> <Rt>, [<Rn>], #+/-<imm12>         Post-x: (index,wback) = (F,T) *)
     LoadRegister (c, rt WR, rn, imm, mem, false)

  (* <cc><2>pu1w0<rn><rt><--imm12---> *)   (* STRB-imm *)
  | (1, 0, _) ->
     let mem = mk_mem WR in
     (* STRB<c> <Rt>, [<Rn>{, #+/-<imm12>}]       Offset: (index,wback) = (T,F)
      * STRB<c> <Rt>, [<Rn>, #+/-<imm12>]!        Pre-x : (index,wback) = (T,T)
      * STRB<c> <Rt>, [<Rn>], #+/-<imm12>         Post-x: (index,wback) = (F,T) *)
     StoreRegisterByte (c, rt RD, rn, imm, mem, false)

  (* <cc><2>pu1w1<rn><rt><--imm12---> *)   (* LDRB-imm *)
  | (1, 1, _) ->
     let mem = mk_mem RD in
     (* LDRB<c> <Rt>, [<Rn>{, #+/-<imm12>}]       Offset: (index,wback) = (T,F)
      * LDRB<c> <Rt>, [<Rn>, #+/-<imm12>]!        Pre-x : (index,wback) = (T,T)
      * LDRB<c> <Rt>, [<Rn>], #+/-<imm12>         Post-x: (index,wback) = (F,T) *)
     LoadRegisterByte (c, rt WR, rn, imm, mem, false)

  | (k, l, _) ->
     NotRecognized
       ("parse_load_store_imm_type:"
        ^ (stri k)
        ^ "_"
        ^ (stri l),
        instr)


let parse_load_store_reg_type (instr: doubleword_int) (cond: int) =
  (* bitval 4 = 0 *)
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let c = get_opcode_cc cond in
  let p = (bv 24) = 1 in
  let u = (bv 23) = 1 in
  let w = (bv 21) = 1 in
  let isadd = u in
  let iswback = (not p) || w in
  let isindex = p in
  let rnreg = get_arm_reg (b 19 16) in
  let rm = arm_register_op (get_arm_reg (b 3 0)) RD in
  let rn = arm_register_op rnreg (if iswback then RW else RD) in
  let rt = arm_register_op (get_arm_reg (b 15 12)) in
  let (shift_t, shift_n) = decode_imm_shift (b 6 5) (b 11 7) in
  let reg_srt = ARMImmSRT (shift_t, shift_n) in
  let offset = arm_shifted_index_offset (get_arm_reg (b 3 0)) reg_srt in
  let mk_mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
  let selector = (bv 22, bv 20) in
  match selector with
  (* <cc><3>pu0w0<rn><rt><imm>ty0<rm> *)   (* STR (register) - A1 *)
  | (0, 0) ->
     let mem = mk_mem WR in
     (* STR<c> <Rt>, [<Rn>,+/-<Rm>{, <shift>}]{!} *)
     (* STR<c> <Rt>, [<Rn>],+/-<Rm>{, <shift>} *)
     StoreRegister (c, rt RD, rn, rm, mem, false)

  (* <cc><3>pu0w1<rn><rt><imm>ty0<rm> *)   (* LDR (register) - A1 *)
  | (0, 1) ->
     let mem = mk_mem RD in
     (* LDR<c> <Rt>, [<Rn>,+/-<Rm>{, <shift>}[{!} *)
     (* LDR<c> <Rt>, [<Rn>],+/-<Rm>{, <shift>} *)
     LoadRegister (c, rt WR, rn, rm, mem, false)

  (* <cc><3>pu1w0<rn><rt><imm>ty0<rm> *)   (* STRB (register) - A1 *)
  | (1, 0) ->
     let mem = mk_mem WR in
     (* STRB<c> <Rt>, [<Rn>,+/-<Rm>{, <shift>}]{!} *)
     (* STRB<c> <Rt>, [<Rn>],+/-<Rm>{, <shift>} *)
     StoreRegisterByte (c, rt RD, rn, rm, mem, false)

  (* <cc><3>pu1w1<rn><rt><imm>ty0<rm> *)   (* LDRB (register) - A1 *)
  | (1, 1) ->
     let mem = mk_mem RD in
     LoadRegisterByte (c, rt WR, rn, rm, mem, false)

  | _ -> OpInvalid


let parse_media_type (instrbytes: doubleword_int) (cond: int) =
  (* opc (b 17 25) = 3, bitval 4 = 1 *)
  let b = instrbytes#get_segval in
  let c = get_opcode_cc cond in
  let opc = b 24 20 in
  let rx = b 19 16 in
  let ry = b 15 12 in
  let rz = b 3 0 in

  match opc with
  (* <cc><3>< 10><15><rd>ro000111<rm> *)   (* SXTB - A1 *)
  | 10 when (rx = 15) && (b 9 5) = 3 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rotation = (b 11 10) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg rz) rotation RD in
     (* SXTB<c> <Rd>, <Rm>{, <rotation>} *)
     SignedExtendByte (c, rd, rm, false)

  (* <cc><3>< 11><15><rd><15>0011<rm> *)   (* REV - A1 *)
  | 11 when (rx = 15) && (b 11 8) = 15 && (b 7 5) = 1 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rm = arm_register_op (get_arm_reg rz) RD in
     (* REV<c> <Rd>, <Rm> *)
     ByteReverseWord (c, rd, rm, false)

  (* <cc><3>< 11><15><rd><15>1011<rm> *)   (* REV16 - A1 *)
  | 11 when (rx = 15) && (b 11 8) = 15 && (b 7 5) = 5 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rm = arm_register_op (get_arm_reg rz) RD in
     (* REV16<c> <Rd>, <Rm> *)
     ByteReversePackedHalfword (c, rd, rm, false)

  (* <cc><3>< 11><15><rd>ro000111<rm> *)   (* SXTH - A1 *)
  | 11 when (rx = 15) && (b 9 5) = 3 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rotation = (b 11 10) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg rz) rotation RD in
     (* SXTH<c> <Rd>, <Rm>{, <rotation>} *)
     SignedExtendHalfword (c, rd, rm, false)

  (* <cc><3>< 14><15><rd>ro000111<rm> *)   (* UXTB - A1   *)
  | 14 when (rx = 15) && (b 9 5) = 3 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rotation = (b 11 10) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg rz) rotation RD in
     (* UXTB<c> <Rd>, <Rm>{, <rotation>} *)
     UnsignedExtendByte (c, rd, rm, false)

  (* <cc><3>< 14><rn><rd>ro000111<rm> *)   (* UXTAB - A1 *)
  | 14 when (b 9 5) = 3 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rotation = (b 11 10) lsl 3 in
     let rn = arm_register_op (get_arm_reg rx) RD in
     let rm = mk_arm_rotated_register_op (get_arm_reg rz) rotation RD in
     (* UXTAB<c> <Rd>, <Rn>, <Rm>{, <rotation>} *)
     UnsignedExtendAddByte (c, rd, rn, rm)

  (* <cc><3>< 15><15><rd>11110011<rm> *)   (* RBIT - A1 *)
  | 15 when (rx = 15) && (b 11 8) = 15 && (b 7 5) = 1 ->
     let rd = arm_register_op (get_arm_reg ry) in
     let rm = arm_register_op (get_arm_reg rz) in
     (* RBIT<c> <Rd>, <Rm> *)
     ReverseBits (c, rd WR, rm RD)

  (* <cc><3>< 15><15><rd>ro000111<rm> *)   (* UXTH - A1  *)
  | 15 when (rx = 15) && (b 9 5) = 3 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rotation = (b 11 10) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg rz) rotation RD in
     (* UXTH<c> <Rd>, <Rm>{, <rotation>} *)
     UnsignedExtendHalfword (c, rd, rm, false)

  (* <cc><3>< 15><rn><rd>ro000111<rm> *)   (* UXTAH - A1  *)
  | 15 when (b 9 5) = 3 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rn = arm_register_op (get_arm_reg rx) RD in
     let rotation = (b 11 10) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg rz) rotation RD in
     (* UXTAH<c> <Rd>, <Rn>, <Rm>{, <rotation>} *)
     UnsignedExtendAddHalfword (c, rd, rn, rm)

  (* <cc><3>< 17><rd><15><rm>0001<rn> *)   (* SDIV - A1 *)
  | 17 when ry = 15 && (b 7 5) = 0 ->
     let rd = arm_register_op (get_arm_reg rx) WR in
     let rm = arm_register_op (get_arm_reg (b 11 8)) RD in
     let rn = arm_register_op (get_arm_reg rz) RD in
     (* SDIV<c> <Rd>, <Rn>, <Rm> *)
     SignedDivide (c, rd, rn, rm)

  (* <cc><3>< 19><rd><15><rm>0001<rn> *)    (* UDIV - A1 *)
  | 19 when ry = 15 && (b 7 5) = 0 ->
     let rd = arm_register_op (get_arm_reg rx) WR in
     let rm = arm_register_op (get_arm_reg (b 11 8)) RD in
     let rn = arm_register_op (get_arm_reg rz) RD in
     (* UDIV<c> <Rd>, <Rn>, <Rm> *)
     UnsignedDivide (c, rd, rn, rm)

  (* <cc><3>< 21><rd><15><rm>00R1<rn> *)   (* SMMUL - A1 *)
  | 21 when ry = 15 && (b 7 6) = 0 ->
     let rd = arm_register_op (get_arm_reg rx) WR in
     let rm = arm_register_op (get_arm_reg (b 11 8)) RD in
     let rn = arm_register_op (get_arm_reg rz) RD in
     let roundf = (b 5 5) in
     (* SMMUL{R}<c> <Rd>, <Rn>, <Rm> *)
     SignedMostSignificantWordMultiply (c, rd, rn, rm, roundf)

  (* <cc><3>< 21><rd><ra><rm>00R1<rn> *)   (* SMMLA - A1 *)
  | 21 when (b 7 6) = 0 ->
     let rd = arm_register_op (get_arm_reg rx) WR in
     let ra = arm_register_op (get_arm_reg ry) WR in
     let rm = arm_register_op (get_arm_reg (b 11 8)) RD in
     let rn = arm_register_op (get_arm_reg rz) RD in
     let roundf = (b 5 5) in
     (* SMMLA{R}<c> <Rd>, <Rn>, <Rm>, <Ra> *)
     SignedMostSignificantWordMultiplyAccumulate (c, rd, rn, rm, ra, roundf)

  (* <cc><3><13><wm1><rd><lsb>101<rn> *)   (* SBFX - A1 *)
  | 26 | 27 when (b 6 5) = 2 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let lsb = b 11 7 in
     let widthm1 = b 20 16 in
     let rn = mk_arm_reg_bit_sequence_op (get_arm_reg rz) lsb widthm1 RD in
     (* SBFX<c> <Rd>, <Rn>, #<lsb>, #<width> *)
     SingleBitFieldExtract (c, rd, rn)

  (* <cc><3><14><msb><rd><lsb>001<15> *)   (* BFC - A1 *)
  | 28 | 29 when (b 6 5) = 0 && rz = 15 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let msb = b 20 16 in
     let lsb = b 11 7 in
     let width = (msb - lsb) + 1 in
     (* BFC<c> <Rd>, #<lsb>, #<width> *)
     BitFieldClear (c, rd, lsb, width, msb)

  (* <cc><3><14><msb><rd><lsb>001<rn> *)   (* BFI - A1 *)
  | 28 | 29 when (b 6 5) = 0 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let rn = arm_register_op (get_arm_reg rz) RD in
     let msb = b 20 16 in
     let lsb = b 11 7 in
     let width = (msb - lsb) + 1 in
     (* BFI<c> <Rd>, <Rn>, #<lsb>, #<width> *)
     BitFieldInsert (c, rd, rn, lsb, width, msb)

  (* <cc><3><15><wm1><rd><lsb>101<rn> *)   (* UBFX - A1 *)
  | 30 | 31 when (b 6 5) = 2 ->
     let rd = arm_register_op (get_arm_reg ry) WR in
     let lsb = b 11 7 in
     let widthm1 = b 20 16 in
     let rn = mk_arm_reg_bit_sequence_op (get_arm_reg rz) lsb widthm1 RD in
     (* UBFX<c> <Rd>, <Rn>, #<lsb>, #<width> *)
     UnsignedBitFieldExtract (c, rd, rn)

  | _ ->
     NotRecognized ("media_type:" ^ (stri opc), instrbytes)


let parse_block_data_type (instr: doubleword_int) (cond: int) =
  (* bitval 22 = 0 *)
  let b = instr#get_segval in
  let c = get_opcode_cc cond in
  let rnval = b 19 16 in
  let rnreg = get_arm_reg rnval in
  let isstack =  rnval = 13 in
  let iswback = (b 21 21) = 1 in
  let rn = arm_register_op rnreg (if iswback then RW else RD) in
  let rl = get_reglist_from_int 16 (b 15 0) in
  let b24 = b 24 24 in
  let b23 = b 23 23 in
  let b20 = b 20 20 in
  match (b24, b23, b20, isstack) with
  (* <cc><4>000W1<rn><register-list-> *)    (* LDMDA/LDMFA - A1 *)
  | (0, 0, 1, _) ->
     let rlop = arm_register_list_op rl WR in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) RD in
     (* LDMDA<c> <Rn>{!}, <registers> *)
     LoadMultipleDecrementAfter (iswback, c, rn, rlop, mmem)

  (* <cc><4>010W0<rn><register-list-> *)    (* STM/STMIA/STMEA - A1 *)
  | (0, 1, 0, _) ->
     let rlop = arm_register_list_op rl RD in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) WR in
     (* STM<c> <Rn>{!}, <registers> *)
     StoreMultipleIncrementAfter (iswback, c, rn, rlop, mmem, false)

  (* <cc><4>01011<sp><register-list-> *)    (* POP - A1 *)
  | (0, 1, 1, true) when iswback ->
     let rlop = arm_register_list_op rl WR in
     (* POP<c> <registers> *)
     Pop (c, rn, rlop, false)

  (* <cc><4>010W1<rn><register-list-> *)    (* LDM/LDMIA/LDMFD - A1 *)
  | (0, 1, 1, _) ->
     let rlop = arm_register_list_op rl WR in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) RD in
     (* LDM<c> <R>{!}, <registers> *)
     LoadMultipleIncrementAfter (iswback, c, rn, rlop, mmem)

  (* <cc><4>10010<sp><register-list-> *)    (* PUSH - A1 *)
  | (1, 0, 0, true) when iswback ->
     let rlop = arm_register_list_op rl RD in
     (* PUSH<c> <registers> *)
     Push (c, rn, rlop, false)

  (* <cc><4>100W0<rn><register-list-> *)    (* STMDB/STMFD - A1 *)
  | (1, 0, 0, _) ->
     let rlop = arm_register_list_op rl RD in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) WR in
     (* STMDB<c> <Rn>{!}, <registers> *)
     StoreMultipleDecrementBefore (iswback, c, rn, rlop, mmem, false)

  (* <cc><4>100W1<rn><register-list-> *)    (* LDMDB/LDMEA - A1 *)
  | (1, 0, 1, _) ->
     let rlop = arm_register_list_op rl WR in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) RD in
     (* LDMDB<c> <Rn>{!}, <registers> *)
     LoadMultipleDecrementBefore (iswback, c, rn, rlop, mmem)

  (* <cc><4>110W0<rn><register-list-> *)    (* STMIB/STMFA - A1 *)
  | (1, 1, 0, _) ->
     let rlop = arm_register_list_op rl RD in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) WR in
     (* STMIB<c> <Rn>{!}, <registers> *)
     StoreMultipleIncrementBefore (iswback, c, rn, rlop, mmem, false)

  (* <cc><4>110W1<rn><register-list-> *)    (*LDMIB/LDMED - A1 *)
  | (1, 1, 1, _) ->
     let rlop = arm_register_list_op rl WR in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) RD in
     (* LDMIB<c> <Rn>{!}, <registers> *)
     LoadMultipleIncrementBefore (iswback, c, rn, rlop, mmem)

  | (k, l, m, _) ->
     NotRecognized
       ("parse_block_data_type:"
        ^ (stri k)
        ^ "_"
        ^ (stri l)
        ^ "_"
        ^ (stri m)
        ^ " with register "
        ^ (stri rnval),
       instr)
     

let parse_branch_link_type
      (iaddr: doubleword_int)
      (instr: doubleword_int)
      (cond: int) =
  let b = instr#get_segval in
  let offset = b 23 0 in
  let opx = instr#get_bitval 24 in
  let cc = get_opcode_cc cond in
  let imm32 = sign_extend 32 26 (offset lsl 2) in
  let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
  let tgt = iaddr#add_int (imm32 + 8) in
  let tgtop = arm_absolute_op tgt RD in
  if opx = 0 then
    (* <cc><5>0<--------imm24---------> *)    (* B - A1 *)
    Branch (cc, tgtop, false)
  else
    (* <cc><5>1<--------imm24---------> *)    (* BL - A1 *)
    (* BL<c> <label> *)
    BranchLink (cc, tgtop)


let parse_misc_6_type (instr: doubleword_int) (cond: int) =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let c = get_opcode_cc cond in
  let s1 = b 24 23 in
  let s2 = b 21 20 in
  let s3 = b 11 8 in

  match (s1, s2, s3) with
  (* VMOV between two ARM core registers and two single-precision registers *)
  (* <cc><6>00100<t2><rt><10>00M1<vm> - A1-from *)
  | (0, 0, 10) when (bv 22) = 1 && (b 7 6) = 0 && (bv 4) = 1 ->
     let m = postfix_bit (bv 5) (b 3 0) in
     let sm = arm_extension_register_op XSingle m in
     let sm1 = arm_extension_register_op XSingle (m + 1) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rt2 = arm_register_op (get_arm_reg (b 19 16)) in
     (* VMOV<c> <Sm>, <Sm1>, <Rt>, <Rt2> *)
     VectorMove (c, VfpNone, [sm WR; sm1 WR; rt RD; rt2 RD])

  (* VMOV between two ARM core registers and two single-precision registers *)
  (* <cc><6>00101<t2><rt><10>00M1<vm> - A1-to *)
  | (0, 1, 10) when (bv 22) = 1 && (b 7 6) = 0 && (bv 4) = 1 ->
     let m = postfix_bit (bv 5) (b 3 0) in
     let sm = arm_extension_register_op XSingle m in
     let sm1 = arm_extension_register_op XSingle (m + 1) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rt2 = arm_register_op (get_arm_reg (b 19 16)) in
     (* VMOV<c> <Rt>, <Rt2>, <Sm>, <Sm1> *)
     VectorMove (c, VfpNone, [rt WR; rt2 WR; sm RD; sm1 RD])

  (* VMOV between two ARM core registers and a doubleword extension register *)
  (* <cc><6>00101<t2><rt><11>00M1<vm> - A1-from *)
  | (0, 0, 11) when (bv 22) = 1 && (b 7 6) = 0 && (bv 4) = 1 ->
     let m = prefix_bit (bv 5) (b 3 0) in
     let dm = arm_extension_register_op XDouble m in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rt2 = arm_register_op (get_arm_reg (b 19 16)) in
     (* VMOV<c> <Dm>, <Rt>, <Rt2> *)
     VectorMove (c, VfpNone, [dm WR; rt RD; rt2 RD])

  (* VMOV between two ARM core registers and a doubleword extension register *)
  (* <cc><6>00101<t2><rt><11>00M1<vm> - A1-to *)
  | (0, 1, 11) when (bv 22) = 1 && (b 7 6) = 0 && (bv 4) = 1 ->
     let m = prefix_bit (bv 5) (b 3 0) in
     let dm = arm_extension_register_op XDouble m in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rt2 = arm_register_op (get_arm_reg (b 19 16)) in
     (* VMOV<c> <Dm>, <Rt>, <Rt2> *)
     VectorMove (c, VfpNone, [rt WR; rt2 WR; dm RD])

  (* <cc><6>01D11<13><vd><10><-imm8-> *)   (* VPOP - A2 *)
  | (1, 3, 10) when (b 19 16) = 13 ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let spreg = get_arm_reg 13 in
     let sp = arm_register_op spreg in
     let regs = b 7 0 in
     let rl = arm_extension_register_list_op XSingle d regs in
     let mem = mk_arm_mem_multiple_op ~size:4 spreg regs in
     (* VPOP<c> <list> *)
     VectorPop (c, sp WR, rl WR, mem RD)

  (* <cc><6>01D11<13><vd><11><-imm8-> *)   (* VPOP - A1 *)
  | (1, 3, 11) when (b 19 16) = 13 && (bv 0) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let spreg = get_arm_reg 13 in
     let sp = arm_register_op spreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 spreg regs in
     (* VPOP<c> <list> *)
     VectorPop (c, sp WR, rl WR, mem RD)

  (* <cc><6>01D01<rn><vd><10><-imm8-> *)   (* VLDM - A2 *)
  | (1, 1, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 0 in
     let rl = arm_extension_register_list_op XSingle d regs in
     let mem = mk_arm_mem_multiple_op ~size:4 rnreg regs in
     (* VLDM<c> <Rn>, <list> *)
     VectorLoadMultipleIncrementAfter (false, c, rn RD, rl WR, mem RD)

  (* <cc><6>01D11<rn><vd><10><-imm8-> *)   (* VLDM - A2-wb *)
  | (1, 3, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 0 in
     let rl = arm_extension_register_list_op XSingle d regs in
     let mem = mk_arm_mem_multiple_op ~size:4 rnreg regs in
     (* VLDM<c> <Rn>!, <list> *)
     VectorLoadMultipleIncrementAfter (true, c, rn RD, rl WR, mem RD)

  (* <cc><6>01D01<rn><vd><11><-imm8-> *)   (* VLDM - A1 *)
  | (1, 1, 11) when (bv 0) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
     (* VLDM<c> <Rn>, <list> *)
     VectorLoadMultipleIncrementAfter (false, c, rn RD, rl WR, mem RD)

  (* <cc><6>01D11<rn><vd><11><-imm8-> *)   (* VLDM - A1-wb *)
  | (1, 3, 11) when (bv 0) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
     (* VLDM<c> <Rn>, <list> *)
     VectorLoadMultipleIncrementAfter (true, c, rn RD, rl WR, mem RD)

  (* <cc><6>01D11<13><vd><11<-imm7>1 *)   (* FLDMX *)
  | (1, 3, 11) when (bv 0) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let spreg = get_arm_reg 13 in
     let sp = arm_register_op spreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 spreg regs in
     (* FLDMX<c> <SP>{!}, <list> *)
     FLoadMultipleIncrementAfter (true, c, sp WR, rl WR, mem RD)

  (* <cc><6>01D00<rn><vd><10><-imm8-> *)   (* VSTM - A2 *)
  | (1, 0, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 0 in
     let rl = arm_extension_register_list_op XSingle d regs in
     let mem = mk_arm_mem_multiple_op ~size:4 rnreg regs in
     (* VSTM<c> <Rn>, <list> *)
     VectorStoreMultipleIncrementAfter (false, c, rn RD, rl RD, mem WR)

  (* <cc><6>01D10<rn><vd><10><-imm8-> *)   (* VSTM - A2-wb *)
  | (1, 2, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 0 in
     let rl = arm_extension_register_list_op XSingle d regs in
     let mem = mk_arm_mem_multiple_op ~size:4 rnreg regs in
     (* VSTM<c> <Rn>!, <list> *)
     VectorStoreMultipleIncrementAfter (true, c, rn RD, rl RD, mem WR)

  (* <cc><6>01D00<rn><vd><11><-imm8-> *)   (* VSTM - A1 *)
  | (1, 0, 11) when (bv 0) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
     (* VSTM<c> <Rn>, <list> *)
     VectorStoreMultipleIncrementAfter (false, c, rn RD, rl RD, mem WR)

  (* <cc><6>01D00<rn><vd><11><-imm8-> *)   (* FSTMIAX - A1 *)
  | (1, 0, 11) when (bv 0) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
     (* FSTMIAX<c> <Rn>, <list> *)
     FStoreMultipleIncrementAfter (false, c, rn RD, rl RD, mem WR)

  (* <cc><6>01D00<rn><vd><11><-imm8-> *)   (* VSTM - A1-wb *)
  | (1, 2, 11) when (bv 0) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
     (* VSTM<c> <Rn>, <list> *)
     VectorStoreMultipleIncrementAfter (true, c, rn RD, rl RD, mem WR)

  (* <cc><6>01D00<rn><vd><11><-imm8-> *)   (* FSTMIAX - A1-wb *)
  | (1, 2, 11) when (bv 0) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
     (* FSTMIAX<c> <Rn>, <list> *)
     FStoreMultipleIncrementAfter (true, c, rn RD, rl RD, mem WR)

  (* <cc><6>10D10<13><vd><10><-imm8-> *)   (* VPUSH - A2 *)
  | (2, 2, 10) when (b 19 16) = 13 ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let spreg = get_arm_reg 13 in
     let sp = arm_register_op spreg in
     let regs = b 7 0 in
     let rl = arm_extension_register_list_op XSingle d regs in
     let mem = mk_arm_mem_multiple_op ~size:4 spreg regs in
     (* VPUSH<c> <list> *)
     VectorPush (c, sp WR, rl RD, mem WR)

  (* <cc><6>10D10<rn><vd><10><-imm8-> *)   (* VSTMDB - A2 *)
  | (2, 2, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 0 in
     let rl = arm_extension_register_list_op XSingle d regs in
     let mem = mk_arm_mem_multiple_op ~size:4 rnreg regs in
     (* VSTMDB<c> <Rn>, <list> *)
     VectorStoreMultipleDecrementBefore (true, c, rn RD, rl RD, mem WR)

  (* <cc><6>10D10<13><vd><11><-imm8-> *)   (* VPUSH - A1 *)
  | (2, 2, 11) when (bv 0) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let spreg = get_arm_reg 13 in
     let sp = arm_register_op spreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 spreg regs in
     (* VPUSH<c> <list> *)
     VectorPush (c, sp WR, rl RD, mem WR)

  (* <cc><6>10D10<rn><vd><11><-imm8-> *)   (* VSTMDB - A1 *)
  | (2, 2, 11) when (bv 0) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let regs = b 7 1 in
     let rl = arm_extension_register_list_op XDouble d regs in
     let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
     (* VSTM<c> <Rn>, <list> *)
     VectorStoreMultipleDecrementBefore (true, c, rn RD, rl RD, mem WR)

  (* <cc><6>10D00<rn><vd><10><-imm8-> *)   (* VSTR - A2-sub *)
  | (2, 0, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XSingle d in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (4 * (b 7 0)) in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:false ~isindex:true ~iswback:false in
     (* VSTR<c> <Sd>, [<Rn>{, #+/-<imm>}] *)
     VStoreRegister (c, vd RD, rn RD, mem WR)

  (* <cc><6>11D00<rn><vd><10><-imm8-> *)   (* VSTR - A2-add *)
  | (3, 0, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XSingle d in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (4 * (b 7 0)) in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* VSTR<c> <Sd>, [<Rn>{, #-<imm>}] *)
     VStoreRegister (c, vd RD, rn RD, mem WR)

  (* <cc><6>10D00<rn><vd><11><-imm8-> *)   (* VSTR - A1-sub *)
  | (2, 0, 11) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XDouble d in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (4 * (b 7 0)) in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:false ~isindex:true ~iswback:false in
     (* VSTR<c> <Dd>, [<Rn>{, #+/-<imm>}] *)
     VStoreRegister (c, vd RD, rn RD, mem WR)

  (* <cc><6>11D00<rn><vd><11><-imm8-> *)   (* VSTR - A1-add *)
  | (3, 0, 11) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XDouble d in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (4 * (b 7 0)) in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* VSTR<c> <Dd>, [<Rn>{, #+/-<imm>}] *)
     VStoreRegister (c, vd RD, rn RD, mem WR)

  (* <cc><6>10D01<rn><vd><10><-imm8-> *)   (* VLDR - A2-sub *)
  | (2, 1, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XSingle d in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (4 * (b 7 0)) in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:false ~isindex:true ~iswback:false in
     (* VLDRc> <Sd>, [<Rn>{, #+/-<imm>}] *)
     VLoadRegister (c, vd WR, rn RD, mem RD)

  (* <cc><6>11D01<rn><vd><10><-imm8-> *)   (* VLDR - A2-add *)
  | (3, 1, 10) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XSingle d in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (4 * (b 7 0)) in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* VLDRc> <Sd>, [<Rn>{, #+/-<imm>}] *)
     VLoadRegister (c, vd WR, rn RD, mem RD)

  (* <cc><6>10D01<rn><vd><11><-imm8-> *)   (* VLDR - A1-sub *)
  | (2, 1, 11) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XDouble d in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (4 * (b 7 0)) in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:false ~isindex:true ~iswback:false in
     (* VLDR<c> <Dd>, [<Rn>{, #+/-<imm>}] *)
     VLoadRegister (c, vd WR, rn RD, mem RD)

  (* <cc><6>11D01<rn><vd><11><-imm8-> *)   (* VLDR - A1-add *)
  | (3, 1, 11) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XDouble d in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (4 * (b 7 0)) in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* VLDR<c> <Dd>, [<Rn>{, #+/-<imm>}] *)
     VLoadRegister (c, vd WR, rn RD, mem RD)

  | _ ->
     NotRecognized
       ("arm:misc_6:"
        ^ (string_of_int s1)
        ^ "_"
        ^ (string_of_int s2)
        ^ "_"
        ^ (string_of_int s3),
        instr)


let parse_misc_7_type
      (iaddr: doubleword_int) (instr: doubleword_int) (cond: int) =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let c = get_opcode_cc cond in
  let b24_23 = b 24 23 in
  let b21_20 = b 21 20 in
  let bv6 = bv 6 in
  let bv4 = bv 4 in

  match (b24_23, b21_20, bv6, bv4) with

  (* <cc><7>00D00<vn><vd>101sN0M0<vm> *)  (* VMLA (floating-point) - A2 *)
  | (0, 0, 0, 0) when (b 11 9) = 5 ->
     let sz = bv 8 in
     let dp = sz = 1 in
     let dbit = bv 22 in
     let nbit = bv 7 in
     let mbit = bv 5 in
     let vn = b 19 16 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let (dreg, nreg, mreg) =
       if dp then
         (prefix_bit dbit vd, prefix_bit nbit vn, prefix_bit mbit vm)
       else
         (postfix_bit dbit vd, postfix_bit nbit vn, postfix_bit mbit vm) in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype dreg in
     let vn = arm_extension_register_op xtype nreg in
     let vm = arm_extension_register_op xtype mreg in
     (* VMLA<c>.F64 <Dd>, <Dn>, <Dm> *)
     (* VMLA<c>.F32 <Sd>, <Sn>, <Sm> *)
     VectorMultiplyAccumulate (c, dt, vd WR, vn RD, vm RD)

  (* <cc><7>0000o<vn><rt>1010N001< 0> *)(* VMOV (between ARM core and sp reg - A1 *)
  | (0, 0, 0, 1) | (0, 1, 0, 1) when
         (bv 22) = 0 && (b 11 9) = 5 && (bv 8) = 0 && (b 6 5) = 0 && (b 3 0) = 0 ->
     let to_arm = (bv 20) = 1 in
     let n = bv 7 in
     let vn = b 19 16 in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let sn = postfix_bit n vn in
     let sn = arm_extension_register_op XSingle sn in
     let dt = VfpNone in
     if to_arm then
       (* VMOV<c> <Rt>, <Sn> *)
       VectorMove (c, dt, [rt WR; sn RD])
     else
       (* VMOV<c> <Sn>, <Rt> *)
       VectorMove (c, dt, [sn WR; rt RD])

  (* <cc><7>00D00<vn><vd>101sN1M0<vm> *)  (* VMLS (floating-point) - A2 *)
  | (0, 0, 1, 0) when (b 11 9) = 5 ->
     let sz = bv 8 in
     let dp = sz = 1 in
     let dbit = bv 22 in
     let nbit = bv 7 in
     let mbit = bv 5 in
     let vn = b 19 16 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let (dreg, nreg, mreg) =
       if dp then
         (prefix_bit dbit vd, prefix_bit nbit vn, prefix_bit mbit vm)
       else
         (postfix_bit dbit vd, postfix_bit nbit vn, postfix_bit mbit vm) in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype dreg in
     let vn = arm_extension_register_op xtype nreg in
     let vm = arm_extension_register_op xtype mreg in
     (* VMLS<c>.F64 <Dd>, <Dn>, <Dm> *)
     (* VMLS<c>.F32 <Sd>, <Sn>, <Sm> *)
     VectorMultiplySubtract (c, dt, vd WR, vn RD, vm RD)

  (* <cc><7>00oo0<vd><rt>1011Doo1< 0> *) (* VMOV (ARM core to scalar) - A1 *)
  | (0, (0 | 1), _, 1) when (bv 20) = 0 && (b 11 8) = 11 && (b 3 0) = 0 ->
     let opc1 = b 22 21 in
     let opc2 = b 6 5 in
     let (esize, index) =
       match (opc1, opc2) with
       | (2, _) | (3, _) -> (8, ((bv 21) lsl 2) + opc2)
       | (0, 1) | (1, 1) | (0, 3) | (1, 3) -> (16, ((bv 21) lsl 1) + (bv 6))
       | (0, 0) | (1, 0) -> (32, bv 21)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "parse_misc7: VMOV (ARM core to scalar): ";
                    INT opc1;
                    STR ", ";
                    INT opc2])) in
     let d = prefix_bit (bv 7) (b 19 16) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let dt = VfpSize esize in
     let elt = arm_extension_register_element_op XDouble d index esize in
     (* VMOV<c>.<dt> <Dd[x]>, <Rt> *)
     VectorMove (c, dt, [elt WR; rt RD])

  (* <cc><7>00D10<vn><vd>101sN0M0<vm> *)    (* VMUL (floating-point) - A2 *)
  | (0, 2, 0, 0) when (b 11 9) = 5 ->
     let dp = (bv 8) = 1 in
     let d = bv 22 in
     let n = bv 7 in
     let m = bv 5 in
     let vn = b 19 16 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let (dreg, nreg, mreg) =
       if dp then
         (prefix_bit d vd, prefix_bit n vn, prefix_bit m vm)
       else
         (postfix_bit d vd, postfix_bit n vn, postfix_bit m vm) in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype dreg in
     let vn = arm_extension_register_op xtype nreg in
     let vm = arm_extension_register_op xtype mreg in
     (* VMUL<c>.F64 <Dd>, <Dn>, <Dm> *)
     (* VMUL<c>.F32 <Sd>, <Sn>, <Sm> *)
     VectorMultiply (c, dt, vd WR, vn RD, vm RD)

  (* <cc><7>00D11<vn><vd>101sN0M0<vm> *)    (* VADD (floating-point) - A2 *)
  | (0, 3, 0, 0) when (b 11 9) = 5  ->
     let dp = (bv 8) = 1 in
     let d = bv 22 in
     let n = bv 7 in
     let m = bv 5 in
     let vn = b 19 16 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let (dreg, nreg, mreg) =
       if dp then
         (prefix_bit d vd, prefix_bit n vn, prefix_bit m vm)
       else
         (postfix_bit d vd, postfix_bit n vn, postfix_bit m vm) in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype dreg in
     let vn = arm_extension_register_op xtype nreg in
     let vm = arm_extension_register_op xtype mreg in
     (* VADD<c>.F64 <Dd>, <Dn>, <Dm> *)
     (* VADD<c>.F32 <Sd>, <Sn>, <Sm> *)
     VectorAdd (c, dt, vd WR, vn RD, vm RD)

  (* <cc><7>00D11<vn><vd>101sN1M0<vm> *)    (* VSUB (floating-point) - A2 *)
  | (0, 3, 1, 0) when (b 11 9) = 5 ->
     let d = bv 22 in
     let sz = bv 8 in
     let dp = (sz = 1) in
     let nbit = bv 7 in
     let mbit = bv 5 in
     let vn = b 19 16 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let (dreg, nreg, mreg) =
       if dp then
         (prefix_bit d vd, prefix_bit nbit vn, prefix_bit mbit vm)
       else
         (postfix_bit d vd, postfix_bit nbit vn, postfix_bit mbit vm) in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype dreg in
     let vn = arm_extension_register_op xtype nreg in
     let vm = arm_extension_register_op xtype mreg in
     (* VSUB<c>.F64 <Dd>, <Dn>, <Dm> *)
     (* VSUB<c>.F32 <Sd>, <Sn>, <Sm> *)
     VectorSubtract (c, dt, vd WR, vn RD, vm RD)

  (* <cc><7>0<a>0<cn><rt><co><b>1<cm> *)    (* MCR - A1 *)
  | ((0 | 1), (0 | 2), _, 1) when (b 11 9) != 5 ->
     let opc1 = b 23 21 in
     let crn = b 19 16 in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let coproc = b 11 8 in
     let opc2 = b 7 5 in
     let crm = b 3 0 in
     (* MCR<c> <coproc>, <opc1>, <Rt>, <CRn>, <CRm>{, <opc2>} *)
     MoveToCoprocessor (c, coproc, opc1, rt RD, crn, crm, opc2)

  (* <cc><7>0Uo11<vn><rt>1011No21< 0> *) (* VMOV (scalar to ARM core) - A1 *)
  | ((0 | 1), (1 | 3), _, 1) when (bv 20) = 1 && (b 11 8) = 11 && (b 3 0) = 0 ->
     let opc1 = b 22 21 in
     let opc2 = b 6 5 in
     let u = bv 23 in
     let (esize, index) =
       match (u, opc1, opc2) with
       | (_, 2, _) | (_, 3, _) -> (8, ((bv  21) lsl 2) + opc2)
       | (_, 0, 1) | (_, 1, 1) | (_, 0, 3) | (_, 1, 3) ->
          (16, (bv 21) lsl 1 + (bv 6))
       | (0, 0, _) | (0, 1, _) -> (32, bv 21)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "parse_misc7: VMOV (scalar to ARM core): ";
                    INT u;
                    STR ", ";
                    INT opc1;
                    STR ", ";
                    INT opc2])) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let dt = VfpSize esize in
     let elt = arm_extension_register_element_op XDouble n index esize in
     (* VMOV<c>.<dt> <Rt>, <Dn[x]> *)
     VectorMove (c, dt, [rt WR; elt RD])

  (* <cc><7>01D00<vn><vd>101sN0M0<vm> *)    (* VDIV - A1 *)
  | (1, 0, 0, 0) when (b 11 9) = 5 ->
     let d = bv 22 in
     let sz = bv 8 in
     let vn = b 19 16 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let n = bv 7 in
     let m = bv 5 in
     let dp = (sz = 1) in
     let (vdreg, vnreg, vmreg) =
       if dp then
         (prefix_bit d vd, prefix_bit n vn, prefix_bit m vm)
       else
         (postfix_bit d vd, postfix_bit n vn, postfix_bit m vm) in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype vdreg in
     let vn = arm_extension_register_op xtype vnreg in
     let vm = arm_extension_register_op xtype vmreg in
     (* VDIV<c>.F64 <Dd>, <Dn>, <Dm> *)
     VDivide (c, dt, vd WR, vn RD, vm RD)

  (* <cc><7>01BQ0<vd><rt>1011D0E1< 0> *) (* VDUP (ARM core register) - A1 *)
  | (1, (0 | 2), 0, 1) when (b 11 8) = 11 && (b 3 0) = 0 ->
     let q = bv 21 in
     let vd = prefix_bit (bv 7) (b 19 16) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let (esize, elements) =
       match (bv 22, bv 5) with
       | (0, 0) -> (32, 2)
       | (0, 1) -> (16, 4)
       | (1, 0) -> (8, 8)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "parse_misc_7: VDUP: ";
                    INT (bv 22);
                    STR ", ";
                    INT (bv 5)])) in
     if q = 1 then
       let d = arm_extension_register_op XQuad (vd / 2) in
       (* VDUP<c>.<size> <Qd>, <Rt> *)
       VectorDuplicate (c, VfpSize esize, 2, elements, d WR, rt RD)
     else
       let d = arm_extension_register_op XDouble vd in
       (* VDUP<c>.<size> <Dd>, <Rt> *)
       VectorDuplicate (c, VfpSize esize, 1, elements, d WR, rt RD)

  (* <cc><7>01D11<4H><vd>101s0000<4L> *)    (* VMOV (immediate) - A2 *)
  | (1, 3, 0, 0) when (b 11 9) = 5 && (b 7 4) = 0 ->
     let d = bv 22 in
     let sz = bv 8 in
     let size = if sz = 1 then 64 else 32 in
     let singlereg = (sz = 0) in
     let vd = b 15 12 in
     let imm4H = b 19 16 in
     let imm4L = b 3 0 in
     let imm8 = (imm4H lsl 4) + imm4L in
     let vfp = vfp_expand_imm imm8 size in
     let dt = VfpFloat size in
     let (dreg, xtype) =
       if singlereg then
         (postfix_bit d vd, XSingle)
       else
         (prefix_bit d vd, XDouble) in
     let fpreg = arm_extension_register_op xtype dreg in
     let _ =
       ch_error_log#add
         "floating point constant"
         (LBLOCK [iaddr#toPretty; STR ": "; vfp#toPretty]) in
     let imm = mk_arm_immediate_op false (size / 8) numerical_zero in
     (* VMOV<c>,<dt> <D/Sd>, #<imm> *)
     VectorMove (c, dt, [fpreg WR; imm])

  (* <cc><7>01111< 1><rt>10100001< 0> *)    (* VMRS - A1 *)
  | (1, 3, 0, 1) when
         (bv 22) = 1
         && (b 19 16) = 1
         && (b 11 8) = 10
         && (b 7 4) = 1
         && (b 3 0) = 0 ->
     let rt = b 15 12 in
     let dst =
       if rt = 15 then
         arm_special_register_op APSR_nzcv WR
       else
         arm_register_op (get_arm_reg rt) WR in
     let src = arm_special_register_op FPSCR RD in
     (* VMRS<c> <Rt>, FPSCR *)
     VMoveRegisterStatus (c, dst, src)

  (* <cc><7>01D11< 0><vd>101s01M0<vm> *) (* VMOV (register) - A2 *)
  | (1, 3, 1, 0) when (b 19 16) = 0 && (b 11 9) = 5 && (bv 7) = 0 ->
     let sz = bv 8 in
     let dbit = bv 22 in
     let mbit = bv 5 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let dp = (sz = 1) in
     let (vdreg, vmreg) =
       if dp then
         (prefix_bit dbit vd, prefix_bit mbit vm)
       else
         (postfix_bit dbit vd, postfix_bit mbit vm) in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype vdreg in
     let vm = arm_extension_register_op xtype vmreg in
     (* VMOV<c>.F64 <Dd>, <Dm> *)
     (* VMOV<c>.F32 <Sd>, <Sm> *)
     VectorMove (c, dt, [vd WR; vm RD])

  (* <cc><7>01D11< 1><vd><5>s01M0<vm> *)    (* VNEG - A2 *)
  | (1, 3, 1, 0) when (b 19 16) = 1 && (b 11 9) = 5 && (bv 7) = 0 ->
     let dp = (bv 8) = 1 in
     let dbit = bv 22 in
     let mbit = bv 5 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     if dp then
       let d = prefix_bit dbit vd in
       let vd = arm_extension_register_op XDouble d in
       let m = prefix_bit mbit vm in
       let vm = arm_extension_register_op XDouble m in
       let dt = VfpFloat 64 in
       (* VNEG<c>.F64 <Dd>, <Dm> *)
       VectorNegate (c, dt, vd WR, vm RD)
     else
       let d = postfix_bit dbit vd in
       let vd = arm_extension_register_op XSingle d in
       let m = postfix_bit mbit vm in
       let vm = arm_extension_register_op XSingle m in
       let dt = VfpFloat 32 in
       (* VNEG<c>.F32 <Sd>, <Sm> *)
       VectorNegate (c, dt, vd WR, vm RD)     

  (* <cc><7>01D11< 0><vd><5>s11M0<vm> *) (* VABS -A2 *)
  | (1, 3, 1, 0) when (b 19 16) = 0 && (b 11 9) = 5 && (bv 7) = 1 ->
     let sz = bv 8 in
     let dbit = bv 22 in
     let mbit = bv 5 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let dp = (sz = 1) in
     let (vdreg, vmreg) =
       if dp then
         (prefix_bit dbit vd, prefix_bit mbit vm)
       else
         (postfix_bit dbit vd, postfix_bit mbit vm) in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype vdreg in
     let vm = arm_extension_register_op xtype vmreg in
     (* VABS<c>. F64 <Dd>, <Dm> *)
     (* VABS<c>.F32 <Sd>, <Sm> *)
     VectorAbsolute (c, dt, vd WR, vm RD)

  (* <cc><7>01D11< 5><vd>101sE1000000 *) (* VCMP, VCMPE - A2 *)
  | (1, 3, 1, 0) when (b 19 16) = 5 && (b 11 9) = 5 ->
     let sz = bv 8 in
     let dbit = bv 22 in
     let ebit = bv 7 in
     let dp = sz = 1 in
     let vd = b 15 12 in
     let vdreg = if dp then prefix_bit dbit vd else postfix_bit dbit vd in
     let (dt, xtype) =
       if dp then (VfpFloat 64, XDouble) else (VfpFloat 32, XSingle) in
     let vd = arm_extension_register_op xtype vdreg RD in
     (* VCMP{E}<c>.F64 <Dd>, #0.0 *)
     (* VCMP{E}<c>.F32 <Sd>, #0.0 *)
     VCompare (ebit = 1, c, dt, vd, arm_fp_constant_op (0.0))

  (* <cc><7>01D111<o><vd>101so1M0<vm> *) (* VCVT (between fp and int) - A1 *)
  | (1, 3, 1, 0) when
         (bv 19) = 1
         && ((b 18 16) = 0 || (b 18 16) = 4 || (b 18 16) = 5)
         && (b 11 9) = 5 ->
     let sz = bv 8 in
     let op = bv 7 in
     let dbit = bv 22 in
     let mbit = bv 5 in
     let vd = b 15 12 in
     let vm = b 3 0 in
     let opc2 = b 18 16 in
     (match (opc2, sz) with
      | (0, 0) ->
         let dt1 = VfpFloat 32 in
         let dt2 = if op = 0 then VfpUnsignedInt 32 else VfpSignedInt 32 in
         let sd = postfix_bit dbit vd in
         let sm = postfix_bit mbit vm in
         let sd = arm_extension_register_op XSingle sd in
         let sm = arm_extension_register_op XSingle sm in
         (* VCVT<c>.F32.<Tm> <Sd>, <Sm> *)
         VectorConvert (false, c, dt1, dt2, sd WR, sm RD)
      | (0, 1) ->
         let dt1 = VfpFloat 64 in
         let dt2 = if op = 0 then VfpUnsignedInt 32 else VfpSignedInt 32 in
         let dd = prefix_bit dbit vd in
         let sm = postfix_bit mbit vm in
         let dd = arm_extension_register_op XDouble dd in
         let sm = arm_extension_register_op XSingle sm in
         (* VCVT<c>.F64.<Tm> <Dd>, <Sm> *)
         VectorConvert (false, c, dt1, dt2, dd WR, sm RD)
      | (4, 0) ->
         let dt1 = VfpUnsignedInt 32 in
         let dt2 = VfpFloat 32 in
         let sd = postfix_bit dbit vd in
         let sm = postfix_bit mbit vm in
         let sd = arm_extension_register_op XSingle sd in
         let sm = arm_extension_register_op XSingle sm in
         (* VCVT{R}<c>.U32.F32 <Sd>, <Sm> *)
         VectorConvert (false, c, dt1, dt2, sd WR, sm RD)
      | (4, 1) ->
         let dt1 = VfpUnsignedInt 32 in
         let dt2 = VfpFloat 64 in
         let sd = postfix_bit dbit vd in
         let dm = prefix_bit mbit vm in
         let sd = arm_extension_register_op XSingle sd in
         let dm = arm_extension_register_op XDouble dm in
         (* VCVT{R}<c>.U32.F64 <Sd>, <Dm> *)
         VectorConvert (false, c, dt1, dt2, sd WR, dm RD)
      | (5, 0) ->
         let dt1 = VfpSignedInt 32 in
         let dt2 = VfpFloat 32 in
         let sd = postfix_bit dbit vd in
         let sm = postfix_bit mbit vm in
         let sd = arm_extension_register_op XSingle sd in
         let sm = arm_extension_register_op XSingle sm in
         (* VCVT{R}<c>.S32.F32 <Sd>, <Sm> *)
         VectorConvert (false, c, dt1, dt2, sd WR, sm RD)
      | (5, 1) ->
         let dt1 = VfpSignedInt 32 in
         let dt2 = VfpFloat 64 in
         let sd = postfix_bit dbit vd in
         let dm = prefix_bit mbit vm in
         let sd = arm_extension_register_op XSingle sd in
         let dm = arm_extension_register_op XDouble dm in
         (* VCVT{R}<c>.S32.F64 <Sd>, <Dm> *)
         VectorConvert (false, c, dt1, dt2, sd WR, dm RD)
      | (x, y) ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "misc7_1_3_1_0: VCVT: ";
                   INT x;
                   STR ", ";
                   INT y])))

  (* <cc><7>01D110100<vd>101sE1M0<vm> *)    (* VCMP{E} - A1 *)
  | (1, 3, 1, 0) when (b 19 16) = 4 && (b 11 9) = 5 ->
     let d = bv 22 in
     let vd = b 15 12 in
     let sz = bv 8 in
     let e = bv 7 in
     let m = bv 5 in
     let vm = b 3 0 in
     let (vd, vm, xtype, dt) =
       if sz = 1 then
         (prefix_bit d vd, prefix_bit m vm, XDouble, VfpFloat 64)
       else
         (postfix_bit d vd, postfix_bit m vm, XSingle, VfpFloat 32) in
     let vd = arm_extension_register_op xtype vd RD in
     let vm = arm_extension_register_op xtype vm RD in
     (*VCMP{E}<c>.F64 <Dd>, <Dm> *)
     (*VCMP{E}<c>.F32 <Sd>, <Sm> *)
     VCompare (e = 1, c, dt, vd, vm)

  (* <cc><7>01D11< 7><vd>101s11M0<vm> *) (* VCVT (between dp and sp) - A1 *)
  | (1, 3, 1, 0) when (b 19 16) = 7 && (b 11 9) = 5 && (bv 7) = 1 ->
     let double2single = (bv 8) = 1 in
     let vd = b 15 12 in
     let dbit = bv 22 in
     let vm = b 3 0 in
     let mbit = bv 5 in
     let (d, m, dt1, dt2) =
       if double2single then
         (postfix_bit dbit vd, prefix_bit mbit vm, VfpFloat 32, VfpFloat 64)
       else
         (prefix_bit dbit vd, postfix_bit mbit vm, VfpFloat 64, VfpFloat 32) in
     if double2single then
       let sd = arm_extension_register_op XSingle d in
       let dm = arm_extension_register_op XDouble m in
       (* VCVT<c>.F32.F64 <Sd>, <Dm> *)
       VectorConvert (false, c, dt1, dt2, sd WR, dm RD)
     else
       let dd = arm_extension_register_op XDouble d in
       let sm = arm_extension_register_op XSingle m in
       (* VCVT<c>.F64.F32 <Dd>, <Sm> *)
       VectorConvert (false, c, dt1, dt2, dd WR, sm RD)

  (* <cc><7>1<--------imm24---------> *)    (* SVC - A1 *)
  | ((2 | 3), _, _, _) ->
     let imm32 = arm_immediate_op (TR.tget_ok (signed_immediate_from_int (b 23 0))) in
     SupervisorCall (c, imm32)

  | (k, l, m, n) ->
     NotRecognized (
         "arm:misc_7:"
         ^ (stri k)
         ^ "_"
         ^ (stri l)
         ^ "_"
         ^ (stri m)
         ^ "_"
         ^ (stri n),
         instr)


let parse_vector_structured_store
      (instr: doubleword_int) (iaddr: doubleword_int) =
  (* (b 27 24) = 4, (b 21 20) = 0 *)
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let cc = ACCUnconditional in
  let rnreg = b 19 16 in
  let rn = arm_register_op (get_arm_reg rnreg) in
  let d = bv 22 in
  let vd = prefix_bit d (b 15 12) in
  let rmreg = b 3 0 in
  let rm = get_arm_reg rmreg in
  let rmop = arm_register_op rm RD in

  if bv 23 = 0 then
    (* <15>01000D00<rn><vd><ty>szal<rm> *) (* VST1 (multiple single elts) - A1 *)
    let ty = b 11 8 in
    let sz = b 7 6 in
    let align = b 5 4 in
    match ty with
    | 2 | 6 | 7 | 10 ->
       let alignment = if align = 0 then 1 else 4 lsl align in
       let ebytes = 1 lsl sz in
       let esize = 8 * ebytes in
       let (wb, wback) =
         match rmreg with
         | 15 -> (false, SIMDNoWriteback)
         | 13 -> (true, SIMDBytesTransferred 8)
         | _ -> (true, SIMDAddressOffsetRegister rm) in
       let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
       let rnop = if wb then rn WR else rn RD in
       let rlist =
         match ty with
         (* <15>01000D00<rn><vd>0111szal<rm> *) (* 1 register *)
         | 7 -> arm_simd_reg_list_op XDouble [vd]
         (* <15>01000D00<rn><vd>1010szal<rm> *) (* 2 registers *)
         | 10 -> arm_simd_reg_list_op XDouble [vd; vd + 1]
         (* <15>01000D00<rn><vd>0110szal<rm> *) (* 3 registers *)
         | 6 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2]
         (* <15>01000D00<rn><vd>0010szal<rm> *) (* 4 registers *)
         | 2 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2; vd + 3]
         | _ ->
            raise (BCH_failure (STR "VectorStoreOne: not reachable")) in
       VectorStoreOne (wb, cc, VfpSize esize, rlist RD, rnop, mem WR, rmop)
    | 3 | 8 | 9 ->
       let alignment = if align = 0 then 1 else 4 lsl align in
       let ebytes = 1 lsl sz in
       let esize = 8 * ebytes in
       let (wb, wback) =
         match rmreg with
         | 15 -> (false, SIMDNoWriteback)
         | 13 -> (true, SIMDBytesTransferred 8)
         | _ -> (true, SIMDAddressOffsetRegister rm) in
       let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
       let rnop = if wb then rn WR else rn RD in
       let rlist =
         match ty with
         (* <15><  8>D00<rn><vd>< 8>szal<rm> *)  (* 1 register *)
         | 8 -> arm_simd_reg_list_op XDouble [vd; vd + 1]
         (* <15><  8>D00<rn><vd>< 9>szal<rm> *)  (* 2 registers *)
         | 9 -> arm_simd_reg_list_op XDouble [vd; vd + 2]
         (* <15><  8>D00<rn><vd>< 3>szal<rm> *)  (* 4 registers *)
         | 3 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2; vd + 3]
         | _ ->
            raise (BCH_failure (STR "VectorStoreOne: not reachable")) in
       VectorStoreTwo (wb, cc, VfpSize esize, rlist RD, rnop, mem WR, rmop)

    | _ ->
       NotRecognized (
           "arm_vector_structured_store_0:" ^ (string_of_int ty), instr)

  else
    NotRecognized ("arm_vector_structured_store_1", instr)


let parse_vector_structured_load (instr: doubleword_int) (iaddr: doubleword_int) =
  (* (b 27 24) = 4, (b 21 20) = 2 *)
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let cc = ACCUnconditional in
  let rnreg = b 19 16 in
  let rn = arm_register_op (get_arm_reg rnreg) in
  let d = bv 22 in
  let vd = prefix_bit d (b 15 12) in
  let rmreg = b 3 0 in
  let rm = get_arm_reg rmreg in
  let rmop = arm_register_op rm RD in

  if (bv 23) = 0 then
    (* <15>01000D10<rn><vd><ty>szal<rm> *) (* VLD1 (multiple single elts) - A1 *)
    let ty = b 11 8 in
    let sz = b 7 6 in
    let align = b 5 4 in
    match ty with
    | 2 | 6 | 7 | 10 ->
       let alignment = if align = 0 then 1 else 4 lsl align in
       let ebytes = 1 lsl sz in
       let esize = 8 * ebytes in
       let (wb, wback) =
         match rmreg with
         | 15 -> (false, SIMDNoWriteback)
         | 13 -> (true, SIMDBytesTransferred 8)
         | _ -> (true, SIMDAddressOffsetRegister rm) in
       let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
       let rnop = if wb then rn WR else rn RD in
       let rlist =
         match ty with
         (* <15>01000D10<rn><vd>0111szal<rm> *) (* 1 register *)
         | 7 -> arm_simd_reg_list_op XDouble [vd]
         (* <15>01000D10<rn><vd>1010szal<rm> *) (* 2 registers *)
         | 10 -> arm_simd_reg_list_op XDouble [vd; vd + 1]
         (* <15>01000D10<rn><vd>0110szal<rm> *) (* 3 registers *)
         | 6 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2]
         (* <15>01000D10<rn><vd>0010szal<rm> *) (* 4 registers *)
         | 2 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2; vd + 3]
         | _ ->
            raise (BCH_failure (STR "VectorLoadOne: not reachable")) in
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}]{!} *)
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}], <Rm> *)
       VectorLoadOne (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)
    | _ ->
       NotRecognized (
           "arm_vector_structured_load_0:" ^ (string_of_int ty), instr)

  else if (b 11 8) = 12 then
    (* <15><  9>D10<rn><vd><12>szTa<rm> *)(* VLD1 (single elt to all lanes) - A1 *)
    let sz = b 7 6 in
    let t = bv 5 in
    let a = bv 4 in
    let ebytes = 1 lsl sz in
    let esize = 8 * ebytes in
    let elements = 8 / ebytes in
    let alignment = if a = 0 then 1 else ebytes in
    let (wb, wback) =
      match rmreg with
      | 15 -> (false, SIMDNoWriteback)
      | 13 -> (true, SIMDBytesTransferred ebytes)
      | _ -> (true, SIMDAddressOffsetRegister rm) in
    let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
    let rnop = if wb then rn WR else rn RD in
    let rlist =
      if t = 0 then
        arm_simd_reg_rep_elt_list_op XDouble [vd] esize elements
      else
        arm_simd_reg_rep_elt_list_op XDouble [vd + 1] esize elements in
    (* VLD1<c>.<size> <list>, [<Rn>{:align>}]{!} *)
    (* VLD1<c>.<size> <list>, [<Rn>{:align>}], <Rm> *)
    VectorLoadOne (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)

  else if (b 9 8) = 0 then
    (* <15><  9>D10<rn><vd>< 0><ia><rm> *) (* VLD1 (single elt to one lane) - A1-1 *)
    (* <15><  9>D10<rn><vd>< 4><ia><rm> *) (* VLD1 (single elt to one lane) - A1-2 *)
    (* <15><  9>D10<rn><vd>< 8><ia><rm> *) (* VLD1 (single elt to one lane) - A1-4 *)
    let sz = b 11 10 in
    let index_align = b 7 4 in
    let (ebytes, esize, index, alignment) =
      match sz with
      | 0 -> (1, 8, index_align lsr 1, 1)
      | 1 -> (2, 16, index_align lsr 2, 16)
      | 2 -> (4, 32, index_align lsr 3, 32)
      | _ -> raise (BCH_failure (STR "VectorLoadOne: not reachable")) in
    let (wb, wback) =
      match rmreg with
      | 15 -> (false, SIMDNoWriteback)
      | 13 -> (true, SIMDBytesTransferred ebytes)
      | _ -> (true, SIMDAddressOffsetRegister rm) in
    let rnop = if wb then rn WR else rn RD in
    let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
    let rlist = arm_simd_reg_elt_list_op XDouble [vd] index esize in
    VectorLoadOne (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)

  else
    NotRecognized ("arm_vector_structured_load_1", instr)


let parse_cond15 (instr: doubleword_int) (iaddr: doubleword_int) =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let cc = ACCUnconditional in

  let selector = b 27 23 in
  let isz = b 21 20 in
  let cmode = b 11 8 in
  let q = bv 6 in
  let b4 = bv 4 in
  match (selector, isz, cmode, q, b4) with
  (* <15><  4>D00<vn><vd>< 1>N0M1<vm> *) (* VAND (register) - A1 (Q=0) *)
  | (4, 0, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     (* VAND<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseAnd (cc, vd WR, vn RD, vm RD)

  (* <15><  4>D00<vn><vd>< 1>N1M1<vm> *) (* VAND (register) - A1 (Q=1) *)
  | (4, 0, 1, 1, 1) ->
     let _ =
       if (bv 16) > 0 || (bv 12) > 0 || (bv 0) > 0 then
         raise
           (ARM_undefined
              ("VAND: Q=1 && (Vd<0> == 1 || Vn<0> == 1 || Vm<0. == 1)")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     (* VAND<c> <Qd>, <Qn>, <Qm> *)
     VectorBitwiseAnd (cc, vd WR, vn RD, vm RD)

  (* <15><  4>D00<vn><vd><12>NQM0<vm> *) (* SHA1C - A1 *)
  | (4, 0, 12, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1C.32 <Qd>, <Qn>, <Qm> *)
     SHA1HashUpdateChoose (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  4>D10<vm><vd>< 1>M0M1<vm> *) (* VMOV (register) - A1 (Q=0) *)
  | (4, 2, 1, 0, 1) when (b 19 16) = (b 3 0) && (bv 7) = (bv 5) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpNone in
     (* VMOV<v> <Dd>, <Dm> *)
     VectorMove (cc, dt, [vd WR; vm RD])

  (* <15><  4>D10<vm><vd>< 1>M1M1<vm> *) (* VMOV (register) - A1 (Q=1) *)
  | (4, 2, 1, 1, 1) when (b 19 16) = (b 3 0) && (bv 7) = (bv 5) ->
     let _ =
       if (bv 16) > 0 || (bv 0) > 0 then
         raise
           (ARM_undefined
              ("VMOV: Q=1 && (Vd<0> == 1 || Vm<0> == 1)")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpNone in
     (* VMOV<v> <Dd>, <Dm> *)
     VectorMove (cc, dt, [vd WR; vm RD])

  (* <15><  4>D10<vn><vd>< 1>N0M1<vm> *) (* VORR (register) - A1 (Q=0) *)
  | (4, 2, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     (* VORR<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseOr (cc, VfpNone, vd WR, vn RD, vm RD)

  (* <15><  4>D10<vn><vd>< 1>N1M1<vm> *) (* VORR (register) - A1 (Q=1) *)
  | (4, 2, 1, 1, 1) ->
     let _ =
       if (bv 16) > 0 || (bv 12) > 0 || (bv 0) > 0 then
         raise
           (ARM_undefined
              ("VORR: Q=1 && (Vd<0> == 1 || Vn<0> == 1 || Vm<0. == 1)")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     (* VORR<c> <Qd>, <Qn>, <Qm> *)
     VectorBitwiseOr (cc, VfpNone, vd WR, vn RD, vm RD)

  (* <15><  4>D10<vn><vd><12>N!M0<vm> *) (* SHA1M - A1 *)
  | (4, 2, 12, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1M<dt> <Qd>, <Qn>, <Qm> *)
     SHA1HashUpdateMajority (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  4>Dsz<vn><vd>< 8>N0M0<vm> *) (* VADD (integer) - A1  (Q=0 *)
  | (4, sz, 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpInt (8 lsl sz) in
     (* VADD<c>.<dt> <Dd>, <Dn>, <Dm> *)
     VectorAdd (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  4>Dsz<vn><vd>< 8>N1M0<vm> *) (* VADD (integer) - A1  (Q=1 *)
  | (4, sz, 8, 1, 0) ->
     let _ =
       if (bv 16) > 0 || (bv 12) > 0 || (bv 0) > 0 then
         raise
           (ARM_undefined
              ("VADD: Q=1 && (Vd<0> == 1 || Vn<0> == 1 || Vm<0. == 1)")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpInt (8 lsl sz) in
     (* VADD<c>.<dt> <Qd>, <Qn>, <Qm> *)
     VectorAdd (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  4>Dsz<vn><vd>< 9>N0M1<vm> *) (* VMUL (integer) - A1 (Q=0) *)
  | (4, sz, 9, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpInt (8 lsl sz) in
     (* VMUL<c>.<dt> <Dd>, <Dn>, <Dm> *)
     VectorMultiply (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  4>Dsz<vn><vd>< 9>N0M1<vm> *) (* VMUL (integer) - A1 (Q=1) *)
  | (4, sz, 9, 1, 1) ->
     let _ =
       if (bv 16) > 0 || (bv 12) > 0 || (bv 0) > 0 then
         raise
           (ARM_undefined
              ("VMUL: Q=1 && (Vd<0> == 1 || Vn<0> == 1 || Vm<0. == 1)")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpInt (8 lsl sz) in
     (* VMUL<c>.<dt> <Qd>, <Qn>, <Qm> *)
     VectorMultiply (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  5>D000<i><vd><cm>0001<i4) *) (* VORR (immediate) - A1-0 (Q=0) *)
  | (5, 0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 0, 1)
       when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:VORR-immediate: not reachable"])) in
     let vd = arm_extension_register_op XDouble d in
     (* VORR<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseOr (cc, dt, vd WR, vd RD, immop)

  (* <15><  5>D000<i><vd><cm>0101<i4) *) (* VORR (immediate) - A1-0 (Q=1) *)
  | (5, 0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 1, 1)
       when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:VORR-immediate: not reachable"])) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VORR<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseOr (cc, dt, vd WR, vd RD, immop)

  (* <15><  5>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - A1-0-0 (Q=0) *)
  | (5, 0, cm, 0, 1) when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 cm "VMOV" in
     let vd = arm_extension_register_op XDouble d in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMove (cc, dt, [vd WR; immop])

  (* <15><  5>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - A1-0-0 (Q=1) *)
  | (5, 0, cm, 1, 1) when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 cm "VMOV" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMove (cc, dt, [vd WR; immop])

  (* <15><  5>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - A1-0-1 (Q=0) *)
  | (5, 0, 14, 0, 1) when (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 14 "VMOV" in
     let vd = arm_extension_register_op XDouble d in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMove (cc, dt, [vd WR; immop])

  (* <15><  5>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - A1-0-1 (Q=1) *)
  | (5, 0, 14, 1, 1) when (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 14 "VMOV" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMove (cc, dt, [vd WR; immop])

  (* <15><  5>D000<i><vd><cm>0011<i4> *) (* VBIC (immediate) - A1-0 (Q=0) *)
  | (5, 0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 0, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:VBIC-immediate: not reachable"])) in
     let vd = arm_extension_register_op XDouble d in
     (* VBIC<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseBitClear (cc, dt, vd WR, vd RD, immop)

  (* <15><  5>D000<i><vd><cm>0111<i4> *) (* VBIC (immediate) - A1-0 (Q=1) *)
  | (5, 0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 1, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:VBIC-immediate: not reachable"])) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VBIC<c>.<dt> <Qd>, #<imm> *)
     VectorBitwiseBitClear (cc, dt, vd WR, vd RD, immop)

  (* <15><  5>D000<i><vd><cm>0011<i4> *)  (* VMVN (immediate) - A1-0 (Q=0) *)
  | (5, 0, cm, 0, 1) when (bv 7) = 0 && (bv 5) = 1->
     let _ =
       if cm = 15 then
         raise (ARM_undefined ("VMVN immediate with cmode=15")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 cm "VMVN" in
     let vd = arm_extension_register_op XDouble d in
     (* VMVN<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseNot (cc, dt, vd WR, immop)

  (* <15><  5>D000<i><vd><cm>0111<i4> *)  (* VMVN (immediate) - A1-0 (Q=1) *)
  | (5, 0, cm, 1, 1) when (bv 7) = 0 && (bv 5) = 1 ->
     let _ =
       if cm = 15 then
         raise (ARM_undefined ("VMVN immediate with cmode=15")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 cm "VMVN" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMVN<c>.<dt> <Qd>, #<imm> *)
     VectorBitwiseNot (cc, dt, vd WR, immop)

  (* <15><  5>D11<vn><vd><i4>NQM0<vm> *) (* VEXT - A1 (Q=0) *)
  | (5, 3, i4, 0, 0) ->
     let _ =
       if (bv 11) = 1 then
         raise (ARM_undefined ("VEXT: Q=0 and imm4<3> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let imm = mk_arm_immediate_op false 4 (mkNumerical i4) in
     (* VEXT<c>.8 <Dd>, <Dn>, <Dm>, #<imm> *)
     VectorExtract (cc, VfpSize 8, vd WR, vn RD, vm RD, imm)

  (* <15><  5>D11<vn><vd><i4>NQM0<vm> *) (* VEXT - A1 (Q=1) *)
  | (5, 3, i4, 1, 0) ->
     let _ =
       if (bv 16) = 1 || (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined
              ("VEXT: Q=1 and Vd<0> = 1 or Vn<0> = 1 or Vm<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let imm = mk_arm_immediate_op false 4 (mkNumerical i4) in
     (* VEXT<c>.8 <Dd>, <Dn>, <Dm>, #<imm> *)
     VectorExtract (cc, VfpSize 8, vd WR, vn RD, vm RD, imm)

  (* <15><  5>D001000<vd><10>00M1<vm> *) (* VMOVL - A1-s *)
  | (5, 0, 10, 0, 1) when  (b 19 16) = 8 && (bv 7) = 0 ->
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VMOVL: Vd<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt 8 in
     (* VMOVL<c>.<dt> <Qd>, <Dm> *)
     VectorMoveLong (cc, dt, vd WR, vm RD)

  (* <15><  5>D010000<vd><10>00M1<vm> *) (* VMOVL - A1-s *)
  | (5, 1, 10, 0, 1) when  (b 19 16) = 0 && (bv 7) = 0 ->
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VMOVL: Vd<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt 16 in
     (* VMOVL<c>.<dt> <Qd>, <Dm> *)
     VectorMoveLong (cc, dt, vd WR, vm RD)

  (* <15><  5>D100000<vd><10>00M1<vm> *) (* VMOVL - A1-s *)
  | (5, 2, 10, 0, 1) when  (b 19 16) = 0 && (bv 7) = 0 ->
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VMOVL: Vd<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt 32 in
     (* VMOVL<c>.<dt> <Qd>, <Dm> *)
     VectorMoveLong (cc, dt, vd WR, vm RD)

  (* <15><  5>D<imm6><vd>< 0>LQM1<vm> *) (* VSHR - A1-s (Q=0) *)
  | (5, sz, 0, 0, 1) ->
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm = mk_arm_immediate_op true 4 (mkNumerical sam) in
     (* VSHR<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftRight (cc, dt, vd WR, vm RD, imm)

  (* <15><  5>D<imm6><vd>< 0>LQM1<vm> *) (* VSHR - A1-s (Q=1) *)
  | (5, sz, 0, 1, 1) ->
     let _ =
       if (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined ("VSHR: Q=1 and Vd<0> = 1 or Vm<0> = 1")) in
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm = mk_arm_immediate_op true 4 (mkNumerical sam) in
     (* VSHR<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftRight (cc, dt, vd WR, vm RD, imm)

  (* <15><  5>D<imm6><vd>< 1>LQM1<vm> *) (* VSRA - A1-s (Q=0) *)
  | (5, sz, 1, 0, 1) ->
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm = mk_arm_immediate_op true 4 (mkNumerical sam) in
     (* VSRA<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* <15><  5>D<imm6><vd>< 1>LQM1<vm> *) (* VSRA - A1-s (Q=1) *)
  | (5, sz, 1, 1, 1) ->
     let _ =
       if (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined ("VSRA: Q=1 and Vd<0> = 1 or Vm<0> = 1")) in
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm = mk_arm_immediate_op true 4 (mkNumerical sam) in
     (* VSRA<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* <15><  5>D<imm6><vd>< 3>LQM1<vm> *) (* VRSRA - A1-s (Q=0) *)
  | (5, sz, 3, 0, 1) ->
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VRSRA: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm = mk_arm_immediate_op true 4 (mkNumerical sam) in
     (* VRSRA<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorRoundingShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* <15><  5>D<imm6><vd>< 3>LQM1<vm> *) (* VRSRA - A1-s (Q=1) *)
  | (5, sz, 3, 1, 1) ->
     let _ =
       if (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined ("VRSRA: Q=1 and Vd<0> = 1 or Vm<0> = 1")) in
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VRSRA: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm = mk_arm_immediate_op true 4 (mkNumerical sam) in
     (* VRSRA<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorRoundingShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* <15><  5>D<imm6><vd>< 5>LQM1<vm> *) (* VSHL - A1 (Q=0) *)
  | (5, sz, 5, 0, 1) ->
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, imm6 - 8)
       | (0, (2 | 3)) -> (16, imm6 - 16)
       | (0, (4 | 5 | 6 | 7)) -> (32, imm6 - 32)
       | (1, _) -> (64, imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VSHL: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpInt esize in
     let imm = mk_arm_immediate_op true 4 (mkNumerical sam) in
     (* VSHL<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftLeft (cc, dt, vd WR, vm RD, imm)

  (* <15><  5>D<imm6><vd>< 5>LQM1<vm> *) (* VSHL - A1 (Q=1) *)
  | (5, sz, 5, 1, 1) ->
     let _ =
       if (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined ("VSHL: Q=1 and Vd<0> = 1 or Vm<0> = 1")) in
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, imm6 - 8)
       | (0, (2 | 3)) -> (16, imm6 - 16)
       | (0, (4 | 5 | 6 | 7)) -> (32, imm6 - 32)
       | (1, _) -> (64, imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VSHL: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpInt esize in
     let imm = mk_arm_immediate_op true 4 (mkNumerical sam) in
     (* VSHL<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftLeft (cc, dt, vd WR, vm RD, imm)

  (* <15><  5>Dsz<vn><vd>< 0>N0M0<vm> *) (* VADDL - A1-s *)
  | (5, ((0 | 1 | 2) as sz), 0, 0, 0) ->
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VADDL: Vd<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt (8 lsl sz) in
     (* VADDL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorAddLong (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  5>Dsz<vn><vd>< 1>N0M0<vm> *) (* VADDW - A1-s *)
  | (5, ((0 | 1 | 2) as sz), 1, 0, 0) ->
     let _ =
       if (bv 12) = 1 || (bv 16) = 1 then
         raise (ARM_undefined ("VADDW: Vd<0> = 1 or Vn<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt (8 lsl sz) in
     (* VADDW<c>.<dt> <Qd>, <Qn>, <Dm> *)
     VectorAddWide (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  5>Dsz<vn><vd>< 2>N1M0<vm> *)  (* VMLAL (by scalar) - A2-s (sz=1) *)
  | (5, 1, 2, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let m = b 2 0 in
     let index = ((bv 5) * 2) + (bv 3) in
     let dt = VfpSignedInt 16 in
     let elt = arm_extension_register_element_op XDouble m index 16 in
     (* VMLAL<c>.<dt> <Qd>, <Dn>, <Dm[x]>) *)
     VectorMultiplyAccumulateLong (cc, dt, vd WR, vn RD, elt RD)

  (* <15><  5>Dsz<vn><vd>< 2>N1M0<vm> *)  (* VMLAL (by scalar) - A2-s (sz=2) *)
  | (5, 2, 2, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let m = b 3 0 in
     let index = bv 5 in
     let dt = VfpSignedInt 32 in
     let elt = arm_extension_register_element_op XDouble m index 32 in
     (* VMLAL<c>.<dt> <Qd>, <Dn>, <Dm[x]>) *)
     VectorMultiplyAccumulateLong (cc, dt, vd WR, vn RD, elt RD)

  (* <15><  5>Dsz<vn><vd>< 8>N0M0<vm> *)  (* VMLAL (integer) - A2-s *)
  | (5, ((0 | 1 | 2) as sz), 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt (8 lsl sz) in
     (* VMLAL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorMultiplyAccumulateLong (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  5>Dsz<vn><vd><10>N1M0<vm> *)  (* VMULL (by scalar) - A2-s (sz=1) *)
  | (5, 1, 10, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let m = b 2 0 in
     let index = ((bv 5) * 2) + (bv 3) in
     let dt = VfpSignedInt 16 in
     let elt = arm_extension_register_element_op XDouble m index 16 in
     (* VMULL<c>.<dt> <Qd>, <Dn>, <Dm[x]>) *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, elt RD)

  (* <15><  5>Dsz<vn><vd><10>N1M0<vm> *)  (* VMULL (by scalar) - A2-s (sz=2) *)
  | (5, 2, 10, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let m = b 3 0 in
     let index = bv 5 in
     let dt = VfpSignedInt 32 in
     let elt = arm_extension_register_element_op XDouble m index 32 in
     (* VMULL<c>.<dt> <Qd>, <Dn>, <Dm[x]>) *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, elt RD)

  (* <15><  5>Dsz<vn><vd><12>N0M0<vm> *) (* VMULL (integer) - A2-s *)
  | (5, ((0 | 1 | 2) as sz), 12, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt (8 lsl sz) in
     (* VMULL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  5>D00<vn><vd><14>N0M0<vm> *) (* VMULL (polynomial) - A2-p *)
  | (5, 0, 14, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpPolynomial 8 in
     (* VMULL<c>.<dt>, <Qd>, <Dn>, <Dm> *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, vm RD)

  (* VMULL (polynomial) - A2 (crypto extension) *)
  (* <15><  5>D10<vn><vd><14>N0M0<vm> *)
  | (5, 2, 14, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpPolynomial 64 in
     (* VMULL<c>.<dt>, <Qd>, <Dn>, <Dm> *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  6>D00<vn><vd>< 1>NQM1<vm> *) (* VEOR - A1 (Q=0) *)
  | (6, 0, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     (* VEOR<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseExclusiveOr (cc, vd WR, vn RD, vm RD)

  (* <15><  6>D00<vn><vd>< 1>NQM1<vm> *) (* VEOR - A1 (Q=1) *)
  | (6, 0, 1, 1, 1) ->
     let _ =
       if (bv 16) = 1 || (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined
              ("VEOR: Q=1 and (Vd<0> = 1 or Vn<0> = 1 or Vm<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     (* VEOR<c> <Qd>, <Qn>, <Qm> *)
     VectorBitwiseExclusiveOr (cc, vd WR, vn RD, vm RD)

  (* <15><  6>Dsz<vn><vd>< 8>NQM0<vm> *) (* VSUB (integer) - A1 (Q=0) *)
  | (6, sz, 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpInt (8 lsl sz) in
     (* VSUB<c>.<dt> <Dd>, <Dn>, <Dm> *)
     VectorSubtract (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  6>Dsz<vn><vd>< 8>NQM0<vm> *) (* VSUB (integer) - A1 (Q=1) *)
  | (6, sz, 8, 1, 0) ->
     let _ =
       if (bv 16) = 1 || (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined
              ("VSUB: Q=1 and (Vd<0> = 1 or Vn<0> = 1 or Vm<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpInt (8 lsl sz) in
     (* VSUB<c>.<dt> <Qd>, <Qn>, <Qm> *)
     VectorSubtract (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  6>Dsz<vn><vd>< 9>NQM1<vm> *) (* VMUL (polynomial) - A1 (Q=0) *)
  | (6, sz, 9, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpPolynomial (8 lsl sz) in
     (* VMUL<c>.<dt> <Dd>, <Dn>, <Dm> *)
     VectorMultiply (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  6>Dsz<vn><vd>< 9>NQM1<vm> *) (* VMUL (polynomial) - A1 (Q=1) *)
  | (6, sz, 9, 1, 1) ->
     let _ =
       if (bv 16) > 0 || (bv 12) > 0 || (bv 0) > 0 then
         raise
           (ARM_undefined
              ("VMUL: Q=1 && (Vd<0> == 1 || Vn<0> == 1 || Vm<0. == 1)")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpPolynomial (8 lsl sz) in
     (* VMUL<c>.<dt> <Qd>, <Qn>, <Qm> *)
     VectorMultiply (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  7>D000<i><vd><cm>0011<i4) *) (* VORR (immediate) - A1-1 (Q=0) *)
  | (7, 0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 0, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:VBIC-immediate: not reachable"])) in
     let vd = arm_extension_register_op XDouble d in
     (* VORR<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseOr (cc, dt, vd WR, vd RD, immop)

  (* <15><  7>D000<i><vd><cm>0111<i4) *) (* VORR (immediate) - A1-1 (Q=1) *)
  | (7, 0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 1, 1)
       when (bv 19 = 0) && (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:VBIC-immediate: not reachable"])) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VORR<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseOr (cc, dt, vd WR, vd RD, immop)

  (* <15><  7>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - A1-1-0 (Q=0) *)
  | (7, 0, cm, 0, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 cm "VMOV" in
     let vd = arm_extension_register_op XDouble d in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMove (cc, dt, [vd WR; immop])

  (* <15><  7>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - A1-1-0 (Q=1) *)
  | (7, 0, cm, 1, 1) when (bv 19) = 0  && (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 cm "VMOV" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMove (cc, dt, [vd WR; immop])

  (* <15><  7>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - A1-1-1 (Q=0) *)
  | (7, 0, 14, 0, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 14 "VMOV" in
     let vd = arm_extension_register_op XDouble d in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMove (cc, dt, [vd WR; immop])

  (* <15><  7>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - A1-1-1 (Q=1) *)
  | (7, 0, 14, 1, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 14 "VMOV" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMove (cc, dt, [vd WR; immop])

  (* <15><  7>D000<i><vd><cm>0011<i4> *) (* VBIC (immediate) - A1-1 (Q=0) *)
  | (7, 0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 0, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:BIC-immediate:unreachable"])) in
     let vd = arm_extension_register_op XDouble d in
     (* VBIC<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseBitClear (cc, dt, vd WR, vd RD, immop)

  (* <15><  7>D000<i><vd><cm>0111<i4> *) (* VBIC (immediate) - A1-1 (Q=1) *)
  | (7, 0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 1, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:BIC-immediate:unreachable"])) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VBIC<c>.<dt> <Qd>, #<imm> *)
     VectorBitwiseBitClear (cc, dt, vd WR, vd RD, immop)

  (* <15><  7>D000<i><vd><cm>0011<i4> *)  (* VMVN (immediate) - A1-1 (Q=0) *)
  | (7, 0, cm, 0, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let _ =
       if cm = 15 then
         raise (ARM_undefined "VMVN immediate with cmode=15") in
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 cm "VMVN" in
     let vd = arm_extension_register_op XDouble d in
     (* VMVN<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseNot (cc, dt, vd WR, immop)

  (* <15><  7>D000<i><vd><cm>0111<i4> *)  (* VMVN (immediate) - A1-1 (Q=1) *)
  | (7, 0, cm, 1, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let _ =
       if cm = 15 then
         raise (ARM_undefined "VMVN immediate with cmode=15") in
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = mk_arm_immediate_op false 4 (mkNumerical imm8) in
     let dt = adv_simd_mod_dt 0 cm "VMVN" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMVN<c>.<dt> <Qd>, #<imm> *)
     VectorBitwiseNot (cc, dt, vd WR, immop)

  (* <15><  7>D001000<vd><10>00M1<vm> *) (* VMOVL - A1-u (imm3=1) *)
  | (7, 0, 10, 0, 1) when  (b 19 16) = 8 && (bv 7) = 0 ->
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VMOVL: Vd<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt 8 in
     (* VMOVL<c>.<dt> <Qd>, <Dm> *)
     VectorMoveLong (cc, dt, vd WR, vm RD)

  (* <15><  7>D010000<vd><10>00M1<vm> *) (* VMOVL - A1-u (imm3=2) *)
  | (7, 1, 10, 0, 1) when  (b 19 16) = 0 && (bv 7) = 0 ->
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VMOVL: Vd<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt 16 in
     (* VMOVL<c>.<dt> <Qd>, <Dm> *)
     VectorMoveLong (cc, dt, vd WR, vm RD)

  (* <15><  7>D100000<vd><10>00M1<vm> *) (* VMOVL - A1-u (imm3=4) *)
  | (7, 2, 10, 0, 1) when  (b 19 16) = 0 && (bv 7) = 0 ->
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VMOVL: Vd<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt 32 in
     (* VMOVL<c>.<dt> <Qd>, <Dm> *)
     VectorMoveLong (cc, dt, vd WR, vm RD)

  (* <15><  7>D11<vn><vd>< 8>N0M0<vm> *)  (* VTBL - A1-1 *)
  | (7, 3, 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let xlst = arm_extension_register_list_op XDouble n 1 in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize 8 in
     (* VTBL<c>.8 <Dd>, <list>, <Dm> *)
     VectorTableLookup (cc, dt, vd WR, xlst RD, vm RD)

  (* <15><  7>D11<vn><vd>< 9>N0M0<vm> *)  (* VTBL - A1-2 *)
  | (7, 3, 9, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let _ =
       if n > 30 then
         raise
           (ARM_unpredictable ("VTBL: n+length > 32")) in
     let vd = arm_extension_register_op XDouble d in
     let xlst = arm_extension_register_list_op XDouble n 2 in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize 8 in
     (* VTBL<c>.8 <Dd>, <list>, <Dm> *)
     VectorTableLookup (cc, dt, vd WR, xlst RD, vm RD)

  (* <15><  7>D11<vn><vd><10>N0M0<vm> *)  (* VTBL - A1-3 *)
  | (7, 3, 10, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let _ =
       if n > 29 then
         raise
           (ARM_unpredictable ("VTBL: n+length > 32")) in
     let vd = arm_extension_register_op XDouble d in
     let xlst = arm_extension_register_list_op XDouble n 3 in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize 8 in
     (* VTBL<c>.8 <Dd>, <list>, <Dm> *)
     VectorTableLookup (cc, dt, vd WR, xlst RD, vm RD)

  (* <15><  7>D11<vn><vd><11>N0M0<vm> *)  (* VTBL - A1-4 *)
  | (7, 3, 11, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let _ =
       if n > 28 then
         raise
           (ARM_unpredictable ("VTBL: n+length > 32")) in
     let vd = arm_extension_register_op XDouble d in
     let xlst = arm_extension_register_list_op XDouble n 2 in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize 8 in
     (* VTBL<c>.8 <Dd>, <list>, <Dm> *)
     VectorTableLookup (cc, dt, vd WR, xlst RD, vm RD)

  (* <15><  7>D11<i4><vd><12>0QM0<vm> *)  (* VDUP (scalar) A1 (Q=0) *)
  | (7, 3, 12, 0, 0) when (bv 7) = 0 ->
     let imm4 = b 19 16 in
     let _ =
       if imm4 = 0 || imm4 = 8 then
         raise (ARM_undefined ("VDUP: imm4 IN x000")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let (esize, index, elts) =
       match (b 18 16) with
       | 1 | 3 | 5 | 7 -> (8, b 19 17, 8)
       | 2 | 6 -> (16, b 19 18, 4)
       | _ -> (32, bv 19, 2) in
     let dt = VfpSize esize in
     let vd = arm_extension_register_op XDouble d in
     let elt = arm_extension_register_element_op XDouble m index esize in
     (* VDUP<c>.<size> <Dd>, <Dm[x]> *)
     VectorDuplicate (cc, dt, 1, elts, vd WR, elt RD)

  (* <15><  7>D11<i4><vd><12>0QM0<vm> *)  (* VDUP (scalar) - A1 (Q=1) *)
  | (7, 3, 12, 1, 0) when (bv 7) = 0 ->
     let imm4 = b 19 16 in
     let _ =
       if imm4 = 0 || imm4 = 8 then
         raise (ARM_undefined ("VDUP: imm4 IN x000")) in
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VDUP: Q=1 and (Vd<0> = 1)")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let (esize, index, elts) =
       match (b 18 16) with
       | 1 | 3 | 5 | 7 -> (8, b 19 17, 8)
       | 2 | 6 -> (16, b 19 18, 4)
       | _ -> (32, bv 19, 2) in
     let dt = VfpSize esize in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let elt = arm_extension_register_element_op XDouble m index esize in
     (* VDUP<c>.<size> <Dd>, <Dm[x]> *)
     VectorDuplicate (cc, dt, 2, elts, vd WR, elt RD)

  (* <15><  7>D11sz00<vd>< 1>0QM0<vm> *) (* VREV16 - A1 (Q=0) *)
  | (7, 3, 1, 0, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let sz = b 19 18 in
     let dt = VfpSize (8 lsl sz) in
     (* VREV16.<size> <Dd>, <Dm> *)
     VectorReverseHalfwords (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 1>0QM0<vm> *) (* VREV16 - A1 (Q=1) *)
  | (7, 3, 1, 1, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let sz = b 19 18 in
     let dt = VfpSize (8 lsl sz) in
     (* VREV16.<size> <Qd>, <Qm> *)
     VectorReverseHalfwords (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 0>1QM0<vm> *) (* VREV32 - A1 (Q=0) *)
  | (7, 3, 0, 0, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let sz = b 19 18 in
     let dt = VfpSize (8 lsl sz) in
     (* VREV32.<size> <Dd>, <Dm> *)
     VectorReverseWords (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 0>1QM0<vm> *) (* VREV32 - A1 (Q=1) *)
  | (7, 3, 0, 1, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let sz = b 19 18 in
     let dt = VfpSize (8 lsl sz) in
     (* VREV32.<size> <Qd>, <Qm> *)
     VectorReverseWords (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 0>0QM0<vm> *) (* VREV64 - A1 (Q=0) *)
  | (7, 3, 0, 0, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VREV64.<size> <Dd>, <Dm> *)
     VectorReverseDoublewords (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 0>0QM0<vm> *) (* VREV64 - A1 (Q=1) *)
  | (7, 3, 0, 1, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VREV64.<size> <Qd>, <Qm> *)
     VectorReverseDoublewords (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz10<vd>< 0>1QM0<vm> *)   (* VTRN - A1 (Q=0) *)
  | (7, 3, 0, 0, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VTRN.<size> <Dd>, <Dm> *)
     VectorTranspose (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz10<vd>< 0>1QM0<vm> *)   (* VTRN - A1 (Q=1) *)
  | (7, 3, 0, 1, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VTRN.<size> <Qd>, <Qm> *)
     VectorTranspose (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz10<vd>< 1>1QM0<vm> *)   (* VZIP - A1 (Q=0) *)
  | (7, 3, 1, 0, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VZIP.<size> <Dd>, <Dm> *)
     VectorZip (cc, dt, vd RW, vm RW)

  (* <15><  7>D11sz10<vd>< 1>1QM0<vm> *)   (* VZIP - A1 (Q=1) *)
  | (7, 3, 1, 1, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VZIP.<size> <Qd>, <Qm> *)
     VectorZip (cc, dt, vd RW, vm RW)

  (* <15><  7>D11sz10<vd>< 2>00M0<vm> *)   (* VMOVN - A1 *)
  | (7, 3, 2, 0, 0) when (b 17 16) = 2 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VMOVN.<size> <Dd>, <Qm> *)
     VectorMoveNarrow (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 3>00M0<vm> *) (* AESE - A1 *)
  | (7, 3, 3, 0, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 8 in
     (* AESE.<dt> <Qd>, <Qm> *)
     AESSingleRoundEncryption (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 3>10M0<vm> *) (* AESMC - A1 *)
  | (7, 3, 3, 0, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 8 in
     (* AESMC.<dt> <Qd>, <Qm> *)
     AESMixColumns (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 3>01M0<vm> *) (* AESD - A1 *)
  | (7, 3, 3, 1, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 8 in
     (* AESE.<dt> <Qd>, <Qm> *)
     AESSingleRoundDecryption (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz00<vd>< 3>11M0<vm> *) (* AESIMC - A1 *)
  | (7, 3, 3, 1, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 8 in
     (* AESIMC.<dt> <Qd>, <Qm> *)
     AESInverseMixColumns (cc, dt, vd WR, vm RD)

  (* <15><  7>D11sz01<vd>< 4>11M0<vm> *)  (* SHA1H - A1 *)
  | (7, 3, 4, 1, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1H.<dt> <Qd>, <Qm> *)
     SHA1FixedRotate (cc, dt, vd WR, vm RD)

  (* <15><  7>D<imm6><vd>< 0>LQM1<vm> *) (* VSHR - A1-u (Q=0) *)
  | (7, sz, 0, 0, 1)  when ((bv 7) = 1 || (b 21 19) > 0) ->
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpUnsignedInt esize in
     let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
     (* VSHR<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftRight (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 0>LQM1<vm> *) (* VSHR - A1-u (Q=1) *)
  | (7, sz, 0, 1, 1)  when ((bv 7) = 1 || (b 21 19) > 0) ->
     let _ =
       if (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined ("VSHR: Q=1 and Vd<0> = 1 or Vm<0> = 1")) in
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpUnsignedInt esize in
     let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
     (* VSHR<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftRight (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 1>LQM1<vm> *) (* VSRA - A1-u (Q=0) *)
  | (7, sz, 1, 0, 1)  when ((bv 7) = 1 || (b 21 19) > 0) ->
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VSRA: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpUnsignedInt esize in
     let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
     (* VSRA<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 1>LQM1<vm> *) (* VSRA - A1-u (Q=1) *)
  | (7, sz, 1, 1, 1)  when ((bv 7) = 1 || (b 21 19) > 0) ->
     let _ =
       if (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined ("VSRA: Q=1 and Vd<0> = 1 or Vm<0> = 1")) in
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VSRA: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpUnsignedInt esize in
     let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
     (* VSRA<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 3>LQM1<vm> *) (* VRSRA - A1-u (Q=0) *)
  | (7, sz, 3, 0, 1)  when ((bv 7) = 1 || (b 21 19) > 0) ->
     let imm6 = b 21 16 in
      let d = prefix_bit (bv 22) (b 15 12) in
      let m = prefix_bit (bv 5) (b 3 0) in
      let vd = arm_extension_register_op XDouble d in
      let vm = arm_extension_register_op XDouble m in
      let (esize, sam) =
        match (bv 7, b 21 19) with
        | (0, 1) -> (8, 16 - imm6)
        | (0, (2 | 3)) -> (16, 32 - imm6)
        | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
        | (1, _) -> (64, 64 - imm6)
        | _ ->
           raise
             (BCH_failure
                (LBLOCK [
                     STR "cond15:VRSRA: ";
                     INT (bv 7);
                     STR ", ";
                     INT (b 21 19)])) in
      let dt = VfpUnsignedInt esize in
      let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
      (* VRSRA<c>.<dt> <Dd>, <Dm>, #<imm> *)
      VectorRoundingShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 3>LQM1<vm> *) (* VRSRA - A1-u (Q=1) *)
  | (7, sz, 3, 1, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
     let _ =
       if (bv 12) = 1 || (bv 0) = 1 then
         raise
           (ARM_undefined ("VSRA: Q=1 and Vd<0> = 1 or Vm<0> = 1")) in
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let (esize, sam) =
       match (bv 7, b 21 19) with
       | (0, 1) -> (8, 16 - imm6)
       | (0, (2 | 3)) -> (16, 32 - imm6)
       | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
       | (1, _) -> (64, 64 - imm6)
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "cond15:VRSRA: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpUnsignedInt esize in
     let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
     (* VRSRA<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorRoundingShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 4>LQM1<vm> *) (* VSRI - A1 (Q=0) *)
  | (7, _, 4, 0, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let imm6 = b 21 16 in
       let (esize, sam) =
         match (bv 7, b 21 19) with
         | (0, 1) -> (8, 16 - imm6)
         | (0, (2 | 3)) -> (16, 32 - imm6)
         | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
         | (1, _) -> (64, 64 - imm6)
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "cond15:VSRI: ";
                      INT (bv 7);
                      STR ", ";
                      INT (b 21 19)])) in
       let dt = VfpSize esize in
       let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
       (* VSRI<c>.<size> <Dd>, <Dm>, #<imm> *)
       VectorShiftRightInsert (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 4>LQM1<vm> *) (* VSRI - A1 (Q=1) *)
  | (7, _, 4, 1, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let imm6 = b 21 16 in
       let (esize, sam) =
         match (bv 7, b 21 19) with
         | (0, 1) -> (8, 16 - imm6)
         | (0, (2 | 3)) -> (16, 32 - imm6)
         | (0, (4 | 5 | 6 | 7)) -> (32, 64 - imm6)
         | (1, _) -> (64, 64 - imm6)
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "cond15:VSRI: ";
                      INT (bv 7);
                      STR ", ";
                      INT (b 21 19)])) in
       let dt = VfpSize esize in
       let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
       (* VSRI<c>.<size> <Qd>, <Qm>, #<imm> *)
       VectorShiftRightInsert (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 5>LQM1<vm> *) (* VSLI - A1 (Q=0) *)
  | (7, _, 5, 0, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let imm6 = b 21 16 in
       let (esize, sam) =
         match (bv 7, b 21 19) with
         | (0, 1) -> (8, imm6 - 8)
         | (0, (2 | 3)) -> (16, imm6 - 16)
         | (0, (4 | 5 | 6 | 7)) -> (32, imm6 - 32)
         | (1, _) -> (64, imm6)
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "cond15:VSLI: ";
                      INT (bv 7);
                      STR ", ";
                      INT (b 21 19)])) in
       let dt = VfpSize esize in
       let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
       (* VSLI<c>.<size> <Dd>, <Dm>, #<imm> *)
       VectorShiftLeftInsert (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>D<imm6><vd>< 5>LQM1<vm> *) (* VSLI - A1 (Q=1) *)
  | (7, _, 5, 1, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let imm6 = b 21 16 in
       let (esize, sam) =
         match (bv 7, b 21 19) with
         | (0, 1) -> (8, imm6 - 8)
         | (0, (2 | 3)) -> (16, imm6 - 16)
         | (0, (4 | 5 | 6 | 7)) -> (32, imm6 - 32)
         | (1, _) -> (64, imm6)
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "cond15:VSLI: ";
                      INT (bv 7);
                      STR ", ";
                      INT (b 21 19)])) in
       let dt = VfpSize esize in
       let imm = mk_arm_immediate_op false 4 (mkNumerical sam) in
       (* VSLI<c>.<size> <Qd>, <Qm>, #<imm> *)
       VectorShiftLeftInsert (cc, dt, vd WR, vm RD, imm)

  (* <15><  7>Dsz<vn><vd>< 0>N0M0<vm> *) (* VADDL - A1-u *)
  | (7, ((0 | 1 | 2) as sz), 0, 0, 0) ->
     let _ =
       if (bv 12) = 1 then
         raise (ARM_undefined ("VADDL: Vd<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt (8 lsl sz) in
     (* VADDL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorAddLong (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  7>Dsz<vn><vd>< 1>N0M0<vm> *) (* VADDW - A1-u *)
  | (7, ((0 | 1 | 2) as sz), 1, 0, 0) ->
     let _ =
       if (bv 12) = 1 || (bv 16) = 1 then
         raise (ARM_undefined ("VADDW: Vd<0> = 1 or Vn<0> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt (8 lsl sz) in
     (* VADDW<c>.<dt> <Qd>, <Qn>, <Dm> *)
     VectorAddWide (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  7>Dsz<vn><vd>< 2>N1M0<vm> *)  (* VMLAL (by scalar) - A2-u (sz=1) *)
  | (7, 1, 2, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let m = b 2 0 in
     let index = ((bv 5) * 2) + (bv 3) in
     let dt = VfpUnsignedInt 16 in
     let elt = arm_extension_register_element_op XDouble m index 16 in
     (* VMLAL<c>.<dt> <Qd>, <Dn>, <Dm[x]>) *)
     VectorMultiplyAccumulateLong (cc, dt, vd WR, vn RD, elt RD)

  (* <15><  7>Dsz<vn><vd>< 2>N1M0<vm> *)  (* VMLAL (by scalar) - A2-u (sz=2) *)
  | (7, 2, 2, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let m = b 3 0 in
     let index = bv 5 in
     let dt = VfpUnsignedInt 32 in
     let elt = arm_extension_register_element_op XDouble m index 32 in
     (* VMLAL<c>.<dt> <Qd>, <Dn>, <Dm[x]>) *)
     VectorMultiplyAccumulateLong (cc, dt, vd WR, vn RD, elt RD)

  (* <15><  7>Dsz<vn><vd>< 8>N0M0<vm> *)  (* VMLAL (integer) - A2-u *)
  | (7, ((0 | 1 | 2) as sz), 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt (8 lsl sz) in
     (* VMLAL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorMultiplyAccumulateLong (cc, dt, vd WR, vn RD, vm RD)

  (* <15><  7>Dsz<vn><vd><10>N1M0<vm> *)  (* VMULL (by scalar) - A2-u (sz=1) *)
  | (7, 1, 10, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let m = b 2 0 in
     let index = ((bv 5) * 2) + (bv 3) in
     let dt = VfpUnsignedInt 16 in
     let elt = arm_extension_register_element_op XDouble m index 16 in
     (* VMULL<c>.<dt> <Qd>, <Dn>, <Dm[x]>) *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, elt RD)

  (* <15><  7>Dsz<vn><vd><10>N1M0<vm> *)  (* VMULL (by scalar) - A2-u (sz=2) *)
  | (7, 2, 10, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let m = b 3 0 in
     let index = bv 5 in
     let dt = VfpUnsignedInt 32 in
     let elt = arm_extension_register_element_op XDouble m index 32 in
     (* VMULL<c>.<dt> <Qd>, <Dn>, <Dm[x]>) *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, elt RD)

  (* <15><  7>Dsz<vn><vd><12>N0M0<vm> *)  (* VMULL (integer) - A2-u *)
  | (7, ((0 | 1 | 2) as sz), 12, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt (8 lsl sz) in
     (* VMULL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, vm RD)

  (*  <15><  8>D00<rn><vd>< 2>szal<rm> *) (* VST1 (multiple single elts) - A1-4 *)
  | (8, 0, 2, _, _) ->
     let sz = b 7 6 in
     let align = b 5 4 in
     let alignment = if align = 0 then 1 else 4 lsl align in
     let ebytes = 1 lsl sz in
     let dt = VfpSize (8 * ebytes) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = b 19 16 in
     let m = b 3 0 in
     let rm = get_arm_reg m in
     let (wb, wback) =
       match m with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred 8)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let mem = mk_arm_simd_address_op (get_arm_reg n) alignment wback in
     let rn = arm_register_op (get_arm_reg n) in
     let rnop = if wb then rn WR else rn RD in
     let rmop = arm_register_op rm RD in
     let rlist = arm_simd_reg_list_op XDouble [d; d + 1; d + 2; d + 3] in
     VectorStoreOne (wb, cc, dt, rlist RD, rnop, mem WR, rmop)

  (*  <15><  8>D00<rn><vd>< 6>szal<rm> *) (* VST1 (multiple single elts) - A1-3 *)
  | (8, 0, 6, _, _) ->
     let sz = b 7 6 in
     let align = b 5 4 in
     let alignment = if align = 0 then 1 else 4 lsl align in
     let ebytes = 1 lsl sz in
     let dt = VfpSize (8 * ebytes) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = b 19 16 in
     let m = b 3 0 in
     let rm = get_arm_reg m in
     let (wb, wback) =
       match m with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred 8)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let mem = mk_arm_simd_address_op (get_arm_reg n) alignment wback in
     let rn = arm_register_op (get_arm_reg n) in
     let rnop = if wb then rn WR else rn RD in
     let rmop = arm_register_op rm RD in
     let rlist = arm_simd_reg_list_op XDouble [d; d + 1; d + 2] in
     VectorStoreOne (wb, cc, dt, rlist RD, rnop, mem WR, rmop)

  (*  <15><  8>D00<rn><vd>< 7>szal<rm> *) (* VST1 (multiple single elts) - A1-1 *)
  | (8, 0, 7, _, _) ->
     let sz = b 7 6 in
     let align = b 5 4 in
     let alignment = if align = 0 then 1 else 4 lsl align in
     let ebytes = 1 lsl sz in
     let dt = VfpSize (8 * ebytes) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = b 19 16 in
     let m = b 3 0 in
     let rm = get_arm_reg m in
     let (wb, wback) =
       match m with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred 8)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let mem = mk_arm_simd_address_op (get_arm_reg n) alignment wback in
     let rn = arm_register_op (get_arm_reg n) in
     let rnop = if wb then rn WR else rn RD in
     let rmop = arm_register_op rm RD in
     let rlist = arm_simd_reg_list_op XDouble [d] in
     VectorStoreOne (wb, cc, dt, rlist RD, rnop, mem WR, rmop)

  (* <15><  8>D00<rn><vd><10>szal<rm> *) (* VST1 (multiple single elts) - A1-2 *)
  | (8, 0, 10, _, _) ->
     let sz = b 7 6 in
     let align = b 5 4 in
     let alignment = if align = 0 then 1 else 4 lsl align in
     let ebytes = 1 lsl sz in
     let dt = VfpSize (8 * ebytes) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = b 19 16 in
     let m = b 3 0 in
     let rm = get_arm_reg m in
     let (wb, wback) =
       match m with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred 8)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let mem = mk_arm_simd_address_op (get_arm_reg n) alignment wback in
     let rn = arm_register_op (get_arm_reg n) in
     let rnop = if wb then rn WR else rn RD in
     let rmop = arm_register_op rm RD in
     let rlist = arm_simd_reg_list_op XDouble [d; d + 1] in
     VectorStoreOne (wb, cc, dt, rlist RD, rnop, mem WR, rmop)

  (* <15><  8>D10<rn><vd>< 2>szal<rm> *) (* VLD1 (multiple single elts) - A1-4 *)
  | (8, 2, 2, _, _) ->
     let sz = b 7 6 in
     let align = b 5 4 in
     let alignment = if align = 0 then 1 else 4 lsl align in
     let ebytes = 1 lsl sz in
     let dt = VfpSize (8 * ebytes) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = b 19 16 in
     let m = b 3 0 in
     let rm = get_arm_reg m in
     let (wb, wback) =
       match m with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred 8)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let mem = mk_arm_simd_address_op (get_arm_reg n) alignment wback in
     let rn = arm_register_op (get_arm_reg n) in
     let rnop = if wb then rn WR else rn RD in
     let rmop = arm_register_op rm RD in
     let rlist = arm_simd_reg_list_op XDouble [d; d + 1; d + 2; d + 3] in
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}]{!} *)
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}], <Rm> *)
     VectorLoadOne (wb, cc, dt, rlist WR, rnop, mem RD, rmop)

  (* <15><  8>D10<rn><vd>< 6>szal<rm> *) (* VLD1 (multiple single elts) - A1-3 *)
  | (8, 2, 6, _, _) ->
     let sz = b 7 6 in
     let align = b 5 4 in
     let alignment = if align = 0 then 1 else 4 lsl align in
     let ebytes = 1 lsl sz in
     let dt = VfpSize (8 * ebytes) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = b 19 16 in
     let m = b 3 0 in
     let rm = get_arm_reg m in
     let (wb, wback) =
       match m with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred 8)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let mem = mk_arm_simd_address_op (get_arm_reg n) alignment wback in
     let rn = arm_register_op (get_arm_reg n) in
     let rnop = if wb then rn WR else rn RD in
     let rmop = arm_register_op rm RD in
     let rlist = arm_simd_reg_list_op XDouble [d; d + 1; d + 2] in
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}]{!} *)
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}], <Rm> *)
     VectorLoadOne (wb, cc, dt, rlist WR, rnop, mem RD, rmop)

  (* <15><  8>D10<rn><vd>< 7>szal<rm> *) (* VLD1 (multiple single elts) - A1-1 *)
  | (8, 2, 7, _, _) ->
     let sz = b 7 6 in
     let align = b 5 4 in
     let alignment = if align = 0 then 1 else 4 lsl align in
     let ebytes = 1 lsl sz in
     let dt = VfpSize (8 * ebytes) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = b 19 16 in
     let m = b 3 0 in
     let rm = get_arm_reg m in
     let (wb, wback) =
       match m with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred 8)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let mem = mk_arm_simd_address_op (get_arm_reg n) alignment wback in
     let rn = arm_register_op (get_arm_reg n) in
     let rnop = if wb then rn WR else rn RD in
     let rmop = arm_register_op rm RD in
     let rlist = arm_simd_reg_list_op XDouble [d] in
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}]{!} *)
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}], <Rm> *)
     VectorLoadOne (wb, cc, dt, rlist WR, rnop, mem RD, rmop)

  (* <15><  8>D10<rn><vd><10>szal<rm> *) (* VLD1 (multiple single elts) - A1-2 *)
  | (8, 2, 10, _, _) ->
     let sz = b 7 6 in
     let align = b 5 4 in
     let alignment = if align = 0 then 1 else 4 lsl align in
     let ebytes = 1 lsl sz in
     let dt = VfpSize (8 * ebytes) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = b 19 16 in
     let m = b 3 0 in
     let rm = get_arm_reg m in
     let (wb, wback) =
       match m with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred 8)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let mem = mk_arm_simd_address_op (get_arm_reg n) alignment wback in
     let rn = arm_register_op (get_arm_reg n) in
     let rnop = if wb then rn WR else rn RD in
     let rmop = arm_register_op rm RD in
     let rlist = arm_simd_reg_list_op XDouble [d; d + 1] in
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}]{!} *)
       (* VLD1<c>.<size> <list>, [<Rn>{:<align>}], <Rm> *)
     VectorLoadOne (wb, cc, dt, rlist WR, rnop, mem RD, rmop)

  (* <15>< 10>101<15><15><--imm12---> *)  (* PLD (literal) - A1-sub *)
  | (10, 1, _, _, _) when (bv 22) = 1 && (b 19 16) = 15 && (b 15 12) = 15 ->
     let imm12 = b 11 0 in
     let pcreg = arm_register_op (get_arm_reg 15) in
     let immop = arm_literal_op ~is_add:false (iaddr#add_int 8) imm12 in
     (* PLD <label> *)
     PreloadData (false, cc, pcreg RD, immop)

  (* <15>< 10>R01<rn><15><--imm12---> *)    (* PLD (immediate) - A1-sub *)
  | (10, 1, _, _, _) when (b 15 12) = 15 ->
     let imm12 = b 11 0 in
     let offset = ARMImmOffset imm12 in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let is_pldw = (bv 22) = 0 in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:false ~isindex:true ~iswback:false in
     (* PLD{W} [<Rn>, #+/-<imm12>] *)
     PreloadData (is_pldw, cc, rn RD, mem WR)

  (* <15>< 11>101<15><15><--imm12---> *)  (* PLD (literal) - A1-add *)
  | (11, 1, _, _, _) when (bv 22) = 1 && (b 19 16) = 15 && (b 15 12) = 15 ->
     let imm12 = b 11 0 in
     let pcreg = arm_register_op (get_arm_reg 15) in
     let immop = arm_literal_op ~is_add:true (iaddr#add_int 8) imm12 in
     (* PLD <label> *)
     PreloadData (false, cc, pcreg RD, immop)

  (* <15>< 11>R01<rn><15><--imm12---> *)    (* PLD (immediate) - A1-add *)
  | (11, 1, _, _, _) when (b 15 12) = 15 ->
     let imm12 = b 11 0 in
     let offset = ARMImmOffset imm12 in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let is_pldw = (bv 22) = 0 in
     let mem =
       mk_arm_offset_address_op
         ~align:4 rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* PLD{W} [<Rn>, #+/-<imm12>] *)
     PreloadData (is_pldw, cc, rn RD, mem WR)

  (* <15>1010<--------imm24---------> *)    (* BLX - A2 *)
  | ((20 | 21), _, _, _, _) ->
     let imm = sign_extend 32 26 ((b 23 0) lsl 2) in
     let imm32 = if imm > e31 then imm - e32 else imm in
     let tgt = iaddr#add_int (imm32 + 8) in
     let tgtop = arm_absolute_op tgt RD in
     (* BLX <label> *)
     BranchLinkExchange(cc, tgtop)

  (* <15>1011<--------imm24---------> *)    (* BLX - A2 *)
  | ((22 | 23), _, _, _, _) ->
     let imm = sign_extend 32 26 (((b 23 0) lsl 2) + 2) in
     let imm32 = if imm > e31 then imm - e32 else imm in
     let tgt = iaddr#add_int (imm32 + 8) in
     let tgtop = arm_absolute_op tgt RD in
     (* BLX <label> *)
     BranchLinkExchange(cc, tgtop)

  | (x, y, z, q, v) ->
     NotRecognized (
         "arm:cond15:"
         ^ (string_of_int x)
         ^ "_"
         ^ (string_of_int y)
         ^ "_"
         ^ (string_of_int z)
         ^ "_"
         ^ (string_of_int q)
         ^ "_"
         ^ (string_of_int v),
         instr)


let parse_opcode
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instrbytes: doubleword_int):arm_opcode_t =
  let b = instrbytes#get_segval in
  let bv = instrbytes#get_bitval in
  let cond = b 31 28 in
  let opc = b 27 25 in
  if cond = 15 then
    parse_cond15 instrbytes iaddr
  else
    match opc with
    | 0 when (b 7 4) = 9 ->
       parse_data_proc_reg_misc instrbytes cond
    | 0 when (bv 4) = 1 && (bv 7) = 1 ->
       parse_data_proc_reg_load_stores instrbytes cond
    | 0 -> parse_data_proc_reg_type instrbytes cond
    | 1 -> parse_data_proc_imm_type ch iaddr instrbytes cond
    | 2 -> parse_load_store_imm_type iaddr instrbytes cond
    | 3 when (instrbytes#get_bitval 4) = 1 ->
       parse_media_type instrbytes cond
    | 3 -> parse_load_store_reg_type instrbytes cond
    | 4 when (instrbytes#get_bitval 22) = 0 ->
       parse_block_data_type instrbytes cond
    | 5 -> parse_branch_link_type iaddr instrbytes cond
    | 6 -> parse_misc_6_type instrbytes cond
    | 7 -> parse_misc_7_type iaddr instrbytes cond
    | _ ->
       raise (BCH_failure (LBLOCK [STR "ARM:parse_opcode: Not reachable"]))


let disassemble_arm_instruction
      (ch:pushback_stream_int) (iaddr:doubleword_int) (instrbytes:doubleword_int) =
  try
    parse_opcode ch iaddr instrbytes
  with
  | ARM_undefined s ->
     begin
       ch_error_log#add
         "ARM instruction:UNPREDICTABLE"
         (LBLOCK [iaddr#toPretty; STR ": "; STR s]);
       OpcodeUndefined s
     end
  | ARM_unpredictable s ->
     begin
       ch_error_log#add
         "ARM instruction:UNDEFINED"
         (LBLOCK [iaddr#toPretty; STR ": "; STR s]);
       OpcodeUnpredictable s
     end
  | BCH_failure p ->
     begin
       ch_error_log#add
         "disassembly - ARM"
         (LBLOCK [
              STR "Error in disassembling ARM: ";
              iaddr#toPretty;
              STR ": ";
              p]);
       raise (BCH_failure p)
     end
  | IO.No_more_input ->
     let address = iaddr#add_int 4 in
     begin
       ch_error_log#add
         "no more input"
         (LBLOCK [
              STR "No more input at position ";
              address#toPretty ; STR " (" ;
              INT ch#pos;
              STR ")"]) ;
       raise IO.No_more_input
     end

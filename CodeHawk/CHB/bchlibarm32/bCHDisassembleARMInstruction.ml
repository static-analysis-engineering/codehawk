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

(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16

let stri = string_of_int

let parse_data_proc_reg_load_stores
      (c:arm_opcode_cc_t)
      (bit24_21:int)
      (bit20:int)
      (bit19_16:int)
      (bit15_12:int)
      (bit11_8:int)
      (bit6_5:int)
      (bit3_0:int) =
  (* <cc><0>.................1..1.... *)
  let p = bit24_21 lsr 3 in
  let u = (bit24_21 lsr 2) mod 2 in
  let w = bit24_21 mod 2 in
  let isindex = (p = 1) in
  let isadd = (u = 1) in
  let iswback = (w = 1) || (p = 0) in
  let bit22 = (bit24_21 lsr 1) mod 2 in
  let get_imm32 imm4H imm4L = (imm4H lsl 4) + imm4L in

  match (bit22,bit20,bit6_5) with
  (* <cc><0>10000<rn><rt>< 0>1001<rt> *)   (* SWP *)
  | (0,0,0) when w = 0 && bit11_8 = 0 && bit6_5 = 0 ->
     let rnreg = get_arm_reg bit19_16 in
     let rt = arm_register_op (get_arm_reg bit15_12) in
     let rt2 = arm_register_op (get_arm_reg bit3_0) in
     let offset = ARMImmOffset 0 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* SWP<c> <Rt>, <Rt2>, [<Rn>] *)
     Swap (c, rt WR, rt2 WR, mem WR)

  (* <cc><0>pu0w0<rn><rt>< 0>1011<rm> *)   (* STRH-reg *)
  | (0,0,1) when bit11_8 = 0 ->
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let rnreg = get_arm_reg bit19_16 in
     let rmreg = get_arm_reg bit3_0 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = ARMIndexOffset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback WR in
     (* STRH{<c>} <Rt>, [<Rn>, +/-<Rm>]{!}          Pre-x : (index,wback) = (T,T/F)
      * STRH{<c>} <Rt>, [<Rn>], +/-<Rm>             Post-x: (index,wback) = (F,T) *)
     StoreRegisterHalfword (c,rt,rn,rm,mem)

  (* <cc><0>pu0w0<rn><rt>< 0>1101<rm> *)   (* LDRD-reg *)
  | (0,0,2) when bit11_8 = 0 ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let rt2 = arm_register_op (get_arm_reg (bit15_12 + 1)) WR in
     let rnreg = get_arm_reg bit19_16 in
     let rmreg = get_arm_reg bit3_0 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = ARMIndexOffset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRD{<c>} <Rt>, <Rt2>, [<Rn>, +/-<Rm>]{!}   Pre-x : (index,wback) = (T,T/F)
      * LDRD{<c>} <Rt>, <Rt2>, [<Rn>], +/-<Rm>      Post-x: (index,wback) = (F,T) *)
     LoadRegisterDual (c,rt,rt2,rn,rm,mem)

  (* <cc><0>pu0w0<rn><rt>< 0>1111<rm> *)   (* STRD-reg *)
  | (0,0,3) when bit11_8 = 0 ->
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let rt2 = arm_register_op (get_arm_reg (bit15_12 + 1)) RD in
     let rnreg = get_arm_reg bit19_16 in
     let rmreg = get_arm_reg bit3_0 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = ARMIndexOffset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback WR in
     (* STRD<c> <Rt>, <Rt2>, [<Rn>, +/-<Rm>]{!}     Pre-x : (index,wback) = (T,T/F)
      * STRD<c> <Rt>, <Rt2>, [<Rn>], +/-<Rm>        Post-x: (index,wback) = (F,T)  *)
     StoreRegisterDual (c,rt,rt2,rn,rm,mem)

  (* <cc><0>pu0w1<rn><rt>< 0>1011<rm> *)   (* LDRH-reg *)
  | (0,1,1) when bit11_8 = 0 ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let rnreg = get_arm_reg bit19_16 in
     let rmreg = get_arm_reg bit3_0 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = ARMIndexOffset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRH<c> <Rt>, [<Rn>, +/-<Rm>]{!}             Pre-x : (index,wback) = (T,T/F)
      * LDRH<c> <Rt>, [<Rn>], +/-<Rm>                Post-x: (index,wback) = (F,T)  *)
     LoadRegisterHalfword (c,rt,rn,rm,mem)

  (* <cc><0>pu0w1<rn><rt>< 0>1101<rm> *)   (* LDRSB *)
  | (0,1,2) when bit11_8 = 0 ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let rnreg = get_arm_reg bit19_16 in
     let rmreg = get_arm_reg bit3_0 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let rm = arm_register_op rmreg RD in
     let offset = ARMIndexOffset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRSB<c> <Rt>, [<Rn>,+/-<Rm>]{!}
      * LDRSB<c> <Rt>, [<Rn>],+/-<Rm> *)
     LoadRegisterSignedByte (c,rt,rn,rm,mem)

  (* <cc><0>10100<rn><rt>< 0>1001<rt> *)   (* SWPB *)
  | (1,0,0) when w = 0 && bit11_8 = 0 && bit6_5 = 0 ->
     let rnreg = get_arm_reg bit19_16 in
     let rt = arm_register_op (get_arm_reg bit15_12) in
     let rt2 = arm_register_op (get_arm_reg bit3_0) in
     let offset = ARMImmOffset 0 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* SWPB<c> <Rt>, <Rt2>, [<Rn>] *)
     SwapByte (c, rt WR, rt2 WR, mem WR)

  (* <cc><0>pu1w0<rn><rt><iH>1011<iL> *)   (* STRH-imm *)
  | (1,0,1) ->
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let rnreg = get_arm_reg bit19_16 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 bit11_8 bit3_0 in
     let imm = arm_immediate_op (immediate_from_int imm32) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback WR in
     (* STRH<c> <Rt>, [<Rn>{, #+/-<imm8>}]           Offset: (index,wback) = (T,F)
      * STRH<c> <Rt>, [<Rn>, #+/-<imm>]!             Pre-x : (index,wback) = (T,T)
      * STRH<c> <Rt>, [<Rn>], #+/-<imm>              Post-x: (index,wback) = (F,T) *)
     StoreRegisterHalfword (c,rt,rn,imm,mem)

  (* <cc><0>pu1w0<rn><rt><iH>1101<iL> *)   (* LDRD-imm *)
  (* <cc><0>1u1001111<rt><iH>1101<iL> *)   (* LDRD-lit *)
  | (1,0,2) ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let rt2 = arm_register_op (get_arm_reg (bit15_12 + 1)) WR in
     let rnreg = get_arm_reg bit19_16 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 bit11_8 bit3_0 in
     let imm = arm_immediate_op (immediate_from_int imm32) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRD<c> <Rt>, <Rt2>, [<Rn>{, #+/-<imm>}]     Offset: (index,wback) = (T,F)
      * LDRD<c> <Rt>, <Rt2>, [<Rn>, #+/-<imm>]!      Pre-x : (index,wback) = (T,T)
      * LDRD<c> <Rt>, <Rt2>, [<Rn>], #+/-<imm>       Post-x: (index,wback) = (F,T) *)
     LoadRegisterDual (c,rt,rt2,rn,imm,mem)

  (* <cc><0>pu1w0<rn><rt><iH>1111<iL> *)   (* STRD-imm *)
  | (1,0,3) ->
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let rt2 = arm_register_op (get_arm_reg (bit15_12 + 1)) RD in
     let rnreg = get_arm_reg bit19_16 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 bit11_8 bit3_0 in
     let imm = arm_immediate_op (immediate_from_int imm32) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* STRD<c> <Rt>, <Rt2>, [<Rn>{, #+/-<imm>}]     Offset: (index,wback) = (T,F)
      * STRD<c> <Rt>, <Rt2>, [<Rn>, #+/-<imm>]!      Pre-x : (index,wback) = (T,T)
      * STRD<c> <Rt>, <Rt2>, [<Rn>], #+/-<imm>       Post-x: (index,wback) = (F,T) *)
     StoreRegisterDual (c,rt,rt2,rn,imm,mem)

  (* <cc><0>pu1w1<rn><rt><iH>1011<iL> *)   (* LDRH-imm *)
  (* <cc><0>pu1w11111<rt><iH>1011<iL> *)   (* LDRH-lit *)
  | (1,1,1) ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let rnreg = get_arm_reg bit19_16 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 bit11_8 bit3_0 in
     let imm = arm_immediate_op (immediate_from_int imm32) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRH<c> <Rt>, [<Rn>{, #+/-<imm>}]            Offset: (index,wback) = (T,F)
      * LDRH<c> <Rt>, [<Rn>, #+/-<imm>]!             Pre-x : (index,wback) = (T,T)
      * LDRH<c> <Rt>, [<Rn>], #+/-<imm>              Post-x: (index,wback) = (F,T) *)
     LoadRegisterHalfword (c,rt,rn,imm,mem)

  (* <cc><0>pu1w1<rn><rt><iH>1101<iL> *)   (* LDRSB-imm *)
  | (1,1,2) ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let rnreg = get_arm_reg bit19_16 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 bit11_8 bit3_0 in
     let imm = arm_immediate_op (immediate_from_int imm32) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRSB<c> <Rt>, [<Rn>{, #+/-<imm8>}]
      * LDRSB<c> <Rt>, [<Rn>], #+/-<imm8>
      * LDRSB<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     LoadRegisterSignedByte (c,rt,rn,imm,mem)

  (* <cc><0>pu1w1<rn><rt><iH>1111<iL> *)   (* LDRSH-imm *)
  | (1,1,3) ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let rnreg = get_arm_reg bit19_16 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let imm32 = get_imm32 bit11_8 bit3_0 in
     let imm = arm_immediate_op (immediate_from_int imm32) in
     let offset = ARMImmOffset imm32 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback RD in
     (* LDRSH<c> <Rt>, [<Rn>{, #+/-<imm8>}]
      * LDRSH<c> <Rt>, [<Rn>], #+/-<imm8>
      * LDRSH<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     LoadRegisterSignedHalfword (c,rt,rn,imm,mem)

  | (k,l,m) ->
     NotRecognized
       (("data_proc_reg_load_stores ("
         ^ (stri k)
         ^ ", "
         ^ (stri l)
         ^ ", "
         ^ (stri m)
         ^ ")"),
        wordzero)


let parse_data_proc_reg_type
      (cond:int)
      (bit24_21:int)
      (bit20:int)
      (bit19_16:int)
      (bit15_12:int)
      (bit11_8:int)
      (bit7:int)
      (bit6_5:int)
      (bit4:int)
      (bit3_0:int) =
  let c = get_opcode_cc cond in
  let mk_imm5 b4 b1 = (b4 lsl 1) + b1 in
  let mk_imm_shift_reg r ty imm mode =
    mk_arm_imm_shifted_register_op (get_arm_reg r) ty imm mode in
  let mk_reg_shift_reg r ty reg mode =
    mk_arm_reg_shifted_register_op (get_arm_reg r) ty (get_arm_reg reg) mode in
  match bit24_21 with
  (* <cc><0>< 0>s<rd>< 0><rm>1001<rn> *)   (* MUL-reg *)
  | 0 when (bit15_12 = 0) && (bit7 = 1) && (bit6_5 = 0) && (bit4 = 1) -> 
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit19_16) RD in
     let rm = arm_register_op (get_arm_reg bit11_8) WR in
     let rn = arm_register_op (get_arm_reg bit3_0) RD in
     (* MUL{S}<c> <Rd>, <Rn>, <Rm> *)
     Multiply(s,c,rd,rn,rm)

  (* <cc><0>< 0>s<rn><rd><imm>ty0<rm> *)   (* AND-reg *)
  | 0 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* AND{S}<c> <Rd>, <Rn>{, <shift>} *)
     BitwiseAnd (s,c,rd,rn,rm)

  (* <cc><0>< 0>s<rn><rd><rs>0ty1<rm> *)   (* AND-reg-shifted *)
  | 0 when (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rm = mk_reg_shift_reg bit3_0 bit6_5 bit11_8 RD in
     (* AND{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     BitwiseAnd (s,c,rd,rn,rm)

  (* <cc><0>< 1>s<rd><ra><rm>1001<rn> *)   (* MLA     *)
  | 1 when (bit7 = 1) && (bit6_5 = 0) && (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit19_16) WR in
     let ra = arm_register_op (get_arm_reg bit15_12) RD in
     let rm = arm_register_op (get_arm_reg bit11_8) RD in
     let rn = arm_register_op (get_arm_reg bit3_0) RD in
     (* MLA{S}<c> <Rd>, <Rn>, <Rm>, <Ra> *)
     MultiplyAccumulate (s,c,rd,rn,rm,ra)

  (* <cc><0>< 1>s<rn><rd><imm>ty0<rm> *)   (* EOR-reg *)
  | 1 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* EOR{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseExclusiveOr (s,c,rd,rn,rm)

  (* <cc><0>< 1>s<rn><rd><rs>0ty1<rm> *)   (* EOR-reg-shifted *)
  | 1 when (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rm = mk_reg_shift_reg bit3_0 bit6_5 bit11_8 RD in
     (* EOR{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     BitwiseExclusiveOr (s,c,rd,rn,rm)

  (* cond0000010s<rn><rd><imm>ty0<rm> *)
  | 2 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* SUB{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     Subtract (s,c,rd,rn,rm,false)

  (* <cc><0>< 3>s<rn><rd><imm>ty0<rm> *)   (* RSB-reg *)
  | 3 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* RSB{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     ReverseSubtract(s,c,rd,rn,rm)

  (* <cc><0>< 3>s<rn><rd><rs>0ty1<rm> *)   (* RSB-reg-shifted *)
  | 3 when (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rm = mk_reg_shift_reg bit3_0 bit6_5 bit11_8 RD in
     (* RSB{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     ReverseSubtract(s, c, rd, rn, rm)

  (* <cc><0>< 4>s<rn><rd><imm>ty0<rm> *)   (* ADD-reg *)
  | 4 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* ADD{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     Add (s,c,rd,rn,rm,false)

  (* <cc><0>< 4>s<hi><lo><rm>1001<rn> *)   (* UMULL   *)
  | 4 when (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rdhi = arm_register_op (get_arm_reg bit19_16) WR in
     let rdlo = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit11_8) RD in
     let rn = arm_register_op (get_arm_reg bit3_0) RD in
     (* UMULL{S}<c> <RdLo>, <RdHi>, <Rn>, <Rm> *)
     UnsignedMultiplyLong (s,c,rdlo,rdhi,rn,rm)

  (* <cc><0>< 5>s<rn><rd><imm>ty0<rm> *)   (* ADC-reg *)
  | 5 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* ADC{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     AddCarry (s,c,rd,rn,rm,false)

  (* <cc><0>< 5>s<rn><rd><rs>0ty1<rm> *)   (* ADC-reg-shifted *)
  | 5 when (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rm = mk_reg_shift_reg bit3_0 bit6_5 bit11_8 RD in
     (* ADC{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     AddCarry (s,c,rd,rn,rm,false)

  (* <cc><0>< 6>s<rn><rd><imm>ty0<rm> *)   (* SBC-reg *)
  | 6 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* SBC{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     SubtractCarry (s,c,rd,rn,rm)

  (* <cc><0>< 6>s<hi><lo><rm>1001<rn> *)   (* SMULL *)
  | 6 when (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rdhi = arm_register_op (get_arm_reg bit19_16) WR in
     let rdlo = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit11_8) RD in
     let rn = arm_register_op (get_arm_reg bit3_0) RD in
     (* SMULL{S} <RdLo>, <RdHi>, <Rn>, <Rm> *)
     SignedMultiplyLong (s,c,rdlo,rdhi,rn,rm)

  (* <cc><0>< 8>1<rn>0000<imm>ty0<rm> *)   (* TST-reg *)
  | 8 when (bit20 = 1) && (bit4 = 0) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* TST<c> <Rn>, <Rm>{, <shift>} *)
     Test (c,rn,rm)

  (* <cc><0>< 9>0<15><15><15>0001<rm> *)   (* BX      *)
  | 9 when
         (bit20 = 0)
         && (bit19_16 = 15)
         && (bit15_12 = 15)
         && (bit11_8 = 15)
         && (bit7 = 0)
         && (bit6_5 = 0)
         && (bit4 = 1) ->
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     (* BX<c> <Rm> *)
     BranchExchange(c,rm)

  (* <cc><0>< 9>0<15><15><15>0011<rm> *)   (* BLX-reg *)
  | 9 when
         (bit20 = 0)
         && (bit19_16 = 15)
         && (bit15_12 = 15)
         && (bit11_8 = 15)
         && (bit7 = 0)
         && (bit6_5 = 1)
         && (bit4 = 1) ->
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     (* BLX<c> <Rm> *)
     BranchLinkExchange(c,rm)

  (* <cc><0>< 9>1<rn>< 0><imm>ty0<rm> *)   (* TEQ-reg *)
  | 9 when (bit20 = 1) && (bit4 = 0) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* TEQ<c> <Rn>, <Rm>{, <shift>} *)
     TestEquivalence (c,rn,rm)

  (* <cc><0><10>1<rn>< 0><imm>ty0<rm> *)   (* CMP-reg *)
  | 10 when (bit20 = 1) && (bit4 = 0) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* CMP<c> <Rn>, <Rm>{, <shift>} *)
     Compare (c,rn,rm,false)

  (* <cc><0><10>1<rn>< 0><rs>0ty1<rm> *)   (* CMP-reg-shifted *)
  | 10 when (bit20 = 1) && (bit4 = 1) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rm = mk_reg_shift_reg bit3_0 bit6_5 bit11_8 RD in
     (* CMP<c> <Rn>, <Rm>, <type> <Rs> *)
     Compare (c,rn,rm,false)

  (* <cc><0><11>0<15><rd><15>0001<rm> *)   (* CLZ     *)
  | 11 when
         (bit20 = 0)
         && (bit19_16 = 15)
         && (bit11_8 = 15)
         && (bit7 = 0)
         && (bit6_5 = 0)
         && (bit4 = 1) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     (* CLZ<c> <Rd>, <Rm> *)
     CountLeadingZeros (c,rd,rm)

  (* <cc><0><11>1<rn>< 0><imm>ty0<rm> *)   (* CMN-reg *)
  | 11 when (bit20 = 1) && (bit4 = 0) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* CMM<c> <Rn>, <Rm>{, <shift>} *)
     CompareNegative (c,rn,rm)

  (* <cc><0><12>s<rn><rd><rs>0ty1<rm> *)   (* ORR-reg-shifted *)
  | 12 when (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rm = mk_reg_shift_reg bit3_0 bit6_5 bit11_8 RD in
     (* ORR{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     BitwiseOr (s,c,rd,rn,rm)

  (* <cc><0><12>s<rn><rd><imm>ty0<rm> *)   (* ORR-reg *)
  | 12 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* ORR{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseOr (s,c,rd,rn,rm)

  (* <cc><0><13>s< 0><rd>< 0>0000<rm> *)   (* MOV-reg *)
  | 13 when
         (bit19_16 = 0)
         && (bit11_8 = 0)
         && (bit7 = 0)
         && (bit6_5 = 0)
         && (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     (* MOV{S}<c> <Rd>, <Rm> *)
     Move (s, c, rd, rm, false)

  (* <cc><0><13>s< 0><rd><imm>000<rm> *)   (* LSL-imm *)
  | 13 when (bit19_16 = 0) && (bit6_5 = 0) && (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let (_,imm) = decode_imm_shift 0 imm5 in
     let imm = mk_arm_immediate_op false 4 (mkNumerical imm) in
     (* LSL{S}<c> <Rd>, <Rm>, #<imm> *)
     LogicalShiftLeft (s,c,rd,rm,imm,false)

  (* <cc><0><13>s< 0><rd><rm>0001<rn> *)   (* LSL-reg *)
  |13 when (bit19_16 = 0) && (bit7 = 0) && (bit6_5 = 0) && (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit11_8) RD in
     let rn = arm_register_op (get_arm_reg bit3_0) RD in
     (* LSL{S}<c> <Rd>, <Rn>, <Rm> *)
     LogicalShiftLeft (s,c,rd,rn,rm,false)

  (* <cc><0><13>s< 0><rd><imm>010<rm> *)   (* LSR-imm *)
  | 13 when (bit19_16 = 0) && (bit6_5 = 1) && (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let (_,imm) = decode_imm_shift 1 imm5 in
     let imm = mk_arm_immediate_op false 4 (mkNumerical imm) in
     (* LSR{S}<c> <Rd>, <Rm>, #<imm> *)
     LogicalShiftRight (s,c,rd,rm,imm)

  (* <cc><0><13>s< 0><rd><rm>0011<rn> *)   (* LSR-reg *)
  | 13 when (bit19_16 = 0) && (bit7 = 0) && (bit6_5 = 1) && (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit11_8) RD in
     let rn = arm_register_op (get_arm_reg bit3_0) RD in
     (* LSR{S}<c> <Rd>, <Rn>, <Rm> *)
     LogicalShiftRight (s,c,rd,rn,rm)

  (* <cc><0><13>s< 0><rd><imm>100<rm> *)   (* ASR-imm *)
  | 13 when (bit19_16 = 0) && (bit6_5 = 2) && (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let (_,imm) = decode_imm_shift 2 imm5 in
     let imm = mk_arm_immediate_op false 4 (mkNumerical imm) in
     (* ASR{S}<c> <Rd>, <Rm>, #<imm> *)
     ArithmeticShiftRight (s,c,rd,rm,imm)

  (* <cc><0><13>s< 0><rd><rm>0101<rn> *)   (* ASR-reg *)
  | 13 when (bit19_16 = 0) && (bit7 = 0) && (bit6_5 = 2) && (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit11_8) RD in
     let rn = arm_register_op (get_arm_reg bit3_0) RD in
     (* ASR{S}<c> <Rd>, <Rn>, <Rm> *)
     ArithmeticShiftRight (s,c,rd,rn,rm)

  (* <cc><0><13>s< 0><rd>< 0>0110<rm> *)   (* RRX *)
  | 13 when (bit19_16 = 0)
            && (bit11_8 = 0)
            && (bit7 = 0)
            && (bit6_5 = 3)
            && (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     (* RRX{S}<c> <Rd>, <Rm> *)
     RotateRightExtend (s,c,rd,rm)

  (* <cc><0><13>s< 0><rd><imm>110<rm> *)
  | 13 when (bit19_16 = 0) && (bit6_5 = 3) && (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let (_,imm) = decode_imm_shift 2 imm5 in
     let imm = mk_arm_immediate_op false 4 (mkNumerical imm) in
     (* ROR{S}<c> <Rd>, <Rm>, #<imm> *)
     RotateRight (s, c, rd, rm, imm)

  (* <cc><0><14>s<rn><rd><imm>ty0<rm> *)   (* BIC-reg *)
  | 14 when (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg 15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* BIC{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseBitClear (s,c,rd,rn,rm)

  (* <cc><0><14>s<rn><rd><rs>0ty1<rm> *)   (* BIC-reg-shifted *)
  | 14 when (bit4 = 1) && (bit7 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rm = mk_reg_shift_reg bit3_0 bit6_5 bit11_8 RD in
     (* BIC{S}<c> <Rd>, <Rn>, <Rm>, <type> <Rs> *)
     BitwiseBitClear (s,c,rd,rn,rm)

  (* <cc><0><15>s< 0><rd><imm>ty0<rm> *)   (* MVN-reg *)
  | 15 when (bit19_16 = 0) && (bit4 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm5 = mk_imm5 bit11_8 bit7 in
     let rm = mk_imm_shift_reg bit3_0 bit6_5 imm5 RD in
     (* MVN{S}<c> <Rd>, <Rm>{, <shift>} *)
     BitwiseNot (s,c,rd,rm)

  (* <cc><0><15>s< 0><rd><rs>0ty1<rm> *)   (* MVN-reg-shifted *)
  | 15 when (bit19_16 = 0) && (bit4 = 1) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = mk_reg_shift_reg bit3_0 bit6_5 bit11_8 RD in
     (* MVN{S}<c> <Rd>, <Rm>, <type> <Rs> *)
     BitwiseNot (s,c,rd,rm)

  (* <cc><0>.................1..1.... *)
  | _ when (bit7 = 1) && (bit4 = 1) ->
     parse_data_proc_reg_load_stores
       c bit24_21 bit20 bit19_16 bit15_12 bit11_8 bit6_5 bit3_0

  | tag ->
     NotRecognized ("data_proc_reg_type:" ^ (stri tag), wordzero)

let parse_data_proc_imm_type
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (cond:int)
      (bit24_21:int)
      (bit20:int)
      (bit19_16:int)
      (bit15_12:int)
      (bit11_8:int)
      (bit7_0:int) =
  let c = get_opcode_cc cond in
  let mk_imm rotate imm =
    let imm32 = arm_expand_imm rotate imm in
    let imm32 = make_immediate false 4 (B.big_int_of_int imm32) in
    arm_immediate_op imm32 in
  let mk_imm16 imm4 rotate imm = (imm4 lsl 12) + (rotate lsl 8) + imm in
  match bit24_21 with
  (* <cc><1>< 0>s<rn><rd><--imm12---> *)   (* AND-imm *)
  | 0 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* AND{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseAnd (s,c,rd,rn,imm)

  (* <cc><1>< 1>s<rn><rd><--imm12---> *)   (* EOR-imm *)
  | 1 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* EOR{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseExclusiveOr (s,c,rd,rn,imm)

  (* <cc><1>< 2>s<rn><rd><--imm12---> *)   (* SUB-imm *)
  | 2 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* SUB{S}<c> <Rd>, <Rn>, #<const> *)
     Subtract (s,c,rd,rn,imm,false)

  (* <cc><1>< 3>s<rn><rd><--imm12---> *)   (* RSC-imm *)
  | 3 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* RSB{S}<c> <Rd>, <Rn>, #<const> *)
     ReverseSubtract (s,c,rd,rn,imm)

  (* <cc><1>< 4>0<15><rd><--imm12---> *)   (* ADR     *)
  | 4 when (bit20 = 0) && (bit19_16 = 15) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm32 = arm_expand_imm bit11_8 bit7_0 in
     let imm = mk_arm_absolute_target_op ch base imm32 RD in
     Adr (c,rd,imm)

  (* <cc><1>< 4>s<rn><rd><--imm12---> *)   (* ADD-imm *)
  | 4 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* ADD{S}<c> <Rd>, <Rn>, #<const> *)
     Add (s,c,rd,rn,imm,false)

  (* <cc><1>< 5>s<rn><rd><--imm12---> *)   (* ADC-imm *)
  | 5 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* ADC{S}<c> <Rd>, <Rn>, #<const> *)
     AddCarry (s,c,rd,rn,imm,false)

  (* <cc><1>< 6>s<rn><rd><--imm12---> *)   (* SBC-imm *)
  | 6 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* SBC{S}<c> <Rd>, <Rn>, #<const> *)
     SubtractCarry (s,c,rd,rn,imm)

  (* <cc><1>< 7>s<rn><rd><--imm12---> *)   (* RSC-imm *)
  | 7 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* RSC{S}<c> <Rd>, <Rn>, #<const> *)
     ReverseSubtractCarry (s,c,rd,rn,imm)

  (* <cc><1>< 8>0<i4><rd><--imm12---> *)   (* MOVW-imm *)
  | 8 when (bit20 = 0) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let immval = (bit19_16 lsl 12) + (bit11_8 lsl 8) + bit7_0 in
     let imm32 = make_immediate false 4 (B.big_int_of_int immval) in
     let imm = arm_immediate_op imm32 in
     (* MOVW<c> <Rd>, #<imm16> *)
     MoveWide (c,rd,imm)

  (* <cc><1>< 8>1<rn>< 0><--imm12---> *)   (* TST-imm *)
  | 8 when (bit20 = 1) && (bit15_12 = 0) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* TST<c> <Rn>, #<const> *)
     Test (c,rn,imm)

  (* <cc><1>< 9>1<rn>< 0><--imm12---> *)   (* TEQ-imm *)
  | 9 when (bit20 = 1) && (bit15_12 = 0) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* TEQ<c> <Rn>, #<const> *)
     TestEquivalence (c,rn,imm)

  (* <cc><1>< 9>0< 0><15>< 0>< 0>< 0> *)   (* NOP *)
  | 9 when (bit20 = 0)
           && (bit19_16 = 0)
           && (bit15_12 = 15)
           && (bit11_8) = 0
           && (bit7_0 = 0) ->
     (* NOP<c> *)
     NoOperation c

  (* <cc><1><10>0<i4><rd><--imm12---> *)   (* MOVT    *)
  | 10 when (bit20 = 0) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm16 = mk_imm16 bit19_16 bit11_8 bit7_0 in
     let imm16 = make_immediate false 2 (B.big_int_of_int imm16) in
     let imm = arm_immediate_op imm16 in
     (* MOVT<c> <Rd>, #<imm16> *)
     MoveTop (c,rd,imm)

  (* <cc><1><10>1<rn>< 0><--imm12---> *)   (* CMP-imm *)
  | 10 when (bit20 = 1) && (bit15_12 = 0) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* CMP<c> <Rn>, #<const> *)
     Compare (c,rn,imm,false)

  (* <cc><1><11>1<rn>< 0><--imm12---> *)   (* CMN-imm *)
  | 11 when (bit20 = 1) && (bit15_12 = 0) ->
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let imm = mk_imm bit11_8 bit7_0 in
     (* CMN<c> <Rn>, #<const> *)
     CompareNegative (c,rn,imm)

  (* <cc><1><12>s<rn><rd><--imm12---> *)   (* ORR-imm *)
  | 12 ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm = mk_imm bit11_8 bit7_0 in
     (* ORR{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseOr (s,c,rd,rn,imm)

  (* <cc><1><13>s< 0><rd><--imm12---> *)   (* MOV-imm *)
  | 13 ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm = mk_imm bit11_8 bit7_0 in
     (* MOV{S}<c> <Rd>, #<const> *)
     Move (s, c, rd, imm, false)

  (* <cc><1><14>s<rn><rd><--imm12---> *)   (* BIC-imm *)
  | 14 ->
     let s = (bit20 = 1) in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm = mk_imm bit11_8 bit7_0 in
     (* BIC{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseBitClear (s,c,rd,rn,imm)

  (* <cc><1><15>s< 0><rd><--imm12---> *)   (* MVN-imm *)
  | 15 when (bit19_16 = 0) ->
     let s = (bit20 = 1) in
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let imm = mk_imm bit11_8 bit7_0 in
     (* MVN{S}<c> <Rd>, #<const> *)
     BitwiseNot (s,c,rd,imm)

  | tag ->
     NotRecognized ("data_proc_imm_type:" ^ (stri tag), wordzero)


let parse_load_store_stack
      (c:arm_opcode_cc_t)
      (bit24:int)
      (bit23:int)
      (bit21:int)
      (bit20:int)
      (bit15_12:int) =
  (* <cc><2>..0..<13>................ *)   (* stack *)
  let sp = arm_register_op (get_arm_reg 13) RW in
  match (bit24, bit23, bit21, bit20) with
  (* <cc><2>10010<13><rt><-imm12:4--> *)   (* PUSH *)
  | (1,0,1,0) ->
     let rl = arm_register_list_op [ (get_arm_reg bit15_12) ] RD in
     (* PUSH<c> <registers> *)
     Push (c,sp,rl,false)

  (* <cc><2>01001<13><rt><-imm12:4--> *)   (* POP *)
  | (0,1,0,1) ->
     let rl = arm_register_list_op [ (get_arm_reg bit15_12) ] WR in
     (* POP<c> <registers> *)
     Pop (c,sp,rl,false)

  (* <cc><2>pu0w0<13><rt><-imm12:4--> *)   (* STR-imm *)
  | (_,_,_,0) ->
     let p = (bit24 = 1) in
     let u = (bit23 = 1) in
     let w = (bit21 = 1) in
     let isadd = u in
     let iswback = (not p) || w in
     let isindex = p in
     let rnreg = get_arm_reg 13 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let offset = ARMImmOffset 4 in
     let mk_mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let mem = mk_mem WR in
     (* STR<c> <Rt>, [<Rn>{, #+/-<imm12>}]       Offset: (index,wback) = (T,F)
      * STR<c> <Rt>, [<Rn>, #+/-<imm12>]!        Pre-x : (index,wback) = (T,T)
      * STR<c> <Rt>, [<Rn>], #+/-<imm12>         Post-x: (index,wback) = (F,T) *)
     StoreRegister (c,rt,rn,mem,false)

  (* <cc><2>pu0w1<13><rt><-imm12:4--> *)   (* LDR-imm *)
  | (_,_,_,1) ->
     let p = (bit24 = 1) in
     let u = (bit23 = 1) in
     let w = (bit21 = 1) in
     let isadd = u in
     let iswback = (not p) || w in
     let isindex = p in
     let rnreg = get_arm_reg 13 in
     let rn = arm_register_op rnreg (if iswback then RW else RD) in
     let offset = ARMImmOffset 4 in
     let mk_mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let mem = mk_mem RD in
     (* LDR<c> <Rt>, [<Rn>{, #+/-<imm12>}]           Offset: (index,wback) = (T,F)
      * LDR<c> <Rt>, [<Rn>, #+/-<imm12>]!            Pre-x : (index,wback) = (T,T)
      * LDR<c> <Rt>, [<Rn>], #+/-<imm12>             Post-x: (index,wback) = (F,T)  *)
     LoadRegister (c,rt,rn,mem, false)

  | (k,l,m,n) ->
     NotRecognized
       ("load_store_stack ("
        ^ (stri k)
        ^ ", "
        ^ (stri l)
        ^ ", "
        ^ (stri m)
        ^ ", "
        ^ (stri n)
        ^ ")",
        wordzero)

let parse_load_stores
      (c:arm_opcode_cc_t)
      (bit24:int)
      (bit23:int)
      (bit22:int)
      (bit21:int)
      (bit20:int)
      (bit19_16:int)
      (bit15_12:int)
      (bit11_0:int) =
  let p = (bit24 = 1) in
  let u = (bit23 = 1) in
  let w = (bit21 = 1) in
  let isadd = u in
  let iswback = (not p) || w in
  let isindex = p in
  let rnreg = get_arm_reg bit19_16 in
  let rn = arm_register_op rnreg (if iswback then RW else RD) in
  let offset = ARMImmOffset bit11_0 in
  let mk_mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
  match (bit22, bit20) with
  (* <cc><2>pu0w0<rn><rt><--imm12---> *)   (* STR-imm *)
  | (0,0) ->
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let mem = mk_mem WR in
     (* STR<c> <Rt>, [<Rn>{, #+/-<imm12>}]       Offset: (index,wback) = (T,F)
      * STR<c> <Rt>, [<Rn>, #+/-<imm12>]!        Pre-x : (index,wback) = (T,T)
      * STR<c> <Rt>, [<Rn>], #+/-<imm12>         Post-x: (index,wback) = (F,T) *)
     StoreRegister (c,rt,rn,mem,false)

  (* <cc><2>pu0w1<rn><rt><--imm12---> *)   (* LDR-imm *)
  | (0,1) ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let mem = mk_mem RD in
     (* LDR<c> <Rt>, [<Rn>{, #+/-<imm12>}]           Offset: (index,wback) = (T,F)
      * LDR<c> <Rt>, [<Rn>, #+/-<imm12>]!            Pre-x : (index,wback) = (T,T)
      * LDR<c> <Rt>, [<Rn>], #+/-<imm12>             Post-x: (index,wback) = (F,T)  *)
     LoadRegister (c,rt,rn,mem,false)

  (* <cc><2>pu1w0<rn><rt><--imm12---> *)   (* STRB-imm *)
  | (1,0) ->
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let mem = mk_mem WR in
     (* STRB<c> <Rt>, [<Rn>{, #+/-<imm12>}]       Offset: (index,wback) = (T,F)
      * STRB<c> <Rt>, [<Rn>, #+/-<imm12>]!        Pre-x : (index,wback) = (T,T)
      * STRB<c> <Rt>, [<Rn>], #+/-<imm12>         Post-x: (index,wback) = (F,T) *)
     StoreRegisterByte (c,rt,rn,mem)

  (* <cc><2>pu1w1<rn><rt><--imm12---> *)   (* LDRB-imm *)
  | (1,1) ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let mem = mk_mem RD in
     (* LDRB<c> <Rt>, [<Rn>{, #+/-<imm12>}]          Offset: (index,wback) = (T,F)
      * LDRB<c> <Rt>, [<Rn>, #+/-<imm12>]!           Pre-x : (index,wback) = (T,T)
      * LDRB<c> <Rt>, [<Rn>], #+/-<imm12>            Post-x: (index,wback) = (F,T)  *)
     LoadRegisterByte (c,rt,rn,mem,false)

  | (k,l) ->
     NotRecognized ("load_stores (" ^ (stri k) ^ ", " ^ (stri l) ^ ")", wordzero)


let parse_load_store_imm_type
      (cond:int)
      (bit24:int)
      (bit23:int)
      (bit22:int)
      (bit21:int)
      (bit20:int)
      (bit19_16:int)
      (bit15_12:int)
      (bit11_0:int) =
  let c = get_opcode_cc cond in
  match bit19_16 with
  (* <cc><2>..0..<13>................ *)   (* stack *)
  | 13 when (bit22 = 0) && (bit11_0 = 4) ->
     parse_load_store_stack c bit24 bit23 bit21 bit20 bit15_12

  | _ ->
     parse_load_stores c bit24 bit23 bit22 bit21 bit20 bit19_16 bit15_12 bit11_0


let parse_load_store_reg_type
      (cond:int)
      (bit24:int)
      (bit23:int)
      (bit22:int)
      (bit21:int)
      (bit20:int)
      (bit19_16:int)
      (bit15_12:int)
      (bit11_7:int)
      (bit6_5:int)
      (bit4:int)
      (bit3_0:int) =
  let c = get_opcode_cc cond in
  let p = (bit24 = 1) in
  let u = (bit23 = 1) in
  let w = (bit21 = 1) in
  let isadd = u in
  let iswback = (not p) || w in
  let isindex = p in
  let rnreg = get_arm_reg bit19_16 in
  let rn = arm_register_op rnreg (if iswback then RW else RD) in
  let (shift_t,shift_n) = decode_imm_shift bit6_5 bit11_7 in
  let reg_srt = ARMImmSRT (shift_t,shift_n) in
  let offset = ARMShiftedIndexOffset (get_arm_reg bit3_0,reg_srt) in
  let mk_mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
  match (bit22,bit20) with
  (* <cc><3>pu0w0<rn><rt><imm>ty0<rm> *)   (* STR-reg *)
  | (0,0) ->
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let mem = mk_mem WR in
     (* STR<c> <Rt>, [<Rn>,+/-<Rm>{, <shift>}]{!} *)
     (* STR<c> <Rt>, [<Rn>],+/-<Rm>{, <shift>} *)
     StoreRegister (c,rt,rn,mem,false)

  (* <cc><3>pu0w1<rn><rt><imm>ty0<rm> *)   (* LDR-reg *)
  | (0,1) ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let mem = mk_mem RD in
     (* LDR<c> <Rt>, [<Rn>,+/-<Rm>{, <shift>}[{!} *)
     (* LDR<c> <Rt>, [<Rn>],+/-<Rm>{, <shift>} *)
     LoadRegister (c,rt,rn,mem,false)

  (* <cc><3>pu1w0<rn><rt><imm>ty0<rm> *)   (* STRB-reg *)
  | (1,0) ->
     let rt = arm_register_op (get_arm_reg bit15_12) RD in
     let mem = mk_mem WR in
     (* STRB<c> <Rt>, [<Rn>,+/-<Rm>{, <shift>}]{!} *)
     (* STRB<c> <Rt>, [<Rn>],+/-<Rm>{, <shift>} *)
     StoreRegisterByte (c,rt,rn,mem)

  (* <cc><3>pu1w1<rn><rt><imm>ty0<rm> *)   (* LDRB-reg *)
  | (1,1) ->
     let rt = arm_register_op (get_arm_reg bit15_12) WR in
     let mem = mk_mem RD in
     LoadRegisterByte (c,rt,rn,mem,false)

  | _ -> OpInvalid


let parse_media_type
      (cond:int)
      (bit24_20:int)
      (bit19_16:int)
      (bit15_12:int)
      (bit11_8:int)
      (bit7_5:int)
      (bit3_0:int) =
  let c = get_opcode_cc cond in
  let bit9_8 = bit11_8 mod 4 in
  let bit11_10 = bit11_8 lsr 2 in
  match bit24_20 with
  (* <cc><3>< 10><15><rd>ro000111<rm> *)   (* SXTB *)
  | 10 when (bit19_16 = 15) && (bit9_8 = 0) && (bit7_5 = 3) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rotation = bit11_10 lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg bit3_0) rotation RD in
     (* SXTB<c> <Rd>, <Rm>{, <rotation>} *)
     SignedExtendByte (c,rd,rm)

  (* <cc><3>< 11><15><rd><15>0011<rm> *)   (* REV *)
  | 11 when (bit19_16 = 15) && (bit11_8 = 15) && (bit7_5 = 1) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rm = arm_register_op (get_arm_reg bit3_0) RD in
     (* REV<c> <Rd>, <Rm> *)
     ByteReverseWord (c,rd,rm)

  (* <cc><3>< 11><15><rd>ro000111<rm> *)   (* SXTH *)
  | 11 when (bit19_16 = 15) && (bit9_8 = 0) && (bit7_5 = 3) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rotation = bit11_10 lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg bit3_0) rotation RD in
     (* SXTH<c> <Rd>, <Rm>{, <rotation>} *)
     SignedExtendHalfword (c,rd,rm)

  (* <cc><3>< 14><15><rd>ro000111<rm> *)   (* UXTB   *)
  | 14 when (bit19_16 = 15) && (bit9_8 = 0) && (bit7_5 = 3) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rotation = bit11_10 lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg bit3_0) rotation RD in
     (* UXTB<c> <Rd>, <Rm>{, <rotation>} *)
     UnsignedExtendByte (c,rd,rm)

  (* <cc><3>< 15><15><rd>ro000111<rm> *)   (* UXTH   *)
  | 15 when (bit19_16 = 15) && (bit9_8 = 0) && (bit7_5 = 3) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rotation = bit11_10 lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg bit3_0) rotation RD in
     (* UXTH<c> <Rd>, <Rm>{, <rotation>} *)
     UnsignedExtendHalfword (c,rd,rm)

  (* <cc><3>< 15><rn><rd>ro000111<rm> *)   (* UXTAH  *)
  | 15 when (bit9_8 = 0) && (bit7_5 = 3) ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let rn = arm_register_op (get_arm_reg bit19_16) RD in
     let rotation = bit11_10 lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg bit3_0) rotation RD in
     (* UXTAH<c> <Rd>, <Rn>, <Rm>{, <rotation>} *)
     UnsignedExtendAddHalfword (c,rd,rn,rm)

  (* <cc><3><13><wm1><rd><lsb>101<rn> *)   (* SBFX   *)
  | 26 | 27 when (bit7_5 mod 4) = 2 ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let lsb = (bit11_8 lsl 1) + (bit7_5 lsr 2) in
     let widthm1 = ((bit24_20 mod 2) lsl 4) + bit19_16 in
     let rn = mk_arm_reg_bit_sequence_op (get_arm_reg bit3_0) lsb widthm1 RD in
     (* SBFX<c> <Rd>, <Rn>, #<lsb>, #<width> *)
     SingleBitFieldExtract (c,rd,rn)

  (* <cc><3><15><wm1><rd><lsb>101<rn> *)   (* UBFX   *)
  | 30 | 31 when (bit7_5 mod 4) = 2 ->
     let rd = arm_register_op (get_arm_reg bit15_12) WR in
     let lsb = (bit11_8 lsl 1) + (bit7_5 lsr 2) in
     let widthm1 = ((bit24_20 mod 2) lsl 4) + bit19_16 in
     let rn = mk_arm_reg_bit_sequence_op (get_arm_reg bit3_0) lsb widthm1 RD in
     (* UBFX<c> <Rd>, <Rn>, #<lsb>, #<width> *)
     UnsignedBitFieldExtract (c,rd,rn)

  | tag ->
     NotRecognized ("media_type:" ^ (stri tag), wordzero)

let parse_block_data_stack
      (c:arm_opcode_cc_t)
      (bit24:int)
      (bit23:int)
      (bit20:int)
      (bit15:int)
      (bit14_0:int) =
  let sp = arm_register_op (get_arm_reg 13) RW in
  let rl = get_reglist_from_int 16 bit14_0 in
  let rl = if bit15=1 then rl @ [ ARPC ] else rl in
  match (bit24,bit23,bit20) with
  (* <cc><4>01011<13><register-list-> *)   (* POP *)
  | (0,1,1) ->
     let rl = arm_register_list_op rl WR in
     (* POP<c> <registers> *)
     Pop (c,sp,rl,false)

  (* <cc><4>10010<13><register-list-> *)   (* PUSH *)
  | (1,0,0) ->
     let rl = arm_register_list_op rl RD in
     (* PUSH<c> <registers> *)
     Push (c,sp,rl,false)

  | (k,l,m) ->
     NotRecognized (
         "block_data_stack ("
         ^ (stri k)
         ^ ", "
         ^ (stri l)
         ^ ", "
         ^ (stri m)
         ^ ")",
         wordzero)

let parse_load_store_multiple
      (c:arm_opcode_cc_t)
      (bit24:int)
      (bit23:int)
      (bit21:int)
      (bit20:int)
      (bit19_16:int)
      (bit15:int)
      (bit14_0:int) =
  (* <cc><4>..0w.<rn><register-list-> *)   (* load/store multiple *)
  let iswback = (bit21 = 1) in
  let rnreg = get_arm_reg bit19_16 in
  let rn = arm_register_op rnreg (if iswback then RW else RD) in
  let rl = get_reglist_from_int 16 bit14_0 in
  let rl = if bit15=1 then rl @ [ ARPC ] else rl in

  match (bit24,bit23,bit20) with
  (* >cc><4>000w1<rn><register-list-> *)   (* LDMDA/LDMFA *)
  | (0,0,1) ->
     let rlop = arm_register_list_op rl WR in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) RD in
     LoadMultipleDecrementAfter (iswback,c,rn,rlop,mmem)

  (* <cc><4>010w0<rn><register-list-> *)   (* STM *)
  | (0,1,0) ->
     let rlop = arm_register_list_op rl RD in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) WR in
     StoreMultipleIncrementAfter (iswback,c,rn,rlop,mmem)

  (* <cc><4>010w1<rn><register-list-> *)   (* LDM *)
  | (0,1,1) ->
     let rlop = arm_register_list_op rl WR in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) RD in
     LoadMultipleIncrementAfter (iswback,c,rn,rlop,mmem)

  (* <cc><4>100w0<rn><register-list-> *)   (* STMDB (STMFD) *)
  | (1,0,0) ->
     let rlop = arm_register_list_op rl RD in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) WR in
     (* STMDB<c> <Rn>{!}, <registers> *)
     StoreMultipleDecrementBefore (iswback,c,rn,rlop,mmem)

  (* <cc><4>100w1<rn><register-list-> *)   (* LDMDB (LDMEA) *)
  | (1,0,1) ->
     let rlop = arm_register_list_op rl WR in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) RD in
     LoadMultipleDecrementBefore (iswback,c,rn,rlop,mmem)

  (* <cc><4>110w0<rn><register-list-> *)   (* STMIB (STMFA) *)
  | (1,1,0) ->
     let rlop = arm_register_list_op rl RD in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) WR in
     (* STMIB<c> <Rn>{!}, <registers> *)
     StoreMultipleIncrementBefore (iswback,c,rn,rlop,mmem)

  (* <cc><4>110w1<rn><register-list-> *)   (* LDMIB (LDMED) *)
  | (1,1,1) ->
     let rlop = arm_register_list_op rl WR in
     let mmem = mk_arm_mem_multiple_op rnreg (List.length rl) RD in
     LoadMultipleIncrementBefore (iswback,c,rn,rlop,mmem)

  | (k,l,m) ->
     NotRecognized (
         "load_store_multiple ("
         ^ (stri k)
         ^ ", "
         ^ (stri l)
         ^ ", "
         ^ (stri m)
         ^ ")",
         wordzero)

let parse_block_data_type
      (cond:int)
      (bit24:int)
      (bit23:int)
      (bit22:int)
      (bit21:int)
      (bit20:int)
      (bit19_16:int)
      (bit15:int)
      (bit14_0:int) =
  let c = get_opcode_cc cond in
  match bit19_16 with
  (* <cc><4>..01.<13><register-list-> *)   (* stack *)
  | 13 when (bit22=0) && (bit21=1) ->
     parse_block_data_stack c bit24 bit23 bit20 bit15 bit14_0

  | _ when (bit22 = 0) ->
     parse_load_store_multiple c bit24 bit23 bit21 bit20 bit19_16 bit15 bit14_0

  | tag ->
     NotRecognized ("block_data_type:" ^ (stri tag), wordzero)
     

let parse_branch_link_type
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (cond:int)
      (opx:int)
      (offset:int) =
  let cond = get_opcode_cc cond in
  let imm32 = sign_extend 32 26 (offset lsl 2) in
  let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
  let tgt = (base#add_int (ch#pos + 4))#add_int imm32 in
  let tgtop = arm_absolute_op tgt RD in
  if opx = 0 then
    Branch (cond, tgtop, false)
  else
    BranchLink (cond,tgtop)

let parse_opcode
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (instrbytes:doubleword_int):arm_opcode_t =
  let p = numerical_to_doubleword (mkNumerical ch#pos) in
  let addr = (base#add p)#add_int (-4) in
  let instr = decompose_arm_instr instrbytes in
  let opcode =
    match instr with
    | DataProcRegType (cond,op,opx,rn,rd,rs,opy,shift,reg,rm) ->
       parse_data_proc_reg_type cond op opx rn rd rs opy shift reg rm
    | DataProcImmType (cond,op,opx,rn,rd,rotate,imm) ->
       parse_data_proc_imm_type ch base cond op opx rn rd rotate imm
    | LoadStoreImmType (cond,p,u,opx,w,opy,rn,rd,imm) ->
       parse_load_store_imm_type cond p u opx w opy rn rd imm
    | LoadStoreRegType (cond,p,u,opx,w,opy,rn,rd,shiftimm,shift,opz,rm) ->
       parse_load_store_reg_type cond p u opx w opy rn rd shiftimm shift opz rm
    | MediaType (cond,op1,data1,rd,data2,op2,rn) ->
       parse_media_type cond op1 data1 rd data2 op2 rn
    | BlockDataType (cond,p,u,opx,w,opy,rn,opz,reglist) ->
       parse_block_data_type cond p u opx w opy rn opz reglist
    | BranchLinkType (cond,opx,offset) ->
       parse_branch_link_type ch base cond opx offset
    | _ -> OpInvalid in
  let pinstrclass =
    if system_settings#is_verbose
       && (match opcode with OpInvalid -> true | _ -> false) then
      LBLOCK [ STR " ("; STR (arm_instr_class_to_string instr); STR ")" ]
    else
      STR "" in
  begin
    (if system_settings#is_verbose then
       pr_debug [ addr#toPretty ; STR "  " ; STR (arm_opcode_to_string opcode) ;
                  pinstrclass ; NL ]);
    opcode
  end

let disassemble_arm_instruction
      (ch:pushback_stream_int) (base:doubleword_int) (instrbytes:doubleword_int) =
  try
    parse_opcode ch base instrbytes
  with
  | IO.No_more_input ->
     let address = base#add_int ch#pos in
     begin
       ch_error_log#add
         "no more input"
         (LBLOCK [ STR "No more input at position " ; address#toPretty ; STR " (" ;
                   INT ch#pos ; STR ")" ]) ;
       raise IO.No_more_input
     end

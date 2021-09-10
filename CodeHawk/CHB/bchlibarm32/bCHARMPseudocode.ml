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

(* chlib *)
open CHPretty

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
   
(* bchlibarm32 *)
open BCHARMTypes

let rec pow2 n =
  match n with
  | 0 -> 1
  | 1 -> 2
  | n -> 
    let b = pow2 (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else 2)


let get_opcode_cc (c:int) =
  match c with
  | 0 -> ACCEqual
  | 1 -> ACCNotEqual
  | 2 -> ACCCarrySet
  | 3 -> ACCCarryClear
  | 4 -> ACCNegative
  | 5 -> ACCNonNegative
  | 6 -> ACCOverflow
  | 7 -> ACCNoOverflow
  | 8 -> ACCUnsignedHigher
  | 9 -> ACCNotUnsignedHigher
  | 10 -> ACCSignedGE
  | 11 -> ACCSignedLT
  | 12 -> ACCSignedGT
  | 13 -> ACCSignedLE
  | 14 -> ACCAlways
  | 15 -> ACCUnconditional
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [ STR "Unexpected value for condition code: "; INT c ]))

let get_dmb_option (option:int) =
  match option with
  | 15 -> FullSystemRW
  | 14 -> FullSystemW
  | 11 -> InnerShareableRW
  | 10 -> InnerShareableW
  | 7 -> NonShareableRW
  | 6 -> NonShareableW
  | 3 -> OuterShareableRW
  | 2 -> OuterShareableW
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [STR "Unexpected value for dmb option: "; INT option]))

let get_arm_reg (r:int) =
  match r with
  | 0 -> AR0
  | 1 -> AR1
  | 2 -> AR2
  | 3 -> AR3
  | 4 -> AR4
  | 5 -> AR5
  | 6 -> AR6
  | 7 -> AR7
  | 8 -> AR8
  | 9 -> AR9
  | 10 -> AR10
  | 11 -> AR11
  | 12 -> AR12
  | 13 -> ARSP
  | 14 -> ARLR
  | 15 -> ARPC
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [ STR "Unexpected value for arm register: "; INT r ]))

let get_reglist_from_int (width:int) (reglist:int) =
  let rec collect n l =
    if n = 0 then
      if reglist mod 2 = 1 then
        (get_arm_reg 0) :: l
      else
        l
    else
      if ((reglist lsr n) mod 2) = 1 then
        collect (n-1) ((get_arm_reg n) :: l)
      else
        collect (n-1) l in
  collect (width-1) []


(* Round down to the next lower multiple of size *)
let align (a: int) (size: int): int = (a / size) * size


(* Application Program Status Register (APSR) (pg A2-49)
 * =====================================================
 *  31, N : Negative condition flag, set to bit[31] of the result of the 
 *          instruction; if the result is regarded as two's complement signed 
 *          integer, then the processor sets N to 1 if the result is negative, 
 *          and sets N to 0 if it is positive or zero.
 *  30, Z : Zero condition flag. Set to 1 if the result of the instruction is
 *          zero, and to 0 otherwise. A result of zero often indicates and 
 *          equal result from a comparison.
 *  29, C : Carry condition flag. Set to 1 if the instruction results in a
 *          carry condition, for example an unsigned overflow on an addition.
 *  28, V : Overflow condition flag. Set to 1 if the instruction results in
 *          an overflow condition, for example a signed overflow on addition.
 *  27, Q : Set to 1 to indicate overflow or saturation occurred in some
 *          instructions, normally related to digital signal processing (DSP).
 *)

(* Sign-extension of bitstrings  (pg D16-2639)
 * ===========================================
 * SignExtend(x,i) = Replicate(TopBit(x), i-Len(x)) : x
 * ----------------------------------------------------
 *)
(* argument and result are unsigned integers with the same bits as the
 * corresponding signed values, assuming two's complement *)
let sign_extend (newwidth:int) (width:int) (x:int) =
  let topbit = x lsr (width-1) in
  if newwidth >= width then
    if topbit = 0 then
      x
    else
      let pwm = pow2 (width-1) in
      let pw = pow2 newwidth in
      ((x mod pwm) - pwm) + pw
  else
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected values for newwidth and width ";
                   STR "in sign_extend: " ; INT newwidth ; STR ", ";
                   INT width ]))
    

(* Pseudocode details of shift and rotate operations (pg A2-41)
 * ============================================================
 *
 * // LSL_C
 * // ------
 * (bits(N), bit) LSL_C(bits(N) x, integer shift)
 *    assert shift > 0;
 *    extended_x = x : Zeros(shift)
 *    result = extended_x<N-1:0>
 *    carry_out = extended_x<N>;
 *    return (result, carry_out)
 * -----------------------------------------------
 *)
let do_LSL_C (width:int) (x:int) (shift:int) =
  if shift > 0 then
    let shift = if shift > (width + 1) then width + 1 else shift in
    let extended_x = x lsl shift in
    let result = extended_x mod (pow2 width) in
    let carry_out = extended_x lsr width in
    (result, carry_out)
  else
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected shift in do_LSL_C: "; INT shift ]))

(* // LSL()
 * // -----
 * bits(N) LSL(bits(N) x, integer shift)
 *   assert shift > 0;
 *   if shift == 0 then
 *     result = x;
 *   else
 *     (result,-) = LSL_C(x, shift);
 *   return result
 * ---------------------------------------
 *)
let do_LSL (width:int) (x:int) (shift:int) =
  if shift >= 0 then
    if shift = 0 then
      x
    else
      let (result,_) = do_LSL_C width  x shift in
      result
  else
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected shift in do_LSL: "; INT shift ]))
  
(* // LSR_C()
 * ----------
 *
 * ZeroExtend(x, i) = Replicate('0', i-Len(x)) : x  (pg D16-2639)
 *
 * (bits(N), bit) LSR_C(bits(N) x, integer shift)
 *    assert shift > 0
 *    extended_x = ZeroExtend(x, shift+N);
 *    result = extended_x<shift+N-1:shift>;
 *    carry_out = extended_x<shift-1>;
 *    return (result, carry_out)
 * -----------------------------------------------
 *)
let do_LSR_C (x:int) (shift:int) =
  if shift > 0 then
    let result = x lsr shift in
    let carry_out = x lsr (shift-1) mod 2 in
    (result, carry_out)
  else
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected shift in do_LSR_C: "; INT shift ]))

(* // LSR()
 * --------
 * bits(N) LSR(bits(N) x, integer shift)
 *   assert shift >= 0;
 *   if shift == 0 then
 *     result = x
 *   else
 *     (result,-) = LSR_C(x, shift);
 *   return result
 * --------------------------------------
 *)
let do_LSR (x:int) (shift:int) =
  if shift >= 0 then
    if shift == 0 then
      x
    else
      let (result,_) = do_LSR_C x shift in
      result
  else
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected shift in do_LSL: "; INT shift ]))

(* // ASR_C()
 * ----------
 *
 * SignExtend(x,i) = Replicate(TopBit(x), i-Len(x)) : x   (pg D16-2639)
 *
 * (bits(N), bit) ASR_C(bits(N) x, integer shift)
 *    assert shift > 0;
 *    extended_x = SignExtend(x, shift+N);
 *    result = extended_x<shift+N-1:shift>;
 *    carry_out = extended_x<shift-1>;
 *    return (result, carry_out)
 * -----------------------------------------------
 *)
let do_ASR_C (width:int) (x:int) (shift:int) =
  if shift > 0 then
    let extended_x = sign_extend (width+shift) width x in
    let result = extended_x lsr shift in
    let carry_out = (extended_x lsr (shift-1)) mod 2 in
    (result, carry_out)
  else
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected value for shift in do_ASR_C: ";
                   INT shift ]))

(* // ASR()
 * --------
 * bits(N) ASR(bits(N) x, integer shift)
 *   assert shift >= 0;
 *   if shift == 0 then
 *     result = x;
 *   else
 *     (result,-) = ASR_C(x, shift);
 *   return result
 * --------------------------------------
 *)
let do_ASR (width:int) (x:int) (shift:int) =
  if shift >= 0 then
    if shift == 0 then
      x
    else
      let (result,_) = do_ASR_C width x shift in
      result
  else
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected value for shift in do_ASR: " ;
                   INT shift ]))

(* // ROR_C
 * --------
 * (bits(N), bit) ROR_C(bits(N) x, integer shift)
 *    assert shift != 0;
 *    m = shift MOD N;
 *    result = LSR(x,m) OR LSL(x,N-m);
 *    carry_out = result<N-1>;
 *    return (result, carry_out);
 * -----------------------------------------------
 *)
let do_ROR_C (width:int) (x:int) (shift:int) =
  if shift != 0 then
    let m = shift mod width in
    let result = (x lsr m) + (do_LSL width x (width - m)) in
    let carry_out = (result lsr (width-1)) mod 2 in
    (result, carry_out)
  else
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected value for shift in ROR_C: ";
                   INT shift ]))

(* // ROR()
 * // -----
 * bits(N) ROR(bits(N) x, integer shift)
 *   if shift == 0 then
 *     result = x;
 *   else
 *     (result,-) = ROR_C(x,shift)
 *   return result
 * --------------------------------------
 *)
let do_ROR (width:int) (x:int) (shift:int) =
  if shift == 0 then
    x
  else
    let (result,_) = do_ROR_C width x shift in
    result
 
(* // RRX_C()
 * ----------
 * (bits(N), bit) RRX_C(bits(N) x, bit_carry_in)
 *    result = carry_in : x<N-1:>;
 *    carry_out = x<0>;
 *    return (result,carry_out)
 * ----------------------------------------------
 *)
let do_RRX_C (width:int) (x:int) (carry_in:int) =
  let result =
    if carry_in = 0 then
      x lsr 1
    else
      (x lsr 1) + (pow2 (width-1)) in
  let carry_out = x mod 2 in
  (result, carry_out)

(* // RRX()
 * --------
 * bits(N) RRX(bits(N) x, bit carry_in)
 *   (result,-) = RRX_C(x, carry_in)
 *   return result
 *)
let do_RRX (width:int) (x:int) (carry_in:int) =
  let (result,_) = do_RRX_C width x carry_in in
  result


(* Pseudocode details of instruction-specified shifts and rotates (pg A8-290)
 * ==========================================================================
 *
 * enumeration SRType { SRType_LSL, SRType_LSR, SRType_ASR, SRType_ROR,
 *                      SRType_RRX };
 *
 * (SRType, integer) DecodeImmShift(bits(2) type, bits(5) imm5)
 *   case type of
 *     when '00'
 *         shift_t = SRType_LSL; shift_n = UInt(imm5);
 *     when '01'
 *         shift_t = SRType_LSR; 
 *         shift_n = if imm5 == '00000' then 32 else UInt(imm5);
 *     when '10'
 *         shift_t = SRType_ASR;
 *         shift_n = if imm5 == '00000' then 32 else UInt(imm5);
 *     when '11'
 *         if imm5 == '00000' then
 *            shift_t = SRType_RRX; shift_n = 1;
 *         else
 *            shift_t = SRType_ROR; shift_n = UInt(imm5);
 *   return (shift_t, shift_n)
 *
 * -----------------------------------------------------------------------------
 *)
let decode_imm_shift (typebits:int) (immbits:int) =
  match typebits with
  | 0 -> (SRType_LSL, immbits)
  | 1 -> (SRType_LSR, if immbits = 0 then 32 else immbits)
  | 2 -> (SRType_ASR, if immbits = 0 then 32 else immbits)
  | 3 ->
     if immbits = 0 then
       (SRType_RRX, 1)
     else
       (SRType_ROR, immbits)
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [ STR "Unexpected value for typebits in decode_imm_shift: ";
                    INT typebits ]))

(* DecodeRegShift()
 * ================
 * SRType DecodeRegShift(bits(2) type)
 *   case type of
 *     when '00' shift_t = SRType_LSL;
 *     when '01' shift_t = SRType_LSR;
 *     when '10' shift_t = SRType_ASR;
 *     when '11' shift_t = SRType_ROR
 *   return shift_t
 * --------------------------------------
 *)
let decode_reg_shift (typebits:int) =
  match typebits with
  | 0 -> SRType_LSL
  | 1 -> SRType_LSR
  | 2 -> SRType_ASR
  | 3 -> SRType_ROR
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [ STR "Unexpected value for typebits in decode_reg_shift: ";
                    INT typebits ]))

(* Shift()
 * -------
 * bits(N) Shift(bits(N) value, SRType type, integer amount, bit carry_in)
 *   (result, -) = Shift_C(value, type, amount, carry_in)
 *   return result
 *
 * (bits(N), bit) Shift_C(bits(N) value, SRType type, integer amount, bit carry_in)
 *   assert !(type == SRType_RRX && amount != 1)
 *   if amount == 0 then
 *      (result, carry_out) = (value, carry_in);
 *   else
 *      case type of
 *        when SRType_LSL
 *            (result, carry_out) = LSL_C(value, amount);
 *        when SRType_LSR
 *            (result, carry_out) = LSR_C(value, amount);
 *        when SRType_ASR
 *            (result, carry_out) = ASR_C(value, amount);
 *        when SRType_ROR
 *            (result, carry_out) = ROR_C(value, amount);
 *        when SRType_RRX
 *            (result, carry_out) = RRX_C(value, carry_in);
 *   return (result, carry_out)
 *)
let do_shift_c (width:int) (x:int) (srt:shift_rotate_type_t) (amount:int) (carry_in:int) =
  if (srt = SRType_RRX && amount != 1) then
    raise
      (BCH_failure
         (LBLOCK [ STR "Unexpected values for srt and amount in do_shift_c: ";
                   INT amount ]))
  else
    if amount = 0 then
      (x,carry_in)
    else
      match srt with
      | SRType_LSL -> do_LSL_C width x amount
      | SRType_LSR -> do_LSR_C x amount
      | SRType_ASR -> do_ASR_C width x amount
      | SRType_ROR -> do_ROR_C width x amount
      | SRType_RRX -> do_RRX_C width x carry_in

let do_shift (width:int) (x:int) (srt:shift_rotate_type_t) (amount:int) (carry_in:int) =
  let (result,_) = do_shift_c width x srt amount carry_in in
  result
       
(* Operation of modified immediate constants (pg A5-199)
 * =====================================================
 * bits(32) ARMExpandImm(bits(12 imm12)
 *  // APSR.C argument to following function call does not affect the imm32
 *  // result
 *  (imm32, -) = ARMExpandImm_C(imm12, APSR.C);
 *  return imm32;
 *
 * (bits(32), bit) ARMExpandImm_C(bits(12) imm12, bit carry_in)
 *   unrotated_value = ZeroExtend(imm12<7:0>, 32);
 *   (imm32,carry_out) = 
 *       Shift_C(unrotated_value, SRType_ROR, 2*UInt(imm12<11:8>),carry_in);
 *   return (imm32, carry_out)
 *)
let arm_expand_imm_c (rotate4:int) (imm8:int) (carry_in:int) =
  do_shift_c 32 imm8 SRType_ROR (2*rotate4) carry_in

let arm_expand_imm (rotate4:int) (imm8:int) =
  let (imm32,_) = arm_expand_imm_c rotate4 imm8 0 in
  imm32


    

(* ThumbExpandImm (pg A6-230)
 * ==========================
 * bits(32) ThumbExpandImm(bits(12) imm12)
 * // APSR.C argument to following function call does not affect
 * // the imm32 result
 *   (imm32, _) = ThumbExpandImm_C(imm12, APSR.C);
 *   return imm32;
 *
 * (bits(32), bit) ThumbExpandImm_C(bits(12), bit carry_in)
 *   if imm12<11:10> == '00' then
 *      case imm12<9:8> of
 *         when '00'
 *            imm32 = ZeroExtend(imm12<7:0>, 32)
 *         when '01'
 *            if imm12<7:0> == '00000000' then UNPREDICTABLE;
 *            imm32 = '00000000' : imm12<7:0> : '00000000' : imm12<7:0>;
 *         when '10'
 *            if imm12<7:0> == '00000000' then UNPREDICTABLE;
 *            imm32 = imm12<7:0> : '00000000' : imm12<7:0> : '00000000';
 *         when '11'
 *            if imm12<7:0> == '00000000' then UNPREDICTABLE;
 *            imm32 = imm12<7:0> : imm12<7:0> : imm12<7:0> : imm12<7:0>;
 *      carry_out = carry_in
 *   else
 *      unrotated_value = ZeroExtend('1':imm12<6:0>, 32);
 *      (imm32, carry_out) = ROR_C(unrotated_value, UInt(imm12<11:7>));
 *
 *   return (imm32, carry_out);
 *)
  
let thumb_expand_imm_c (imm12: int) (carry: int): int * int =
  let c1 = imm12 lsr 10 in
  let c2 = (imm12 lsr 8) mod 4 in
  let v = imm12 mod 256 in
  let (imm32, c) =
    if c1 = 0 then
      let imm =
        match c2 with
        | 0 -> v
        | 1 -> (v lsl 16) + v
        | 2 -> (v lsl 24) + (v lsl 8)
        | 3 -> (v lsl 24) + (v lsl 16) + (v lsl 8) + v
        | _ -> raise (BCH_failure (STR "thumb_expand_imm_c")) in
      (imm, carry)
    else
      let unrotval = (1 lsl 7) + (imm12 mod 128) in
      do_ROR_C 32 unrotval (imm12 lsr 7) in
  (imm32, c)
      
let thumb_expand_imm (imm12: int) (carry: int): int =
  let (imm32, _) = thumb_expand_imm_c imm12 carry in
  imm32

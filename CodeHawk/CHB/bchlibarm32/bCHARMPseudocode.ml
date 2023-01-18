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


(* Documentation reference:
 * ========================
 * ARM Architecture Reference Manual
 * ARMv7-A and ARMv7-R edition, March 29, 2018
 *)

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHSystemSettings
   
(* bchlibarm32 *)
open BCHARMTypes

module TR = CHTraceResult

exception ARM_undefined of string
exception ARM_unpredictable of string


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


(* bit:v *)
let prefix_bit (bit: int) (v: int) = (16 * bit) + v


(* v:bit *)
let postfix_bit (bit: int) (v: int) = (2 * v) + bit


(* Round down to the next lower multiple of size *)
let align (a: int) (size: int): int = (a / size) * size


let align_dw (dw: doubleword_int) (size: int): doubleword_int =
  TR.tget_ok (int_to_doubleword (align dw#to_int size))


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


(* convert an integer to an n-bit bit string *)
let to_bit_string (x: int) (n: int): string =
  let f i = if ((x lsr i) mod 2) = 0 then '0' else '1' in
  let rev s =
    let len = String.length s in
    String.init len (fun i -> s.[len - 1 - i]) in
  rev (String.init n f)


(* Bitstring concatenation and replication
 * =======================================
 *
 * Replicate(x, n): bitstring of length n*Len(x) consisting of n copies of x
 *  concatenated together
 *
 * Zeros(n) = Replicate('0', n)
 * Ones(n) = Replicate('1', n)
 *)
let replicate (x: string) (n: int): string =
  string_repeat x n


let replicate_int (x: int) (xlen) (cnt: int): string =
  replicate (to_bit_string x xlen) cnt


let bit_string_to_numerical (s: string): numerical_t =
  let i64 = Int64.of_string ("0b" ^ s) in
  mkNumericalFromInt64 i64


let zeros (n: int): string = string_repeat "0" n


let ones (n: int): string = string_repeat "1" n


(* VFPExpandImm (pg A7-271)
 * ========================
 * bits(N) VFPExpandImm(bits(8) imm8, integer N)
 *   assert N in {32, 64};
 *   if N == 32 then
 *     E = 8;
 *   else
 *     E = 11;
 *   F = N - E - 1;
 *   sign = imm8<7>;
 *   exp = NOT(imm8<6>):Replicate(imm<6>, E-3):imm8<5:4>;
 *   frac = imm8<3:0>:Zeros(F-4);
 *   return sign:exp:frac
 *)
let vfp_expand_imm (imm8: int) (n: int): numerical_t =
  let e = if n == 32 then 8 else 11 in
  let f = (n - e) - 1 in
  let sign = imm8 lsr 7 in
  let imm8_6 = (imm8 lsr 6) mod 2 in
  let imm8_6_neg = if imm8_6 = 1 then 0 else 1 in
  let imm8_5 = (imm8 lsr 5) mod 2 in
  let imm8_4 = (imm8 lsr 4) mod 2 in
  let s_imm8_6 = string_of_int imm8_6 in
  let s_imm8_6_neg = string_of_int imm8_6_neg in
  let exp =
    s_imm8_6_neg
    ^ (string_repeat s_imm8_6 (e-3))
    ^ (string_of_int imm8_5)
    ^ (string_of_int imm8_4) in
  let s_imm_3 = string_of_int ((imm8 lsr 3) mod 2) in
  let s_imm_2 = string_of_int ((imm8 lsr 2) mod 2) in
  let s_imm_1 = string_of_int ((imm8 lsr 1) mod 2) in
  let s_imm_0 = string_of_int (imm8 mod 2) in
  let frac =
    s_imm_3
    ^ s_imm_2
    ^ s_imm_1
    ^ s_imm_0
    ^ (string_repeat "0" (f - 4)) in
  let sv = "0b" ^ (string_of_int sign) ^ exp ^ frac in
  let v = mkNumericalFromInt64 (Int64.of_string sv) in
  let _ =
    if collect_diagnostics () then
      ch_diagnostics_log#add
        "vfp-expand"
        (LBLOCK [
             STR "imm8: ";
             INT imm8;
             STR "; exp: ";
             STR exp;
             STR "; frac: ";
             STR frac;
             STR "; sv: ";
             STR sv;
             STR "; value: ";
             v#toPretty]) in
  v


(* Advanced SIMD expand immediate (pg A7-269)
 * ==========================================
 * bits(64) AdvSIMDExpandImm(bit op, bits(4) cmode, bits(8) imm8)
 *
 * case cmode<3:1> of
 *   when '000'
 *     testimm8 = FALSE; imm64 = Replicate(Zeros(24):imm8, 2)
 *   when '001'
 *     testimm8 = TRUE;  imm64 = Replicate(Zeros(16):imm8:Zeros(8), 2)
 *   when '010'
 *     testimm8 = TRUE;  imm64 = Replicate(Zeros(8):imm8:Zeros(16), 2)
 *   when '011'
 *     testimm8 = TRUE;  imm64 = Replicate(imm8:Zeros(24), 2)
 *   when '100'
 *     testimm8 = FALSE; imm64 = Replicate(Zeros(8):imm8, 4)
 *   when '101
 *     testimm8 = TRUE;  imm64 = Replicate(imm8:Zeros(8), 4)
 *   when '110'
 *     testimm8 = TRUE;
 *     if cmode<0> == '0' then
 *       imm64 = Replicate(Zeros(16):imm8:Ones(8), 2)
 *     else
 *       imm64 = Replicate(Zeros(8):imm8:Ones(16), 2)
 *   when '111'
 *     testimm8 = FALSE;
 *     if cmode<0> == '0' && op == '0' then
 *       imm64 = Replicate(imm8, 8);
 *     if cmode<0> == '0' && op == '1' then
 *       imm8a = Replicate(imm8<7>, 8);
 *       imm8b = Replicate(imm8<6>, 8);
 *       imm8c = Replicate(imm8<5>, 8);
 *       imm8d = Replicate(imm8<4>, 8);
 *       imm8e = Replicate(imm8<3>, 8);
 *       imm8f = Replicate(imm8<2>, 8);
 *       imm8g = Replicate(imm8<1>, 8);
 *       imm8h = Replicate(imm8<0>, 8);
 *       imm64 = imm8a:imm8b:imm8c:imm8d:imm8e:imm8f:imm8g:imm8h;
 *     if cmode<0> == '1' && op == '0' then
 *       imm32 = imm8<7>:NOT(imm8<6>):Replicate(imm8<6>,5):imm8<5:0>:Zeros(19);
 *       imm64 = Replicate(imm32, 2)
 *     if cmode<0> == '1' && op == '1' then
 *       UNDEFINED;
 *
 *   if testimm8 && imm8 == '00000000' then
 *     UNPREDICTABLE;
 *
 *   return imm64;
 *)
let adv_simd_expand_imm (op: int) (cmode: int) (imm8: int) =
  let mk_imm64 (s: string) (n: int) = bit_string_to_numerical (replicate s n) in
  let xbit n = (imm8 lsr n) mod 2 in
  let imm8s = to_bit_string imm8 8 in
  let cmode0 = cmode mod 2 in
  let (testimm8, imm64) =
    match cmode / 2 with
    | 0 -> (false, mk_imm64 ((zeros 24) ^ imm8s) 2)
    | 1 -> (true, mk_imm64 ((zeros 16) ^ imm8s ^ (zeros 8)) 2)
    | 2 -> (true, mk_imm64 ((zeros 8) ^ imm8s ^ (zeros 16)) 2)
    | 3 -> (true, mk_imm64 (imm8s ^ (zeros 24)) 2)
    | 4 -> (false, mk_imm64 ((zeros 8) ^ imm8s) 4)
    | 5 -> (true, mk_imm64 (imm8s ^ (zeros 8)) 4)
    | 6 when cmode0 = 0 -> (false, mk_imm64 ((zeros 16) ^ imm8s ^ (ones 8)) 2)
    | 6 when cmode0 = 1 -> (false, mk_imm64 ((zeros 8) ^ imm8s ^ (ones 16)) 2)
    | 7 when cmode0 = 0 && op = 0 -> (false, mk_imm64 imm8s 8)
    | 7 when cmode0 = 0 && op = 1 ->
       let mk_1rep b = if b = 0 then "00000000" else "11111111" in
       let imm8a = mk_1rep (xbit 7) in
       let imm8b = mk_1rep (xbit 6) in
       let imm8c = mk_1rep (xbit 5) in
       let imm8d = mk_1rep (xbit 4) in
       let imm8e = mk_1rep (xbit 3) in
       let imm8f = mk_1rep (xbit 2) in
       let imm8g = mk_1rep (xbit 1) in
       let imm8h = mk_1rep (xbit 0) in
       let imm64s =
         String.concat "" [imm8a; imm8b; imm8c; imm8d; imm8e; imm8f; imm8g; imm8h] in
       (false, mk_imm64 imm64s 1)
    | 7 when cmode0 = 1 && op = 0 ->
       let imm32 =
         let s7 = String.sub imm8s 0 1 in
         let s6 = if imm8s.[1] = '1' then "0" else "1" in
         let s6p = replicate (String.sub imm8s 1 1) 5 in
         let s5 = String.sub imm8s 2 6 in
         s7 ^ s6 ^ s6p ^ s5 ^ (zeros 19) in
       (false, mk_imm64 imm32 2)
    | 7 when cmode0 = 1 && op = 1 ->
       raise (ARM_undefined ("AdvSIMDExpandImm with cmode<0> = 1 && op = 1"))
    | _ ->
       raise
         (BCH_failure (LBLOCK [STR "Internal error in adv_simd_expand_imm"])) in

  if testimm8 && imm8 = 0 then
    raise (ARM_unpredictable ("AdvSIMExpandImm: testimm8 && imm8 = 0"))
  else
    imm64


(* Modified immediate values for Advanced SIMD instructions (Table A7-15)
 * ======================================================================
 * op  cmode  <dt>  notes
 * ----------------------------------------------------------------------
 * -   000x   I32   VBIC, VMOV, VMVN, VORR
 *     001x   I32   VBIC, VMOV, VMVN, VORR
 *     010x   I32   VBIC, VMOV, VMVN, VORR
 *     011x   I32   VBIC, VMOV, VMVN, VORR
 *     100x   I16   VBIC, VMOV, VMVN, VORR
 *     101x   I16   VBIC, VMOV, VMVN, VORR
 *     1100   I32   VMOV, VMVN
 *     1101   I32   VMOV, VMVN
 * 0   1110   I8    VMOV
 * 0   1111   F32   VMOV
 * 1   1110   I64   VMOV
 * 1   1111   UNDEFINED
 * -------------------------------------------------------------------------
 *)
let adv_simd_mod_dt (op: int) (cmode: int) (opcs: string) =
  match cmode with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 -> VfpInt 32
  | 12 | 13 ->
     (match opcs with
      | "VMOV" | "VMVN" ->
         VfpInt 32
      | _ ->
         raise
           (ARM_undefined
              ("AdvSIMD-modified datatype for "
               ^ opcs
               ^ ": cmode = " ^ (string_of_int cmode))))
  | 8 | 9 | 10 | 11 -> VfpInt 16
  | _ ->
     (match (opcs, op, cmode) with
      | (("VMOV" | "VMVN"), 0, 14) -> VfpInt 8
      | (("VMOV" | "VMVN"), 0, 15) -> VfpFloat 32
      | (("VMOV" | "VMVN"), 1, 14) -> VfpInt 64
      | _ ->
         raise
           (ARM_undefined
              ("AdvSIMD-modified datatype for "
               ^ opcs
               ^ ": cmode = "
               ^ (string_of_int cmode)
               ^ ", op = "
               ^ (string_of_int op))))


(* Signed Saturation Operations
 * ===========================================================================
 * Some instructions perform saturating arithmetic, that is, if the result of
 * the arithmetic overflows the destination signed or unsigned N-bit integer
 * range, the result produced is the largest or smallest value in that range,
 * rather than wrapping around module 2^N.
 *
 * (bits(N), boolean) SignedSatQ(integer i, integer N)
 *    if i > 2^(N-1) - 1 then
 *       result = 2^(N-1) - 1;  saturated = TRUE;
 *    elsif i < -(2^(N-1)) then
 *       result = -(2^(N-1));  saturated = TRUE;
 *    else
 *        result = i;  saturated = FALSE;
 *    return (result<N-1:0>, saturated);
 *
 * (bits(N), boolean) UnsignedSatQ(integer i, integer N)
 *    if i > 2^N - 1 then
 *       result = 2^N - 1;  saturated = TRUE;
 *    elsif i < 0 then
 *       result = 0;  saturated = TRUE;
 *    else
 *       result = i;  saturated = FALSE;
 *    return (result<N-1:0>, saturated);
 *)

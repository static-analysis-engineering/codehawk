(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs, LLC

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
open CHPretty

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHImmediate
open BCHLibTypes
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMDisassemblyUtils
open BCHARMOperand
open BCHARMPseudocode
open BCHARMTypes

module TR = CHTraceResult

(*
   16-bit

   Shift (immediate), add, subtract, move, and compare
   ---------------------------------------------------
   0000000000<r><r>  MOV (register)
   00000<im5><r><r>  LSL (immediate)
   00001<im5><r><r>  LSR (immediate)
   00010<im5><r><r>  ASR (immediate)
   0001100<r><r><r>  ADD (register)
   0001101<r><r><r>  SUB (register)
   0001110<i><r><r>  ADD (immediate)
   0001111<i><r><r>  SUB (immediate)
   00100<r><-imm8->  MOV (immediate)
   00101<r><-imm8->  CMP (immediate)
   00110<r><-imm8->  ADD (immediate)
   00111<r><-imm8->  SUB (immediate)

   Data-processing
   ---------------
   0100000000<r><r>  AND (register)
   0100000001<r><r>  EOR (register)
   0100000010<r><r>  LSL (register)
   0100000011<r><r>  LSR (register)
   0100000100<r><r>  ASR (register)
   0100000101<r><r>  ADC (register)
   0100000110<r><r>  SBC (register)
   0100000111<r><r>  ROR (register)
   0100001000<r><r>  TST (register)
   0100001001<r><r>  RSB (immediate)
   0100001010<r><r>  CMP (register)
   0100001011<r><r>  CMN (register)
   0100001100<r><r>  ORR (register)
   0100001101<r><r>  MUL
   0100001110<r><r>  BIC (register)
   0100001111<r><r>  MVN (register)


   Special data processing
   -----------------------
   01000100D<rm><r>  ADD (register)
   01000100D1101<r>  ADD (SP plus register)
   010001001<rm>101  ADD (SP plus register)
   01000101N<rm><r>  CMP (register)
   01000110D<rm><r>  MOV (register)
   010001110<rm>000  BX
   010001111<rm>000  BLX (register)

   Load/store single data item
   ---------------------------
   01001<r><-imm8->  LDR (literal
   0101000<r><r><r>  STR (register)
   0101001<r><r><r>  STRH (register)
   0101010<r><r><r>  STRB (register)
   0101011<r><r><r>  LDRSB (register)
   0101100<r><r><r>  LDR (register)
   0101101<r><r><r>  LDRH (register)
   0101110<r><r><r>  LDRB (register)
   0101111<r><r><r>  LDRSH (register)
   01100<imm><r><r>  STR (immediate)
   01101<imm><r><r>  LDR (immediate)
   01110<imm><r><r>  STRB (immediate)
   01111<imm><r><r>  LDRB (immediate)
   10000<imm><r><r>  STRH (immediate)
   10001<imm><r><r>  LDRH (immediate)
   10010<r><-imm8->  STR (immediate)
   10011<r><-imm8->  LDR (immediate)

   Generate PC-relative address
   ----------------------------
   10100<r><-imm8->  ADR

   Generate SP-relative address
   ----------------------------
   10101<r><-imm8->  ADD (SP plus immediate)

   Miscellaneous
   -------------
   101100000<imm7->  ADD (SP plus immediate)
   101100001<imm7->  SUB (SP minus immediate)
   1011001000<r><r>  SXTH
   1011001001<r><r>  SXTB
   1011001010<r><r>  UXTH
   1011001011<r><r>  UXTB
   1011010M<rlist->  PUSH
   101101100101E000  SETEND
   1011p0i1<-i5><r>  CBNZ
   1011101000<r><r>  REV
   1011101001<r><r>  REV
   1011101011<r><r>  REVSH
   1011110p<rlist->  POP
   10111110<-imm8->  BKPT
   1011111100000000  NOP
   1011111100010000  YIELD
   1011111100100000  WFE
   1011111100110000  WFE
   1011111101000000  SEV
   10111111<cc><mk>  IT (If-then)

   Store/Load multiple registers
   ------------------------
   11000<r><rlist->  STM/STMIA/STMEA
   11001<r><rlist->  LDM/LDMIA/LDMFD

   Conditional branch and Supervisor Call
   --------------------------------------
   1101<cc><-imm8->  B
   11011110<-imm8->  UDF
   11011111<-imm8->  SVC

   Unconditional branch
   --------------------
   11100<--imm11-->  B


   32-bit

   111010000101<rn><rt>1111<-imm8->   LDREX
   111010000100<rn><rt><rd><-imm8->   STREX
   1110100010W0<rn>0m0<---rlist--->   STM/STMIA/STMEA
   1110100010W1<rn>pm0<---rlist--->   LDM/LDMIA
   111010001100<rn><rt><rt>0111<rd>   STREXD
   111010001100<rn><rt>11110100<rd>   STREXB
   111010001100<rn><rt>11110101<rd>   STREXH
   111010001101<rn><rt><rt>01111111   LDREXD
   111010001101<rn><rt>111101001111   LDREXB
   111010001101<rn><rt>111101011111   LDREXH
   111010001101<rn>11110000000H<rm>   TBB, TBH
   1110100010111101pm0<---rlist--->   POP
   1110100pu1W0<rn><rt><rt><-imm8->   STRD (immediate)
   1110100pu1W1<rn><rt><rt><-imm8->   LDRD (immediate)
   1110100pu1W11111<rt><rt><-imm8->   LRDR (literal)
   1110100100W0<rn>0m0<---rlist--->   STMDB/STMFD
   1110100100W1<rn>pm0<---rlist--->   LDMDB/LDMEA
   11101001001011010M0<---rlist--->   PUSH.W
   11101010000S<rn>0<i><rd>i2ty<rm>   AND (register)
   111010100001<rn>0<i>1111i2ty<rm>   TST (register)
   11101010001S<rn>0<i><rd>i2ty<rm>   BIC (register)
   11101010010S<rn>0<i><rd>i2ty<rm>   ORR (register)
   11101010010S11110000<rd>0000<rm>   MOV (register)
   11101010010S11110000<rd>0011<rm>   RRX
   11101010010S11110<i><rd>i200<rm>   LSL (immediate)
   11101010010S11110<i><rd>i201<rm>   LSR (immediate)
   11101010010S11110<i><rd>i210<rm>   ASR (immediate)
   11101010010S11110<i><rd>i211<rm>   ROR (immediate)
   11101010011S<rn>0<i><rd>i2ty<rm>   ORN (register)
   11101010011S11110<i><rd>i2ty<rm>   MVN (register)
   11101010100S<rn>0<i><rd>i2ty<rm>   EOR (register)
   111010101001<rn>0<i>1111i2ty<rm>   TEQ (register)
   11101010110S<rn>0<i><rd>i2tt<rm>   PKH
   11101011000S<rn>0<i><rd>i2ty<rm>   ADD (register)
   11101011000S11010<i><rd>i2ty<rm>   ADD (SP plus register)
   111010110001<rn>0<i>1111i2ty<rm>   CMN (register)
   11101011010S<rn>0<i><rd>i2ty<rm>   ADC (register)
   11101011011S<rn>0<i><rd>i2ty<rm>   SBC (register)
   11101011101S<rn>0<i><rd>i2ty<rm>   SUB (register)
   11101011101S11010<i><rd>i2ty<rm>   SUB (SP minus register)
   111010111011<rn>0<i>1111i2ty<rm>   CMP (register)
   11101011110S<rn>0<i><rd>i2ty<rm>   RSB (register)

   floating point
   --------------
   11101101UD00<rn><vd>1011<-imm8->   VSTR
   11101101UD01<rn><vd>1010<-imm8->   VLDR
   11101101UD01<rn><vd>1011<-imm8->   VLDR
   11101110000o<vn><rt>1010N0010000   VMOV (register to single-prec register)
   11101110<o>1<rn><rt><co><o>1<rm>   MRC (from coprocessor to arm core register)
   111011101D110100<vd>101sE1M0<vm>   VCMP, VCMPE
   111011101D11<i4><vd>101s0000<i4>   VMOV (immediate)
   111011101D111<o><vd>101so1M0<vm>   VCVT (floating point to integer)
   1110111011110001<rt>101000010000   VMRS

   1111001100s0<rn>0<i><rd>i20<sim>   SSAT
   111100110010<rn>0000<rd>0000<si>   SSAT16
   111100110100<rn>0<i><rd>i20<wm1>   SBFX
   111100110110<rn>0<i><rd>i20<msb>   BFI
   11110011011011110<i><rd>i20<msb>   BFC
   111100111000<rn>1000mm0000000000   MSR (register)
   1111001110s0<rn>0<i><rd>i20<sim>   USAT
   111100111010<rn>0000<rd>0000<sm>   USAT16
   11110011101011111000000000000000   NOP
   11110011101011111000000000000001   YIELD
   11110011101011111000000000000010   WFE
   11110011101011111000000000000011   WFI
   11110011101011111000000000000100   SEV
   1111001110111111100011110101<op>   DMB
   111100111100<rn>0<i><rd>i20<wm1>   UBFX
   11110011111011111000<rd>00000000   MRS
   11110i000001<rn>0<i>1111<-imm8->   TST (immediate)
   11110i00001S<rn>0<i><rd><-imm8->   BIC (immediate)
   11110i00000S<rn>0<i><rd><-imm8->   AND (immediate)
   11110i00010S<rn>0<i><rd><-imm8->   ORR (immediate)
   11110i00010S11110<i><rd><-imm8->   MOV.W (immediate)
   11110i00011S<rn>0<i><rd><-imm8->   ORN (immediate)
   11110i00011S11110<i><rd><-imm8->   MVN (immediate)
   11110i00100S<rn>0<i><rd><-imm8->   EOR (immediate)
   11110i001001<rn>0<i>1111<-imm8->   TEQ (immediate)
   11110i01000S11010<i><rd><-imm8->   ADD (SP plus immediate)
   11110i01010S<rn>0<i><rd><-imm8->   ADC (immediate)
   11110i01000S<rn>0<i><rd><-imm8->   ADD (immediate)
   11110i010001<rn>0<i>1111<-imm8->   CMN (immediate)
   11110i01011S<rn>0<i><rd><-imm8->   SBC (immediate)
   11110i01101S<rn>0<i><rd><-imm8->   SUB (immediate)
   11110i01101S11010<i><rd><-imm8->   SUB (SP minus immediate)
   11110i011011<rn>0<i>1111<-imm8->   CMP (immediate)
   11110i01110S<rn>0<i><rd><-imm8->   RSB (immediate)
   11110i10000011010<i><rd><-imm8->   ADD (SP plus immediate)
   11110i100000<rn>0<i><rd><-imm8->   ADD (immediate)
   11110i10000011110<i><rd><-imm8->   ADR
   11110i100100<ii>0<i><rd><-imm8->   MOVW (immediate)
   11110i101010<rn>0<i><rd><-imm8->   SUB (immediate)
   11110i10101011010<i><rd><-imm8->   SUB (SP minus immediate)
   11110i10101011110<i><rd><-imm8->   ADR
   11110i101100<ii>0<i><rd><-imm8->   MOVT
   11110S<cc><imm6>10J0J<--imm11-->   B
   11110S<--imm10->10J1J<--imm11-->   B
   11110S<-imm10H->11J0J<-imm10L->H   BLX (immediate)
   11110S<--imm10->11J1J<--imm11-->   BL  (immediate)
   111101111111<i4>1010<---imm12-->   UDF

   111110000000<rn><rt>000000i2<rm>   STRB (register)
   111110000000<rn><rt>1puw<-imm8->   STRB (immediate)
   111110000000<rn><rt>1110<-imm8->   STRBT
   111110000001<rn><rt>000000i2<rm>   LDRB (register)
   111110000001<rn><rt>1110<-imm8->   LDRBT
   111110000001<rn><rt>1puw<-imm8->   LDRB (immediate)
   1111100000w1<rn>1111000000i2<rm>   PLD, PLDW (register)
   1111100000w1<rn>11111100<-imm8->   PLD, PLDW (immediate)
   111110000010<rn><rt>00000i2<rm>    STRH (register)
   111110000010<rn><rt>1puw<-imm8->   STRH (immediate)
   111110000010<rn><rt>1110<-imm8->   STRHT
   111110000011<rn><rt>000000i2<rm>   LDRH (register)
   111110000011<rn><rt>1110<-imm8->   LDRHT
   111110000011<rn><rt>1puw<-imm8->   LDRH (immediate)
   111110000100<rn><rt>1110<-imm8->   STRT
   111110000100<rn><rt>000000i2<rm>   STR (register)
   111110000100<rn><rt>1puw<-imm8->   STR (immediate)
   1111100001001101<rt>110100000100   PUSH.W
   111110000101<rn><rt>000000i2<rm>   LDR (register)
   111110000101<rn><rt>1puw<-imm8->   LDR (immediate)
   111110000101<rn><rt>1110<-imm8->   LDRT
   1111100001011101<rt>101100000100   POP
   11111000u0011111<rt><--imm12--->   LDRB (literal)
   11111000u00111111111<--imm12--->   PLD (literal)
   11111000u1011111<rt><--imm12--->   LDR (literal)
   11111000u0111111<rt><--imm12--->   LDRH (literal)
   111110001000<rn><rt><--imm12--->   STRB (immediate)
   111110001001<rn><rt><--imm12--->   LDRB (immediate)
   1111100010w1<rn>1111<--imm12--->   PLD, PLDW (immediate)
   111110001010<rn><rt><--imm12--->   STRH (immediate)
   111110001011<rn><rt><--imm12--->   LDRH (immediate)
   111110001100<rn><rt><--imm12--->   STR (immediate)
   111110001101<rn><rt><--imm12--->   LDR (immediate)
   111110010001<rn><rt>000000i2<rm>   LDRSB (register)
   111110010001<rn><rt>1puw<-imm8->   LDRSB (immediate)
   111110010001<rn>11111100<-imm8->   PLI (immediate, literal)
   111110010001<rn><rt>1110<-imm8->   LDRSBT
   111110010001<rn>1111000000i2<rm>   PLI (register)
   111110010011<rn><rt>000000i2<rm>   LDRSH (register)
   111110010011<rn><rt>1puw<-imm8->   LDRSH (immediate)
   111110010011<rn><rt>1110<-imm8->   LDRSHT
   11111001u0011111<rt><--imm12--->   LDRSB (literal)
   11111001U00111111111<--imm12--->   PLI (immediate, literal)
   11111001u0111111<rt><--imm12--->   LDRSH (literal)
   111110011001<rn><rt><--imm12--->   LDRSB (immediate)
   111110011001<rn>1111<--imm12--->   PLI (immediate, literal)
   111110011011<rn><rt><--imm12--->   LDRSH (immediate)
   111110100000<rn>1111<rd>10ro<rm>   SXTAH
   11111010000011111111<rd>10ro<rm>   SXTH
   11111010000S<rn>1111<rd>0000<rm>   LSL (register)
   111110100001<rn>1111<rd>10ro<rm>   UXTAH
   11111010000111111111<rd>10ro<rm>   UXTH
   111110100010<rn>1111<rd>10ro<rm>   SXTAB16
   11111010001011111111<rd>10ro<rm>   SXTB16
   11111010001S<rn>1111<rd>0000<rm>   LSR (register)
   111110100011<rn>1111<rd>10ro<rm>   UXTAB16
   11111010001111111111<rd>10ro<rm>   UXTB16
   111110100100<rn>1111<rd>10ro<rm>   SXTAB
   11111010010011111111<rd>10ro<rm>   SXTB
   11111010010S<rn>1111<rd>0000<rm>   ASR (register)
   111110100101<rn>1111<rd>10ro<rm>   UXTAB
   11111010010111111111<rd>10ro<rm>   UXTB
   11111010011S<rn>1111<rd>0000<rm>   ROR (register)
   111110101000<rn>1111<rd>0000<rm>   SADD8
   111110101000<rn>1111<rd>0001<rm>   QADD8
   111110101000<rn>1111<rd>0010<rm>   SHADD8
   111110101000<rn>1111<rd>0100<rm>   UADD8
   111110101000<rn>1111<rd>0101<rm>   UQADD8
   111110101000<rn>1111<rd>0110<rm>   UHADD8
   111110101000<rn>1111<rd>1000<rm>   QADD
   111110101000<rn>1111<rd>1001<rm>   QDADD
   111110101000<rn>1111<rd>1010<rm>   QSUB
   111110101000<rn>1111<rd>1011<rm>   QDSUB
   111110101001<rn>1111<rd>0000<rm>   SADD16
   111110101001<rn>1111<rd>0001<rm>   QADD16
   111110101001<rn>1111<rd>0010<rm>   SHADD16
   111110101001<rn>1111<rd>0100<rm>   UADD16
   111110101001<rn>1111<rd>0101<rm>   UQADD16
   111110101001<rn>1111<rd>0110<rm>   UHADD16
   111110101001<rm>1111<rd>1000<rm>   REV
   111110101001<rm>1111<rd>1001<rm>   REV16
   111110101001<rm>1111<rd>1010<rm>   RBIT
   111110101001<rm>1111<rd>1011<rm>   REVSH
   111110101010<rm>1111<rd>0000<rm>   SASX
   111110101010<rn>1111<rd>0001<rm>   QASX
   111110101010<rn>1111<rd>0010<rm>   SHASX
   111110101010<rn>1111<rd>0100<rm>   UASX
   111110101010<rn>1111<rd>0101<rm>   UQASX
   111110101010<rn>1111<rd>0110<rm>   UHASX
   111110101010<rn>1111<rd>1000<rm>   SEL
   111110101011<rm>1111<rd>1000<rm>   CLZ
   111110101100<rn>1111<rd>0000<rm>   SSUB8
   111110101100<rn>1111<rd>0001<rm>   QSUB8
   111110101100<rn>1111<rd>0010<rm>   SHSUB8
   111110101100<rn>1111<rd>0100<rm>   USUB8
   111110101100<rn>1111<rd>0101<rm>   UQSUB8
   111110101100<rn>1111<rd>0110<rm>   UHSUB8
   111110101101<rn>1111<rd>0000<rm>   SSUB16
   111110101101<rn>1111<rd>0001<rm>   QSUB16
   111110101101<rn>1111<rd>0010<rm>   SHSUB16
   111110101101<rn>1111<rd>0100<rm>   USUB16
   111110101101<rn>1111<rd>0101<rm>   UQSUB16
   111110101101<rn>1111<rd>0110<rm>   UHSUB16
   111110101110<rn>1111<rd>0000<rm>   SSAX
   111110101110<rn>1111<rd>0001<rm>   QSAX
   111110101110<rn>1111<rd>0010<rm>   SHSAX
   111110101110<rn>1111<rd>0100<rm>   USAX
   111110101110<rn>1111<rd>0101<rm>   UQSAX
   111110101110<rn>1111<rd>0110<rm>   UHSAX
   111110110000<rn><ra><rd>0000<rm>   MLA
   111110110000<rn>1111<rd>0000<rm>   MUL
   111110110000<rn><ra><rd>0001<rm>   MLS
   111110110001<rn><ra><rd>00NM<rm>   SMLABB
   111110110001<rn>1111<rd>00NM<rm>   SMULBB
   111110110010<rn><ra><rd>000M<rm>   SMLAD
   111110110010<rn>1111<rd>000M<rm>   SMUAD
   111110110011<rn><ra><rd>000M<rm>   SMLAWD
   111110110011<rn>1111<rd>000M<rm>   SMULWB
   111110110100<rn><ra><rd>000M<rm>   SMLSD
   111110110100<rn>1111<rd>000M<rm>   SMUSD
   111110110101<rn><ra><rd>000R<rm>   SMMLA
   111110110101<rn>1111<rd>000R<rm>   SMMUL
   111110110110<rn><ra><rd>000R<rm>   SMMLS
   111110110111<rn><ra><rd>0000<rm>   USADA8
   111110110111<rn>1111<rd>0000<rm>   USAD8
   111110111000<rn><lo><hi>0000<rm>   SMULL
   111110111001<rn>1111<rd>1111<rm>   SDIV
   111110111010<rn><lo><hi>0000<rm>   UMULL
   111110111011<rn>1111<rd>1111<rm>   UDIV
   111110111100<rn><rd><rd>0000<rm>   SMLAL
   111110111100<rn><rd><rd>10NM<rm>   SMLALBB
   111110111100<rn><rd><rd>110M<rm>   SMLALD
   111110111101<rn><lo><hi>110M<rm>   SMLSLD
   111110111110<rn><lo><hi>0000<rm>   UMLAL
   111110111110<rn><lo><hi>0110<rm>   UMAAL

 *)


let stri = string_of_int

let unpredictable (iaddr: doubleword_int) (msg: string) =
  ch_error_log#add
    "thumb unpredictable"
    (LBLOCK [iaddr#toPretty; STR ": "; STR msg])


class itblock_t =
object
  val mutable conditionlist = []

  method set_condition_list (l:(string * arm_opcode_cc_t) list) =
    conditionlist <- l

  method get_xyz = String.concat "" (List.tl (List.map fst conditionlist))

  method is_in_it =
    match conditionlist with
    | [] -> false
    | _ -> true

  method consume_condition =
    match conditionlist with
    | h::tl ->
       begin
         conditionlist <- tl;
         snd h
       end
    | _ ->
       raise (BCH_failure (LBLOCK [STR "No condition to consume"]))

end


let itblock = new itblock_t


let parse_thumb32_29_0
      ?(_in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (_ch: pushback_stream_int)
      (_iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let selector = b 24 20 in
  match selector with

  (* < 29>00PU1W0<rn><rt><t2><-imm8->   STRD (immediate) - T1 *)
  | (6 | 12 | 14 | 20 | 22 | 28 | 30) ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rt2 = arm_register_op (get_arm_reg (b 11 8)) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let imm8 = 4 * (b 7 0) in
     let imm = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let offset = ARMImmOffset imm8 in
     let offset2 = ARMImmOffset (imm8 + 4) in
     let (isadd, isindex, iswback) =
       match selector with
       | 6 -> (false, false, true)
       | 12 -> (false, true, false)
       | 14 -> (false, true, true)
       | 20 -> (true, false, false)
       | 22 -> (true, false, true)
       | 28 -> (true, true, false)
       | 30 -> (true, true, true)
       | _ ->
          raise
            (BCH_failure
             (LBLOCK [STR "Unexpected value in parse_thumb32_29_0:STRD"])) in
     let mem =
       mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     let mem2 =
       mk_arm_offset_address_op rnreg offset2 ~isadd ~isindex ~iswback in
     (* STRD<c> <Rt>, <Rt2>, [<Rn>{, #+/-<imm>}] *)
     StoreRegisterDual (cc, rt WR, rt2 WR, rn RD, imm, mem WR, mem2 WR)

  (* < 29>00< 13><rn><15>00000000<rm>   TBB - T1 *)
  | 13 when (b 15 12) = 15 && (b 11 4) = 0 ->
     let rnreg = get_arm_reg (b 19 16) in
     let rmreg = get_arm_reg (b 3 0) in
     let rn = arm_register_op rnreg in
     let rm = arm_register_op rmreg in
     let offset = arm_index_offset rmreg in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* TBB<c> [<Rn>, <Rm>] *)
     TableBranchByte (cc, rn RD, rm RD, mem RD)

  (* < 29>00< 13><rn><15>00000001<rm>   TBH - T1 *)
  | 13 when (b 15 12) = 15 && (b 11 4) = 1 ->
     let rnreg = get_arm_reg (b 19 16) in
     let rmreg = get_arm_reg (b 3 0) in
     let rn = arm_register_op rnreg in
     let rm = arm_register_op rmreg in
     let offset = arm_index_offset rmreg in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* TBB<c> [<Rn>, <Rm>] *)
     TableBranchHalfword (cc, rn RD, rm RD, mem RD)

  (* < 29>00PU1W1<rn><rt><t2><-imm8->   LDRD (immediate/literal) - T1 *)
  | (7 | 13 | 15 | 21 | 23 | 29 | 31) ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rt2 = arm_register_op (get_arm_reg (b 11 8)) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let imm8 = 4 * (b 7 0) in
     let imm = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let offset = ARMImmOffset imm8 in
     let offset2 = ARMImmOffset (imm8 + 4) in
     let (isindex, isadd, iswback) =
       match selector with
       | 7 -> (false, false, true)
       | 13 -> (false, true, false)
       | 15 -> (false, true, true)
       | 21 -> (true, false, false)
       | 23 -> (true, false, true)
       | 29 -> (true, true, false)
       | 31 -> (true, true, true)
       | _ ->
          raise
            (BCH_failure
             (LBLOCK [STR "Unexpected value in parse_thumb32_29_0:LDRD"])) in
     let mem =
       mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     let mem2 =
       mk_arm_offset_address_op rnreg offset2 ~isadd ~isindex ~iswback in
     (* LDRD<c> <Rt>, <Rt2>, [<Rn>{, #+/-<imm>}] *)
     LoadRegisterDual (cc, rt WR, rt2 WR, rn RD, imm, mem WR, mem2 WR)

  (* < 29>00<  4><rn><rt><rd><-imm8->   STREX - T1 *)
  | 4 ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (b 7 0) in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* STREX<c> <Rd>, <Rt>, [<Rn>{, #<imm>}] *)
     StoreRegisterExclusive (cc, rd WR, rt RD, rn RD, mem WR)

  (* < 29>00<  5><rn><rt><15><-imm8->   LDREX - T1 *)
  | 5 when (b 11 8) = 15 ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let imm = (b 7 0) lsl 2 in
     let offset = ARMImmOffset imm in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDREX<c> <Rt>, [<Rn>{, #<imm>}] *)
     LoadRegisterExclusive (cc, rt WR, rn RD, immop, mem RD)

  (* < 29>00010W0<rn>0m0<---rlist--->   STM/STMIA/STMEA - T2 *)
  | 8 | 10 when (bv 15) = 0 && (bv 13) = 0 ->
     let regs = ((bv 14) lsl 14) + (b 12 0) in
     let reglist = get_reglist_from_int 16 regs in
     let rl = arm_register_list_op reglist in
     let rnreg = get_arm_reg (b 19 16) in
     let mem = mk_arm_mem_multiple_op rnreg (List.length reglist) in
     let rn = arm_register_op rnreg in
     let wback = (bv 21) = 1 in
     let rn = if wback then rn RW else rn RD in
     (* STM<c>.W <Rn>{!}, <registers> *)
     StoreMultipleIncrementAfter (wback, cc, rn, rl RD , mem WR, true)

  (* < 29>00< 11><13>pm0<---rlist--->   POP.W - T2 *)
  | 11 when (b 19 16) = 13 && (bv 13) = 0 ->
     let reglist = get_reglist_from_int 16 (b 15 0) in
     let rl = arm_register_list_op reglist in
     let sp = arm_register_op (get_arm_reg 13) in
     (* POP<c>.W <registers> *)
     Pop (cc, sp RW, rl WR, true)

  (* < 29>00010W1<rn>0m0<---rlist--->   LDM/LDMIA/LDMFD - T2 *)
  | 9 | 11 when (bv 15) = 0 && (bv 13) = 0 ->
     let regs = ((b 14 14) lsl 14) + (b 12 0) in
     let reglist = get_reglist_from_int 16 regs in
     let rl = arm_register_list_op reglist in
     let rnreg = get_arm_reg (b 19 16) in
     let mem = mk_arm_mem_multiple_op rnreg (List.length reglist) in
     let rn = arm_register_op rnreg in
     let wback = (bv 21) = 1 in
     let rn = if wback then rn RW else rn RD in
     (* LDM<c>.W <Rn>{!}, <registers> *)
     LoadMultipleIncrementAfter (wback, cc, rn, rl RD , mem WR)

  (* < 29>00< 18><13>0M0<---rlist--->   PUSH.W - T2 *)
  | 18 when (bv 15) = 0 && (bv 13) = 0 ->
     let reglist = get_reglist_from_int 16 (b 15 0) in
     let rl = arm_register_list_op reglist in
     let sp = arm_register_op (get_arm_reg 13) in
     (* PUSH<c>.W <registers> *)
     Push (cc, sp RW, rl RD, true)

  (* < 29>00100W0<rn>0m0<---rlist--->   STMDB/STMFD - T1 *)
  | 16 | 18 when (bv 15) = 0 && (bv 13) = 0 ->
     let regs = ((bv 14) lsl 14) + (b 12 0) in
     let reglist = get_reglist_from_int 16 regs in
     let rl = arm_register_list_op reglist in
     let rnreg = get_arm_reg (b 19 16) in
     let mem = mk_arm_mem_multiple_op rnreg (List.length reglist) in
     let rn = arm_register_op rnreg in
     let wback = (b 21 21) = 1 in
     let rn = if wback then rn RW else rn RD in
     (* STM<c>.W <Rn>{!}, <registers> *)
     StoreMultipleDecrementBefore (wback, cc, rn, rl RD , mem WR)

  | selector ->
     NotRecognized (
         "parse_thumb32_29_0:" ^ (string_of_int selector), instr)


let parse_thumb32_29_1
      ?(_in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (_ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let setflags = (bv 20) = 1 in
  let mk_imm5 i3 i2 = (i3 lsl 2) + i2 in
  let mk_imm_shift_reg reg ty imm =
    mk_arm_imm_shifted_register_op reg ty imm in
  let selector = b 24 21 in
  let b15 = bv 15 in
  match (selector, b15) with

  (* < 29>01< 0>S<rn>0<i><rd>i2ty<rm>   AND (register) - T2 *)
  | (0, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* AND{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseAnd (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 29>01< 1>S<rn>0<i><rd>i2ty<rm>   BIC (register) - T2 *)
  | (1, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* BIC{S}<c>.W <Rd>, <Rn>, <Rm>{, <shifht>} *)
     BitwiseBitClear (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 29>01< 2>S<15>< 0><rd>0000<rm>   MOV (register) - T3 *)
  | (2, 0) when (b 19 16) = 15 && (b 14 12) = 0 && (b 7 4) = 0 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* MOV{S}<c>.W <Rd>, <Rm> *)
     Move (setflags, cc, rd WR, rm RD, true, false)

  (* < 29>01< 2>S<15>0<i><rd>i200<rm>   LSL (immediate) - T2 *)
  | (2, 0) when (b 19 16) = 15 && (b 5 4) = 0 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     let imm = ((b 14 12) lsl 2) + (b 7 6) in
     let (_, shift_n) = decode_imm_shift 1 imm in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "LSL(T2) at "; iaddr#toPretty]))
         (mk_arm_immediate_op false 4 (mkNumerical shift_n)) in
     (* LSL{S}<c>.W <Rd>, <Rm>, #<imm> *)
     LogicalShiftLeft (setflags, cc, rd WR, rm RD, imm, true)

  (* < 29>01< 2>S<15>0<i><rd>i201<rm>   LSR (immediate) - T2 *)
  | (2, 0) when (b 19 16) = 15 && (b 5 4) = 1 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     let imm = ((b 14 12) lsl 2) + (b 7 6) in
     let (_, shift_n) = decode_imm_shift 1 imm in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "LSR(T2) at "; iaddr#toPretty]))
         (mk_arm_immediate_op false 4 (mkNumerical shift_n)) in
     (* LSR{S}<c>.W <Rd>, <Rm>, #<imm> *)
     LogicalShiftRight (setflags, cc, rd WR, rm RD, imm, true)

  (* < 29>01< 2>S<15>0<i><rd>i210<rm>   ASR (immediate) - T2 *)
  | (2, 0) when (b 19 16) = 15 && (b 5 4) = 2 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     let imm = ((b 14 12) lsl 2) + (b 7 6) in
     let (_, shift_n) = decode_imm_shift 2 imm in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "ASR(T2) at "; iaddr#toPretty]))
         (mk_arm_immediate_op false 4 (mkNumerical shift_n)) in
     (* ASR{S}<c>.W <Rd>, <Rm>, #<imm> *)
     ArithmeticShiftRight (setflags, cc, rd WR, rm RD, imm, true)

  (* < 29>01< 2>S<rn>0<i><rd>i2ty<rm>   ORR (register) - T2 *)
  | (2, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* ORR{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseOr (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 29>01< 3>S<15>0<i><rd>i2ty<rm>   MVN.W (register) - T2 *)
  | (3, 0) when (b 19 16) = 15 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* MVN{S}<c>.W <Rd>, <Rm>{, <shift>} *)
     BitwiseNot (setflags, cc, rd WR, rm RD, true)

  (* < 29>01< 3>S<rn>0<i><rd>i2ty<rm>   ORN (register) - T1 *)
  | (3, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* ORN{S}<c> <Rd>, <Rn>{, <shift>} *)
     BitwiseOrNot (setflags, cc, rd WR, rn RD, rm RD)

  (* < 29>01< 4>S<rn>0<i><rd>i2ty<rm>   EOR (register) - T2 *)
  | (4, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* EOR{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseExclusiveOr (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 29>01< 8>S<rn>0<i><rd>i2ty<rm>   ADD (register) - T3 *)
  | (8, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     Add (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 29>011010S<rn>0<i><rd>i2ty<rm>   ADC (register) - T2 *)
  | (10, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* ADC{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     AddCarry (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 29>01<11>S<rn>0<i><rd>i2ty<rm>   SBC (register) - T2 *)
  | (11, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* SBC{S}.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     SubtractCarry (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 29>01<13>S<rn>0<i><rd>i2ty<rm>   SUB (register) - T2 *)
  | (13, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* SUB{S}.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     Subtract (setflags, cc, rd WR, rn RD, rm RD, true, false)

  (* < 29>011110S<rn>0<i><rd>i2ty<rm>   RSB (register) - T1 *)
  | (14, 0) ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     (* RSB{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     ReverseSubtract (setflags, cc, rd WR, rn RD, rm RD, false)

  | (selector, _) ->
     NotRecognized (
         "parse_thumb32_29_1:" ^ (string_of_int selector), instr)


let parse_thumb32_29_2
      ?(_in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (_ch: pushback_stream_int)
      (_iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  if (b 11 9) != 5 then
    if (b 24 20) = 5 then
      (* < 29>1000101<r2><rt><cp><op><cm>   MRRC - T1 *)
      let coproc = b 11 8 in
      let opc = b 7 4 in
      let crm = b 3 0 in
      let rt = arm_register_op (get_arm_reg (b 15 12)) in
      let rt2 = arm_register_op (get_arm_reg (b 19 16)) in
      (* MRRC<c> <coproc>, <opc>, <Rt>, <Rt2>, <CRm> *)
      MoveTwoRegisterCoprocessor (cc, coproc, opc, rt WR, rt2 WR, crm)
    else
      let isindex = (bv 24) = 1 in
      let isadd = (bv 23) = 1 in
      let iswback = (bv 21) = 1 in
      let islong = (bv 22) = 1 in
      let crd = b 15 12 in
      let coproc = b 11 8 in
      let imm32 = 4 * (b 7 0) in
      let offset = ARMImmOffset imm32 in
      let rnreg = get_arm_reg (b 19 16) in
      let mem =
        mk_arm_offset_address_op
          ~align:4 rnreg offset ~isadd ~isindex ~iswback in
      if (bv 20) = 0 then
        (* STC{L}<c> <coproc>, <CRd>, [<Rn>, #+/-<imm>]{!} *)
        StoreCoprocessor (islong, true, cc, coproc, crd, mem WR, None)
      else
        (* LDC{L}<c> <coproc>, <CRd>, [<Rn>, #+-<imm>}{!} *)
        LoadCoprocessor (islong, true, cc, coproc, crd, mem RD, None)
  else
    let selector = b 24 23 in
    let isz = b 21 20 in
    let cmode = bv 8 in
    match (selector, isz, cmode) with

    (* VMOV (between two ARM core registers and a dw extension register *)
    (* < 29><4>0100<t2><rt><11>00M1<vm> VMOV -T1-from *)
    | (0, 0, 1) when (bv 22) = 1 && (b 7 6) = 0 && (bv 4) = 1 ->
       let m = prefix_bit (bv 5) (b 3 0) in
       let dm = arm_extension_register_op XDouble m in
       let rtreg = get_arm_reg (b 15 12) in
       let rt2reg = get_arm_reg (b 19 16) in
       let rt = arm_register_op rtreg in
       let rt2 = arm_register_op rt2reg in
       let rtd = arm_double_register_op rtreg rt2reg in
       (* VMOV<c> <Dm>, <Rt>, <Rt2> *)
       VectorMoveDSS (cc, VfpNone, dm WR, rt RD, rt2 RD, rtd RD)

    (* VMOV between two ARM core registers and a doubleword extension register *)
    (* < 29><4>0101<t2><rt><11>00M1<vm> - T1-to *)
    | (0, 1, 1) when (bv 22) = 1 && (b 7 6) = 0 && (bv 4) = 1 ->
       let m = prefix_bit (bv 5) (b 3 0) in
       let dm = arm_extension_register_op XDouble m in
       let rtreg = get_arm_reg (b 15 12) in
       let rt2reg = get_arm_reg (b 19 16) in
       let rt = arm_register_op rtreg in
       let rt2 = arm_register_op rt2reg in
       let rtd = arm_double_register_op rtreg rt2reg in
       (* VMOV<c> <Dm>, <Rt>, <Rt2> *)
       VectorMoveDDS (cc, VfpNone, rt WR, rt2 WR, rtd WR, dm RD)

    (* < 29>10PUDW0<rn><vd><5>0<-imm8->    VSTM - T2 *)
    | (1, 0, 0) ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let imm8 = b 7 0 in
       let rl = arm_extension_register_list_op XSingle d imm8 in
       let mem = mk_arm_mem_multiple_op ~size:4 rnreg imm8 in
       (* VSTM<c> <Rn>, <list> *)
       VectorStoreMultipleIncrementAfter (false, cc, rn RD, rl RD, mem WR)

    (* < 29>10PUDW0<rn><vd><5>0<-imm8->    VSTM - T2-wb *)
    | (1, 2, 0) ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let imm8 = b 7 0 in
       let rl = arm_extension_register_list_op XSingle d imm8 in
       let mem = mk_arm_mem_multiple_op ~size:4 rnreg imm8 in
       (* VSTM<c> <Rn>!, <list> *)
       VectorStoreMultipleIncrementAfter (true, cc, rn RW, rl RD, mem WR)

    (* < 29>10PUDW0<rn><vd><5>1<-imm8->    VSTM - T1 *)
    | (1, 0, 1) when (bv 0) = 0 ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
       (* VSTM<c> <Rn>, <list> *)
       VectorStoreMultipleIncrementAfter (false, cc, rn RD, rl RD, mem WR)

    (* < 29>10PUDW0<rn><vd><5>1<-imm8->    VSTM - T1-wb *)
    | (1, 2, 1) when (bv 0) = 0->
       let d = prefix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
       (* VSTM<c> <Rn>!, <list> *)
       VectorStoreMultipleIncrementAfter (true, cc, rn RW, rl RD, mem WR)

    (* < 29>10PUDW0<rn><vd><5>1<-imm8->    VSTM - T1 *)
    | (1, 0, 1) ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
       (* FSTMIAX<c> <Rn>, <list> *)
       FStoreMultipleIncrementAfter (false, cc, rn RD, rl RD, mem WR)

    (* < 29>10PUDW0<rn><vd><5>1<-imm8->    VSTM - T1-wb *)
    | (1, 2, 1) ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
       (* FSTMIAX<c> <Rn>!, <list> *)
       FStoreMultipleIncrementAfter (true, cc, rn RW, rl RD, mem WR)

    (* < 29>1001D11<13><vd>1010<-imm8->   VPOP - T2 *)
    | (1, 3, 0) when (b 19 16) = 13 ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let spreg = get_arm_reg 13 in
       let sp = arm_register_op spreg in
       let imm8 = b 7 0 in
       let rl = arm_extension_register_list_op XSingle d imm8 in
       let mem = mk_arm_mem_multiple_op ~size:4 spreg imm8 in
       (* VPOP<c> <list> *)
       VectorPop (cc, sp WR, rl WR, mem RD)

    (* < 29>1001D11<13><vd>1011<-imm8->   VPOP - T1 *)
    | (1, 3, 1) when (b 19 16) = 13 && (bv 0) = 0 ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let spreg = get_arm_reg (b 19 16) in
       let sp = arm_register_op spreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 spreg regs in
       (* VPOP<c> <list> *)
       VectorPop (cc, sp WR, rl WR, mem RD)

    (* < 29>10PUDW1<rn><vd><5>0<-imm8->    VLDM - T2 *)
    | (1, 1, 0) ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let imm8 = b 7 0 in
       let rl = arm_extension_register_list_op XSingle d imm8 in
       let mem = mk_arm_mem_multiple_op ~size:4 rnreg imm8 in
       (* VLDM<c> <Rn>, <list> *)
       VectorLoadMultipleIncrementAfter (false, cc, rn RD, rl WR, mem RD)

    (* < 29>10PUDW1<rn><vd><5>0<-imm8->    VLDM - T2-wb *)
    | (1, 3, 0) ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let imm8 = b 7 0 in
       let rl = arm_extension_register_list_op XSingle d imm8 in
       let mem = mk_arm_mem_multiple_op ~size:4 rnreg imm8 in
       (* VLD<c> <Rn>!, <list> *)
       VectorLoadMultipleIncrementAfter (true, cc, rn RW, rl WR, mem RD)

    (* < 29>10PUDW1<rn><vd><5>1<-imm8->    VLDM - T1 *)
    | (1, 1, 1) when (bv 0) = 0 ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
       (* VLDM<c> <Rn>, <list> *)
       VectorLoadMultipleIncrementAfter (false, cc, rn RD, rl WR, mem RD)

    (* < 29>10PUDW1<rn><vd><5>1<-imm8->    VLDM - T1-wb *)
    | (1, 3, 1) when (bv 0) = 0->
       let d = prefix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
       (* VLDM<c> <Rn>!, <list> *)
       VectorLoadMultipleIncrementAfter (true, cc, rn RW, rl WR, mem RD)

    (* < 29>10PUDW1<rn><vd><5>1<-imm8->    FLDMIAX *)
    | (1, 1, 1) ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
       (* FLDMIAX<c> <Rn>, <list> *)
       FLoadMultipleIncrementAfter (false, cc, rn RD, rl WR, mem RD)

    (* < 29>10PUDW1<rn><vd><5>1<-imm8->    FLDMIAX (wb) *)
    | (1, 3, 1) ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs in
       (* FLDMIAX<c> <Rn>!, <list> *)
       FLoadMultipleIncrementAfter (true, cc, rn RW, rl WR, mem RD)

    (* < 29>101UD00<rn><vd>1010<-imm8->   VSTR-sub - T2) *)
    | (2, 0, 0) ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let vd = arm_extension_register_op XSingle d in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let offset = ARMImmOffset (4 * (b 7 0)) in
       let mem =
         mk_arm_offset_address_op
           rnreg offset ~isadd:false ~isindex:true ~iswback:false in
       (* VSTR<c> <Sd>, [<Rn>{, #+/-<imm>}] *)
       VStoreRegister (cc, vd RD, rn RD, mem WR)

    (* < 29>101UD00<rn><vd>1010<-imm8->   VSTR-add - T2) *)
    | (3, 0, 0) ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let vd = arm_extension_register_op XSingle d in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let offset = ARMImmOffset (4 * (b 7 0)) in
       let mem =
         mk_arm_offset_address_op
           rnreg offset ~isadd:true ~isindex:true ~iswback:false in
       (* VSTR<c> <Sd>, [<Rn>{, #+/-<imm>}] *)
       VStoreRegister (cc, vd RD, rn RD, mem WR)

    (* < 29>101UD00<rn><vd>1011<-imm8->   VSTR-sub - T1 *)
    | (2, 0, 1) ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let vd = arm_extension_register_op XDouble d in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let offset = ARMImmOffset (4 * (b 7 0)) in
       let mem =
         mk_arm_offset_address_op
           rnreg offset ~isadd:false ~isindex:true ~iswback:false in
       (* VSTR<c> <Dd>, [<Rn>{, #+/-<imm>}] *)
       VStoreRegister (cc, vd RD, rn RD, mem WR)

    (* < 29>101UD00<rn><vd>1011<-imm8->   VSTR-add - T1 *)
    | (3, 0, 1) ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let vd = arm_extension_register_op XDouble d in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let offset = ARMImmOffset (4 * (b 7 0)) in
       let mem =
         mk_arm_offset_address_op
           rnreg offset ~isadd:true ~isindex:true ~iswback:false in
       (* VSTR<c> <Dd>, [<Rn>{, #+/-<imm>}] *)
       VStoreRegister (cc, vd RD, rn RD, mem WR)

    (* < 29>101UD01<rn><vd>1010<-imm8->   VLDR-sub - T2) *)
    | (2, 1, 0) ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let vd = arm_extension_register_op XSingle d in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let offset = ARMImmOffset (4 * (b 7 0)) in
       let mem =
         mk_arm_offset_address_op
           rnreg offset ~isadd:false ~isindex:true ~iswback:false in
       (* VLDR<c> <Sd>, [<Rn>{, #+/-<imm>}] *)
       VLoadRegister (cc, vd RD, rn RD, mem WR)

    (* < 29>101UD01<rn><vd>1010<-imm8->   VLDR-add - T2) *)
    | (3, 1, 0) ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let vd = arm_extension_register_op XSingle d in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let offset = ARMImmOffset (4 * (b 7 0)) in
       let mem =
         mk_arm_offset_address_op
           rnreg offset ~isadd:true ~isindex:true ~iswback:false in
       (* VLDR<c> <Sd>, [<Rn>{, #+/-<imm>}] *)
       VLoadRegister (cc, vd RD, rn RD, mem WR)

    (* < 29>101UD01<rn><vd>1011<-imm8->   VLDR-sub - T1 *)
    | (2, 1, 1) ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let vd = arm_extension_register_op XDouble d in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let offset = ARMImmOffset (4 * (b 7 0)) in
       let mem =
         mk_arm_offset_address_op
           rnreg offset ~isadd:false ~isindex:true ~iswback:false in
       (* VLDR<c> <Dd>, [<Rn>{, #+/-<imm>}] *)
       VLoadRegister (cc, vd RD, rn RD, mem WR)

    (* < 29>101UD01<rn><vd>1011<-imm8->   VLDR-add - T1 *)
    | (3, 1, 1) ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let vd = arm_extension_register_op XDouble d in
       let rnreg = get_arm_reg (b 19 16) in
       let rn = arm_register_op rnreg in
       let offset = ARMImmOffset (4 * (b 7 0)) in
       let mem =
         mk_arm_offset_address_op
           rnreg offset ~isadd:true ~isindex:true ~iswback:false in
       (* VLDR<c> <Dd>, [<Rn>{, #+/-<imm>}] *)
       VLoadRegister (cc, vd RD, rn RD, mem WR)

    (* < 29>1010D101101<vd>1010<-imm8->    VPUSH - T2 *)
    | (2, 2, 0) when (b 19 16) = 13 ->
       let d = postfix_bit (bv 22) (b 15 12) in
       let spreg = get_arm_reg 13 in
       let sp = arm_register_op spreg in
       let regs = b 7 0 in
       let rl = arm_extension_register_list_op XSingle d regs in
       let mem = mk_arm_mem_multiple_op ~size:4 spreg regs in
       (* VPUSH<c> <list> *)
       VectorPush (cc, sp WR, rl RD, mem WR)

    (* < 29>1010D101101<vd>1011<-imm8->    VPUSH - T1 *)
    | (2, 2, 1) when (b 19 16) = 13 && (bv 0) = 0 ->
       let d = prefix_bit (bv 22) (b 15 12) in
       let spreg = get_arm_reg 13 in
       let sp = arm_register_op spreg in
       let regs = (b 7 0) / 2 in
       let rl = arm_extension_register_list_op XDouble d regs in
       let mem = mk_arm_mem_multiple_op ~size:8 spreg regs in
       (* VPUSH<c> <list> *)
       VectorPush (cc, sp WR, rl RD, mem WR)

    | (selector, isz, cmode) ->
       NotRecognized (
           "parse_thumb32_29_2: "
           ^ (string_of_int selector)
           ^ "_"
           ^ (string_of_int isz)
           ^ "_"
           ^ (string_of_int cmode),
           instr)


let parse_thumb32_29_12
      ?(_in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (_ch: pushback_stream_int)
      (_iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let isz = b 21 20 in
  let cmode = bv 8 in
  let q = bv 6 in
  let b4 = bv 4 in
  match (isz, cmode, q, b4) with

  (* VMOV (between ARM core register and single-precision register *)
  (* < 29><12>00o<vn><rt>1010N001< 0>  VMOV - T1-from *)
  | (0, 0, 0, 1) when (bv 22) = 0 && (bv 5) = 0 && (b 3 0) = 0 ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let vn = arm_extension_register_op XSingle n in
     (* VMOV<c> <Sn>, <Rt> *)
     VectorMoveDS (cc, VfpNone, vn WR, rt RD)

  (* VMOV (between ARM core register and single-precision register *)
  (* < 29><12>00o<vn><rt>1010N001< 0>  VMOV - T1-to *)
  | (1, 0, 0, 1) when (bv 22) = 0 && (bv 5) = 0 && (b 3 0) = 0 ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let vn = arm_extension_register_op XSingle n in
     (* VMOV<c> <Rt>, <Sn> *)
     VectorMoveDS (cc, VfpNone, vn WR, rt RD)

  (* < 29><12>D00<vn><vd><5>0N0M0<vm>  VMLA (floating-point) - T2-single *)
  | (0, 0, 0, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VMLA<v>.F32 <Sd>, <Sn>, <Sm> *)
     VectorMultiplyAccumulate (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D00<vn><vd><5>1N0M0<vm>  VMLA (floating-point) - T2-double *)
  | (0, 1, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VMLA<v>.F64 <Dd>, <Dn>, <Dm> *)
     VectorMultiplyAccumulate (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D00<vn><vd><5>0N1M0<vm>  VMLS (floating-point) - T2-single *)
  | (0, 0, 1, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VMLS<v>.F32 <Sd>, <Sn>, <Sm> *)
     VectorMultiplySubtract (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D00<vn><vd><5>1N1M0<vm>  VMLS (floating-point) - T2-double *)
  | (0, 1, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VMLS<v>.F64 <Dd>, <Dn>, <Dm> *)
     VectorMultiplySubtract (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D01<vn><vd><5>0N0M0<vm>  VNMLS - T2-single *)
  | (1, 0, 0, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VNMLS<v>.F32 <Sd>, <Sn>, <Sm> *)
     VectorNegateMultiplySubtract (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D01<vn><vd><5>1N0M0<vm>  VNMLS - T2-double *)
  | (1, 1, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VNMLS<v>.F64 <Dd>, <Dn>, <Dm> *)
     VectorNegateMultiplySubtract (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D01<vn><vd><5>0N1M0<vm>  VNMLA - T2-single *)
  | (1, 0, 1, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VNMLA<v>.F32 <Sd>, <Sn>, <Sm> *)
     VectorNegateMultiplyAccumulate (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D01<vn><vd><5>1N1M0<vm>  VNMLA - T2-double *)
  | (1, 1, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VNMLA<v>.F64 <Dd>, <Dn>, <Dm> *)
     VectorNegateMultiplyAccumulate (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D10<vn><vd><5>0N0M0<vm>  VMUL (floating point) - T2-single *)
  | (2, 0, 0, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VMUL<v>.F32 <Sd>, <Sn>, <Sm> *)
     VectorMultiply (cc, dt, vd WR, vn RD, vm RD)

(* < 29><12>D10<vn><vd><5>1N0M0<vm>  VMUL (floating point) - T2-double *)
  | (2, 1, 0 ,0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VMUL<v>.F64 <Dd>, <Dn>, <Dm> *)
     VectorMultiply (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D10<vn><vd><5>0N1M0<vm>  VNMUL - T2-single *)
  | (2, 0, 1, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VNMUL<v>.F32 <Sd>, <Sn>, <Sm> *)
     VectorNegateMultiply (cc, dt, vd WR, vn RD, vm RD)

(* < 29><12>D10<vn><vd><5>1N0M0<vm>  VNMUL - T2-double *)
  | (2, 1, 1 ,0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VNMUL<v>.F64 <Dd>, <Dn>, <Dm> *)
     VectorNegateMultiply (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D11<vn><vd><10>N0M0<vm>  VADD (floating point) - T2-single *)
  | (3, 0, 0, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VADD<v>.F32 <Sd>, <Sn>, <Sm> *)
     VectorAdd (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D11<vn><vd><11>N1M0<vm>  VADD (floating point) - T2-double *)
  | (3, 1, 0 ,0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VADD<v>.F64 <Dd>, <Dn>, <Dm> *)
     VectorAdd (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D11<vn><vd><5>0N1M0<vm>  VSUB (floating point) - T2-single *)
  | (3, 0, 1, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VSUB<v>.F32 <Sd>, <Sn>, <Sm> *)
     VectorSubtract (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><12>D11<vn><vd><5>1N1M0<vm>  VSUB (floating point) - T2-double *)
  | (3, 1, 1 ,0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VSUB<v>.F64 <Dd>, <Dn>, <Dm> *)
     VectorSubtract (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><6>01o0<vd><rt><11>Doo1< 0>  VMOV (ARM core to scalar: 1xxx) *)
  | ((0 | 2), 1, _, 1) when (bv 22) = 1 ->
     let esize = 8 in
     let index = ((bv 21) lsl 2) + (b 6 5) in
     let d = prefix_bit (bv 7) (b 19 16) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let dt = VfpSize esize in
     let elt = arm_extension_register_element_op XDouble d index esize in
     (* VMOV<c>.<size> <Dd[x], <Rt> *)
     VectorMoveDS (cc, dt, elt WR, rt RD)

  (* < 29><6>01o0<vd><rt><11>Doo1< 0>  VMOV (ARM core to scalar: 0xx1) *)
  | ((0 | 2), 1, _, 1) when (bv 22) = 0 && (bv 5) = 1 ->
     let esize = 16 in
     let index = ((bv 21) lsl 1) + (bv 6) in
     let d = prefix_bit (bv 7) (b 19 16) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let dt = VfpSize esize in
     let elt = arm_extension_register_element_op XDouble d index esize in
     (* VMOV<c>.<size> <Dd[x], <Rt> *)
     VectorMoveDS (cc, dt, elt WR, rt RD)

  (* < 29><6>01o0<vd><rt><11>Doo1< 0>  VMOV (ARM core to scalar: 0x00) *)
  | ((0 | 2), 1,  0, 1) when (bv 22) = 0 && (bv 5) = 0 ->
     let esize = 32 in
     let index = bv 21 in
     let d = prefix_bit (bv 7) (b 19 16) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let dt = VfpSize esize in
     let elt = arm_extension_register_element_op XDouble d index esize in
     (* VMOV<c>.<size> <Dd[x], <Rt> *)
     VectorMoveDS (cc, dt, elt WR, rt RD)

  | (a, b, c, d) ->
     NotRecognized (
         "parse_thumb32_29_12:"
         ^ (string_of_int a)
         ^ "_"
         ^ (string_of_int b)
         ^ "_"
         ^ (string_of_int c)
         ^ "_"
         ^ (string_of_int d),
         instr)


let parse_thumb32_29_13
      ?(_in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (_ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let isz = b 21 20 in
  let cmode = bv 8 in
  let q = bv 6 in
  let b4 = bv 4 in
  let imm0_op = arm_immediate_op imm0 in
  let mk_fbits (size: int) =
    let i4 = b 3 0 in
    let fracbits = size - ((2 * i4) + (bv 5)) in
    if fracbits < 0 then
      raise
        (ARM_undefined
           ("VCVT: fracbits is negative: " ^ (string_of_int fracbits)))
    else
      TR.tget_ok (mk_arm_immediate_op true 4 (mkNumerical fracbits)) in
  match (isz, cmode, q, b4) with

  (* < 29><13>110< 1><rt><5>00001< 0>   VMSR - T1 *)
  | (2, 0, 0, 1) when (bv 22) = 1 && (b 19 16) = 1 && (bv 7) = 0 && (bv 5) = 0 ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let dst = arm_special_register_op FPSCR in
     (* VMSR<c> FPSCR, <Rt> *)
     VMoveToSystemRegister (cc, dst WR, rt RD)

  (* < 29>1101111< 1><15>< 5>00001< 0>   VMRS - T1 *)
  | (3, 0, 0, 1) when (bv 22) = 1 && (b 19 16) = 1 && (bv 7) = 0 && (bv 5) = 0 ->
     let src = arm_special_register_op FPSCR in
     if (b 15 12) = 15 then
       let dst = arm_special_register_op APSR_nzcv in
       (* VMRS<c> <PC>, FPSCR *)
       VMoveRegisterStatus (cc, dst WR, src RD)
     else
       let dst = arm_register_op (get_arm_reg (b 15 12)) in
       (* VMRS<c> <Rt>, FPSCR *)
       VMoveRegisterStatus (cc, dst WR, src RD)

  (* < 29><13>BQ0<vd><rt><5>1D0E1< 0>   VDUP (ARM core register) - T1 (Q=0) *)
  | (0, 1, 0, 1) ->
     let d = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XDouble d in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let be = ((bv 22) lsl 1) + (bv 5) in
     let (esize, elts) =
       match be with
       | 0 -> (32, 2)
       | 1 -> (16, 4)
       | 2 -> (8, 8)
       | _ ->
          raise (ARM_undefined ("VDUP:(B:E) = " ^ (string_of_int be))) in
     let dt = VfpSize esize in
     (* VDUP)<v>.<size> <Dd>, <Rt> *)
     VectorDuplicate (cc, dt, 1, elts, vd WR, rt RD)

  (* < 29><13>BQ0<vd><rt><5>1D0E1< 0>   VDUP (ARM core register) - T1 (Q=1) *)
  | (2, 1, 0, 1) ->
     let d = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let be = ((bv 22) lsl 1) + (bv 5) in
     let (esize, elts) =
       match be with
       | 0 -> (32, 2)
       | 1 -> (16, 4)
       | 2 -> (8, 8)
       | _ ->
          raise (ARM_undefined ("VDUP:(B:E) = " ^ (string_of_int be))) in
     let dt = VfpSize esize in
     (* VDUP)<v>.<size> <Qd>, <Rt> *)
     VectorDuplicate (cc, dt, 2, elts, vd WR, rt RD)

  (* < 29><13>D00<vn><vd><5>0N0M0<vm>  VDIV (floating point) - T1-single *)
  | (0, 0, 0, 0) ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let n = postfix_bit (bv 7) (b 19 16) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vn = arm_extension_register_op XSingle n in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VDIV<c>.F32 <Sd>, <Sn>, <Sm> *)
     VDivide (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><13>D00<vn><vd><5>1N0M0<vm>  VDIV (floating point) - T1-double *)
  | (0, 1, 0 ,0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VDIV<c>.F64 <Dd>, <Dn>, <Dm> *)
     VDivide (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><13>D10<vn><vd><5>1N0M0<vm>  VFMA (floating point) - T2-double *)
  | (2, 1, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VFMA<c>.F64 <Dd>, <Dn>, <Dm> *)
     VectorFusedMultiplyAccumulate (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><13>D11<i4><vd><5>00000<i4>   VMOV (immediate) T2-single *)
  | (3, 0, 0, 0) when (bv 7) = 0 && (bv 5) = 0 ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XSingle d in
     let imm8 = ((b 19 16) lsl 4) + (b 3 0) in
     let vfp = vfp_expand_imm imm8 32 in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VMOV(T2-single) at "; iaddr#toPretty]))
         (mk_arm_immediate_op false 4 vfp) in
     let dt = VfpFloat 32 in
     (* VMOV<c>.F32 <Sd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, imm)

  (* < 29><13>D11<i4><vd><5>10000<i4>   VMOV (immediate) T2-double *)
  | (3, 1, 0, 0) when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let vd = arm_extension_register_op XDouble d in
     let imm8 = ((b 19 16) lsl 4) + (b 3 0) in
     let vfp = vfp_expand_imm imm8 64 in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VMOV(T2-double) at "; iaddr#toPretty]))
         (mk_arm_immediate_op false 8 vfp) in
     let dt = VfpFloat 64 in
     (* VMOV<c>.F64 <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, imm)

  (* < 29><6>1D11< 0><vd><10>01M0<vm>  VMOV (register) -T2-single *)
  | (3, 0, 1, 0) when (b 19 16) = 0 && (bv 7) = 0 ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VMOV<c>.F32 <Sd>, <Sm> *)
     VectorMoveDS (cc, dt, vd WR, vm RD)

  (* < 29><6>1D11< 0><vd<11>01M0<vm>  VMOV (register) -T2-double *)
  | (3, 1, 1, 0) when (b 19 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VMOV<c>.F64 <Dd>, <Dm> *)
     VectorMoveDS (cc, dt, vd WR, vm RD)

  (* < 29><6>1D11< 0><vd><10>11M0<vm>   VABS - T2-single *)
  | (3, 0, 1, 0) when (b 19 16) = 0 && (bv 7) = 1 ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VABS<c>.F32 <Sd>, <Sm> *)
     VectorAbsolute (cc, dt, vd WR, vm RD)

  (* < 29><6>1D11< 0><vd><11>11M0<vm>   VABS - T2-double *)
  | (3, 1, 1, 0) when (b 19 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VABS<c>.F64 <Dd>, <Dm> *)
     VectorAbsolute (cc, dt, vd WR, vm RD)

  (* < 29><13>D11< 1><vd><5>001M0<vm>  VNEG - T2-single *)
  | (3, 0, 1, 0) when (b 19 16) = 1 && (bv 7) = 0 ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XSingle d in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VNEG<c>.F32 <Sd>, <Sm> *)
     VectorNegate (cc, dt, vd WR, vm RD)

  (* < 29><13>D11< 1><vd<5>101M0<vm>  VNEG -T2-double *)
  | (3, 1, 1, 0) when (b 19 16) = 1 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VNEG<c>.F64 <Dd>, <Dm> *)
     VectorNegate (cc, dt, vd WR, vm RD)

  (* < 29><13>D11< 4><vd><5>0<E1M0<vm>   VCMP{E} - T1-single *)
  | (3, 0, 1, 0) when (b 19 16) = 4 ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let m = postfix_bit (bv 5) (b 3 0) in
     let fdst = arm_special_register_op FPSCR in
     let vd = arm_extension_register_op XSingle d in
     let vm = arm_extension_register_op XSingle m in
     let dt = VfpFloat 32 in
     (* VCMP{E}<c>.F32 <Sd>, <Sm> *)
     VCompare ((bv 7) = 1, cc, dt, fdst WR, vd RD, vm RD)

  (* < 29><13>D11< 4><vd><5>0<E1M0<vm>   VCMP{E} - T1-double *)
  | (3, 1, 1, 0) when (b 19 16) = 4 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let fdst = arm_special_register_op FPSCR in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpFloat 64 in
     (* VCMP{E}<c>.F64 <Dd>, <Dm> *)
     VCompare ((bv 7) = 1, cc, dt, fdst WR, vd RD, vm RD)

  (* < 29><13>D11< 5><vd><5>0<E100< 0>  VCMP{E} - T2-single *)
  | (3, 0, 1, 0) when (b 19 16) = 5 ->
     let d = postfix_bit (bv 22) (b 15 12) in
     let fdst = arm_special_register_op FPSCR in
     let vd = arm_extension_register_op XSingle d in
     let zero = arm_fp_constant_op 0.0 in
     let dt = VfpFloat 32 in
     (* VCMP{E}<c>.F32 <Sd>, #0.0 *)
     VCompare ((bv 7) = 1, cc, dt, fdst WR, vd RD, zero)

  (* < 29><13>D11< 5><vd><5>0<E100< 0>  VCMP{E} - T2-double *)
  | (3, 1, 1, 0) when (b 19 16) = 5 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let fdst = arm_special_register_op FPSCR in
     let vd = arm_extension_register_op XDouble d in
     let zero = arm_fp_constant_op 0.0 in
     let dt = VfpFloat 64 in
     (* VCMP{E}<c>.F64 <Dd>, #0.0 *)
     VCompare ((bv 7) = 1, cc, dt, fdst WR, vd RD, zero)

  (* The various VCVT forms *)
  | (3, (0 | 1), 1, 0) ->
     (match (cmode, b 19 16) with

      (* VCVT between double-precision and single-precision *)
      (* < 29><13>D11< 7><vd><5>011M0<vm> VCVT - T1-sd *)
      | (0, 7) when (bv 7 = 1) ->
         let d = prefix_bit (bv 22) (b 15 12) in
         let m = postfix_bit (bv 5) (b 3 0) in
         let vd = arm_extension_register_op XDouble d in
         let vm = arm_extension_register_op XSingle m in
         let dtd = VfpFloat 64 in
         let dtm = VfpFloat 32 in
         (* VCVT<c>.F64.F32 <Dd>, <Sm> *)
         VectorConvert (false, false, cc, dtd, dtm, vd WR, vm RD, imm0_op)

      (* VCVT between double-precision and single-precision *)
      (* < 29><13>D11< 7><vd><5>111M0<vm> VCVT - T1-ds *)
      | (1, 7) when (bv 7 = 1) ->
         let d = postfix_bit (bv 22) (b 15 12) in
         let m = prefix_bit (bv 5) (b 3 0) in
         let vd = arm_extension_register_op XSingle d in
         let vm = arm_extension_register_op XDouble m in
         let dtd = VfpFloat 32 in
         let dtm = VfpFloat 64 in
         (* VCVT<c>.F32.F64 <Dd>, <Sm> *)
         VectorConvert (false, false, cc, dtd, dtm, vd WR, vm RD, imm0_op)

      (* VCVT between floating-point and integer *)
      (* < 29><13>D11< 8><vd><5>0o1M0<vm>  VCVT - T1-single-from *)
      | (0, 8) ->
         let d = postfix_bit (bv 22) (b 15 12) in
         let m = postfix_bit (bv 5) (b 3 0) in
         let vd = arm_extension_register_op XSingle d in
         let vm = arm_extension_register_op XSingle m in
         let dtd = VfpFloat 32 in
         let dtm = if (bv 7) = 0 then VfpUnsignedInt 32 else VfpSignedInt 32 in
         (* VCVT<c>.F32.U32 <Sd>, <Sm>  (op=0) *)
         (* VCVT<c>.F32.S32 <Sd>, <Sm>  (op=1) *)
         VectorConvert (false, false, cc, dtd, dtm, vd WR, vm RD, imm0_op)

      (* VCVT between floating-point and integer *)
      (* < 29><13>D11< 8><vd><5>1o1M0<vm>  VCVT - T1-double-from *)
      | (1, 8) ->
         let d = prefix_bit (bv 22) (b 15 12) in
         let m = postfix_bit (bv 5) (b 3 0) in
         let vd = arm_extension_register_op XDouble d in
         let vm = arm_extension_register_op XSingle m in
         let dtd = VfpFloat 64 in
         let dtm = if (bv 7) = 0 then VfpUnsignedInt 32 else VfpSignedInt 32 in
         (* VCVT<c>.F64.U32 <Dd>, <Sm>  (op=0) *)
         (* VCVT<c>.F64.S32 <Dd>, <Sm>  (op=1) *)
         VectorConvert (false, false, cc, dtd, dtm, vd WR, vm RD, imm0_op)

      (* VCVT between float-point and fixed-point *)
      (* < 29><6>1D11<10><vd><10>s1i0<i4>   VCVT - T1-single-to-float-s (op=0, u=0) *)
      | (0, 10) ->
         let size = 16 in
         let fbits = mk_fbits size in
         let d = prefix_bit (bv 22) (b 15 12) in
         let vd = arm_extension_register_op XSingle d in
         let dtd = VfpFloat 32 in
         let dtm = VfpSignedInt 16 in
         VectorConvert (false, true, cc, dtd, dtm, vd WR, vd RD, fbits)

      (* VCVT between float-point and fixed-point *)
      (* < 29><6>1D11<10><vd><11>s1i0<i4>   VCVT - T1-double-to-float-s (op=0, u=0) *)
      | (1, 10) ->
         let size = 32 in
         let fbits = mk_fbits size in
         let d = prefix_bit (bv 22) (b 15 12) in
         let vd = arm_extension_register_op XDouble d in
         let dtd = VfpFloat 64 in
         let dtm = VfpSignedInt 32 in
         VectorConvert (false, true, cc, dtd, dtm, vd WR, vd RD, fbits)

      (* VCVT between float-point and fixed-point *)
      (* < 29><6>1D11<10><vd><10>s1i0<i4>   VCVT - T1-single-to-float-s (op=0, u=0) *)
      | (0, 11) ->
         let size = 16 in
         let fbits = mk_fbits size in
         let d = prefix_bit (bv 22) (b 15 12) in
         let vd = arm_extension_register_op XSingle d in
         let dtd = VfpFloat 32 in
         let dtm = VfpUnsignedInt 16 in
         VectorConvert (false, true, cc, dtd, dtm, vd WR, vd RD, fbits)

      (* VCVT between float-point and fixed-point *)
      (* < 29><6>1D11<10><vd><11>s1i0<i4>   VCVT - T1-double-to-float-s (op=0, u=0) *)
      | (1, 11) ->
         let size = 32 in
         let fbits = mk_fbits size in
         let d = prefix_bit (bv 22) (b 15 12) in
         let vd = arm_extension_register_op XDouble d in
         let dtd = VfpFloat 64 in
         let dtm = VfpUnsignedInt 32 in
         VectorConvert (false, true, cc, dtd, dtm, vd WR, vd RD, fbits)

      (* VCVT between floating-point and integer *)
      (* < 29><13>D11<12><vd><5>0o1M0<vm>  VCVT - T1-single-to-u *)
      | (0, 12) ->
         let d = postfix_bit (bv 22) (b 15 12) in
         let m = postfix_bit (bv 5) (b 3 0) in
         let vd = arm_extension_register_op XSingle d in
         let vm = arm_extension_register_op XSingle m in
         let dtd = VfpUnsignedInt 32 in
         let dtm = VfpFloat 32 in
         (* VCVT<c>.U32.F32 <Sd>, <Sm> *)
         VectorConvert ((bv 7) = 1, false, cc, dtd, dtm, vd WR, vm RD, imm0_op)

      (* VCVT between floating-point and integer *)
      (* < 29><13>D11<12><vd><5>1o1M0<vm>  VCVT - T1-double-to-u *)
      | (1, 12) ->
         let d = postfix_bit (bv 22) (b 15 12) in
         let m = prefix_bit (bv 5) (b 3 0) in
         let vd = arm_extension_register_op XSingle d in
         let vm = arm_extension_register_op XDouble m in
         let dtd = VfpUnsignedInt 32 in
         let dtm = VfpFloat 64 in
         (* VCVT<c>.U32.F64 <Sd>, <Dm> *)
         VectorConvert ((bv 7) = 1, false, cc, dtd, dtm, vd WR, vm RD, imm0_op)

      (* VCVT between floating-point and integer *)
      (* < 29><13>D11<13><vd><5>0o1M0<vm>  VCVT - T1-single-to-s *)
      | (0, 13) ->
         let d = postfix_bit (bv 22) (b 15 12) in
         let m = postfix_bit (bv 5) (b 3 0) in
         let vd = arm_extension_register_op XSingle d in
         let vm = arm_extension_register_op XSingle m in
         let dtd = VfpSignedInt 32 in
         let dtm = VfpFloat 32 in
         (* VCVT<c>.S32.F32 <Sd>, <Sm> *)
         VectorConvert ((bv 7) = 1, false, cc, dtd, dtm, vd WR, vm RD, imm0_op)

      (* VCVT between floating-point and integer *)
      (* < 29><13>D11<13><vd><5>1o1M0<vm>  VCVT - T1-double-to-s *)
      | (1, 13) ->
         let d = postfix_bit (bv 22) (b 15 12) in
         let m = prefix_bit (bv 5) (b 3 0) in
         let vd = arm_extension_register_op XSingle d in
         let vm = arm_extension_register_op XDouble m in
         let dtd = VfpSignedInt 32 in
         let dtm = VfpFloat 64 in
         (* VCVT<c>.S32.F64 <Sd>, <Dm> *)
         VectorConvert ((bv 7) = 1, false, cc, dtd, dtm, vd WR, vm RD, imm0_op)

      | (a, b) ->
         NotRecognized (
             "parse_thumb32_29_13:3_0|1_1_0:"
             ^ (string_of_int a)
             ^ "_"
             ^ (string_of_int b),
             instr)
     )
  | (a, b, c, d) ->
     NotRecognized (
         "parse_thumb32_29_13:"
         ^ (string_of_int a)
         ^ "_"
         ^ (string_of_int b)
         ^ "_"
         ^ (string_of_int c)
         ^ "_"
         ^ (string_of_int d),
         instr)


let parse_thumb32_29_110
      ?(in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in

  if (bv 24) = 0 && (bv 20) = 1 && (b 11 9) != 5 && (bv 4) = 1 then
    (* < 29>110<1>1<cn><rt><co><2>1<cm>   MRC - T1 *)
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let opc1 = b 23 21 in
     let crn = b 19 16 in
     let coproc = b 11 8 in
     let opc2 = b 7 5 in
     let crm = b 3 0 in
     (* MRC<c> <coproc>, <opc1>, <Rt>, <CRn>, <CRm>, <opc2> *)
     MoveRegisterCoprocessor (cc, coproc, opc1, rt WR, crn, crm, opc2)

  else
    if (bv 23) = 0 then
      parse_thumb32_29_12 ~_in_it:in_it ~cc ch iaddr instr
    else
      parse_thumb32_29_13 ~_in_it:in_it ~cc ch iaddr instr


let parse_thumb32_29_14
      ?(_in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (_ch: pushback_stream_int)
      (_iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let isz = b 21 20 in
  let cmode = b 11 8 in
  let q = bv 6 in
  let b4 = bv 4 in
  match (isz, cmode, q, b4) with

  (* < 29><14>D00<vn><vd>0001NQM1<vm>    VAND (register) - T1 (Q=0) *)
  | (0, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     (* VAND<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseAnd (cc, vd WR, vn RD, vm RD)

  (* < 29><14>D00<vn><vd>0001NQM1<vm>    VAND (register) - T1 (Q=1) *)
  | (0, 1, 1, 1) ->
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

  (* < 29><14>D00<vn><vd><12>NQM0<vm> *) (* SHA1C - T1 *)
  | (0, 12, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1C.32 <Qd>, <Qn>, <Qm> *)
     SHA1HashUpdateChoose (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><14>D01<vm><vd>< 1>NQM1<vm> *)  (* VBIC (register - T1 (Q=0) *)
  | (1, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     (* VBIC<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseBitClear (cc, VfpNone, vd WR, vn RD, vm RD)

  (* < 29><14>D01<vm><vd>< 1>NQM1<vm> *)  (* VBIC (register - T1 (Q=1) *)
  | (1, 1, 1, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     (* VBIC<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseBitClear (cc, VfpNone, vd WR, vn RD, vm RD)

  (* < 29><14>D01<vn><vd><12>NQM0<vm> *) (* SHA1P - T1 *)
  | (1, 12, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1P.32 <Qd>, <Qn>, <Qm> *)
     SHA1HashUpdateParity (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><14>D10<vm><vd>< 1>M0M1<vm> *) (* VMOV (register) - T1 (Q=0) *)
  | (2, 1, 0, 1) when (b 19 16) = (b 3 0) && (bv 7) = (bv 5) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 7) (b 19 16) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpNone in
     (* VMOV<v> <Dd>, <Dm> *)
     VectorMoveDS (cc, dt, vd WR, vm RD)

  (* < 29><14>D10<vm><vd>< 1>M1M1<vm> *) (* VMOV (register) - T1 (Q=1) *)
  | (2, 1, 1, 1) when (b 19 16) = (b 3 0) && (bv 7) = (bv 5) ->
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
     VectorMoveDS (cc, dt, vd WR, vm RD)

  (* < 29><14>D10<vn><vd>< 1>N0M1<vm> *) (* VORR (register) - T1 (Q=0) *)
  | (2, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     (* VORR<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseOr (cc, VfpNone, vd WR, vn RD, vm RD)

  (* < 29><14>D10<vn><vd>< 1>N1M1<vm> *) (* VORR (register) - T1 (Q=1) *)
  | (2, 1, 1, 1) ->
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

  (* < 29><14>D10<vn><vd><12>N0M0<vm> *) (* SHA1M - T1 *)
  | (2, 12, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1M<dt> <Qd>, <Qn>, <Qm> *)
     SHA1HashUpdateMajority (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><7>0D11<vn><vd><12>N0M0<vm> *) (* SHA1SU0 - T1 *)
  | (3, 12, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1SU0<dt> <Qd>, <Qn>, <Qm> *)
     SHA1ScheduleUpdate0 (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><14>D11<vn><vd>< 1>N0M1<vm> *)  (* VORN - T1 (Q=0) *)
  | (3, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     (* VORN<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseOrNot (cc, VfpNone, vd WR, vn RD, vm RD)

  (* < 29><14>D11<vn><vd>< 1>N1M1<vm> *) (* VORN - T1 (Q=1) *)
  | (3, 1, 1, 1) ->
     let _ =
       if (bv 16) > 0 || (bv 12) > 0 || (bv 0) > 0 then
         raise
           (ARM_undefined
              ("VORN: Q=1 && (Vd<0> == 1 || Vn<0> == 1 || Vm<0. == 1)")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     (* VORN<c> <Qd>, <Qn>, <Qm> *)
     VectorBitwiseOrNot (cc, VfpNone, vd WR, vn RD, vm RD)

  (* < 29><14>Dsz<vn><vd>< 8>N0M0<vm> *) (* VADD (integer) - T1  (Q=0) *)
  | (sz, 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpInt (8 lsl sz) in
     (* VADD<c>.<dt> <Dd>, <Dn>, <Dm> *)
     VectorAdd (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><14>Dsz<vn><vd>< 8>N1M0<vm> *) (* VADD (integer) - T1  (Q=1 *)
  | (sz, 8, 1, 0) ->
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

  (* < 29><14>Dsz<vn><vd>< 9>N0M1<vm> *) (* VMUL (integer) - T1 (Q=0) *)
  | (sz, 9, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpInt (8 lsl sz) in
     (* VMUL<c>.<dt> <Dd>, <Dn>, <Dm> *)
     VectorMultiply (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><14>Dsz<vn><vd>< 9>N0M1<vm> *) (* VMUL (integer) - T1 (Q=1) *)
  | (sz, 9, 1, 1) ->
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

  | (a, b, c, d) ->
     NotRecognized (
         "parse_thumb32_29_14:"
           ^ (string_of_int a)
           ^ "_"
           ^ (string_of_int b)
           ^ "_"
           ^ (string_of_int c)
           ^ "_"
           ^ (string_of_int d),
           instr)


let parse_thumb32_29_15
      ?(_in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (_ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let isz = b 21 20 in
  let cmode = b 11 8 in
  let q = bv 6 in
  let b4 = bv 4 in
  match (isz, cmode, q, b4) with

  (* < 29><15>D000<i><vd><cm>0001<i4) *) (* VORR (immediate) - T1-0 (Q=0) *)
  | (0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 0, 1)
       when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "VORR-immediate: not reachable"])) in
     let vd = arm_extension_register_op XDouble d in
     (* VORR<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseOr (cc, dt, vd WR, vd RD, immop)

  (* < 29><15>D000<i><vd><cm>0101<i4) *) (* VORR (immediate) - T1-0 (Q=1) *)
  | (0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 1, 1)
       when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt =
       match cm with
       | 1 | 3 | 5 | 7 -> VfpInt 32
       | 9 | 11 -> VfpInt 16
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "VORR-immediate: not reachable"])) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VORR<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseOr (cc, dt, vd WR, vd RD, immop)

  (* < 29><15>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - T1-0-0 (Q=0) *)
  | (0, cm, 0, 1) when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 cm "VMOV" in
     let vd = arm_extension_register_op XDouble d in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, immop)

  (* < 29><15>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - T1-0-0 (Q=1) *)
  | (0, cm, 1, 1) when (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 cm "VMOV" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, immop)

  (* < 29><15>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - T1-0-1 (Q=0) *)
  | (0, 14, 0, 1) when (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 14 "VMOV" in
     let vd = arm_extension_register_op XDouble d in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, immop)

  (* < 29><15>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - T1-0-1 (Q=1) *)
  | (0, 14, 1, 1) when (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 14 "VMOV" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, immop)

  (* < 29><15>D000<i><vd><cm>0011<i4> *) (* VBIC (immediate) - T1-0 (Q=0) *)
  | (0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 0, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immval = adv_simd_expand_imm 1 cm imm8 in
     let (dt, immop) =
       match cm with
       | 1 | 3 | 5 | 7 ->
          (VfpInt 32, TR.tget_ok (mk_arm_immediate_op false 4 (immval#shift_right 32)))
       | 9 | 11 ->
          VfpInt 16, TR.tget_ok (mk_arm_immediate_op false 4 (immval#shift_right 48))
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "VBIC-immediate: not reachable"])) in
     let vd = arm_extension_register_op XDouble d in
     (* VBIC<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseBitClear (cc, dt, vd WR, vd RD, immop)

  (* < 29><15>D000<i><vd><cm>0111<i4> *) (* VBIC (immediate) - T1-0 (Q=1) *)
  | (0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 1, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immval = adv_simd_expand_imm 1 cm imm8 in
     let (dt, immop) =
       match cm with
       | 1 | 3 | 5 | 7 ->
          (VfpInt 32, TR.tget_ok (mk_arm_immediate_op false 4 (immval#shift_right 32)))
       | 9 | 11 ->
          VfpInt 16, TR.tget_ok (mk_arm_immediate_op false 4 (immval#shift_right 48))
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "VBIC-immediate: not reachable"])) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VBIC<c>.<dt> <Qd>, #<imm> *)
     VectorBitwiseBitClear (cc, dt, vd WR, vd RD, immop)

  (* < 29><15>D000<i><vd><cm>0011<i4> *)  (* VMVN (immediate) - T1-0 (Q=0) *)
  | (0, cm, 0, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1->
     let _ =
       if cm = 15 then
         raise (ARM_undefined ("VMVN immediate with cmode=15")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 cm "VMVN" in
     let vd = arm_extension_register_op XDouble d in
     (* VMVN<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseNot (cc, dt, vd WR, immop)

  (* < 29><15>D000<i><vd><cm>0111<i4> *)  (* VMVN (immediate) - T1-0 (Q=1) *)
  | (0, cm, 1, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let _ =
       if cm = 15 then
         raise (ARM_undefined ("VMVN immediate with cmode=15")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 cm "VMVN" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMVN<c>.<dt> <Qd>, #<imm> *)
     VectorBitwiseNot (cc, dt, vd WR, immop)

  (* < 29><15>D11<vn><vd><i4>NQM0<vm> *) (* VEXT - T1 (Q=0) *)
  | (3, i4, 0, 0) ->
     let _ =
       if (bv 11) = 1 then
         raise (ARM_undefined ("VEXT: Q=0 and imm4<3> = 1")) in
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let imm = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical i4)) in
     (* VEXT<c>.8 <Dd>, <Dn>, <Dm>, #<imm> *)
     VectorExtract (cc, VfpSize 8, vd WR, vn RD, vm RD, imm)

  (* < 29><15>D11<vn><vd><i4>NQM0<vm> *) (* VEXT - T1 (Q=1) *)
  | (3, i4, 1, 0) ->
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
     let imm = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical i4)) in
     (* VEXT<c>.8 <Dd>, <Dn>, <Dm>, #<imm> *)
     VectorExtract (cc, VfpSize 8, vd WR, vn RD, vm RD, imm)

  (* < 29><15>D001000<vd><10>00M1<vm> *) (* VMOVL - T1-s *)
  | (0, 10, 0, 1) when  (b 19 16) = 8 && (bv 7) = 0 ->
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

  (* < 29><15>D010000<vd><10>00M1<vm> *) (* VMOVL - T1-s *)
  | (1, 10, 0, 1) when  (b 19 16) = 0 && (bv 7) = 0 ->
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

  (* < 29><15>D<imm6><vd>< 0>LQM1<vm> *) (* VSHR - T1-s (Q=0) *)
  | (_sz, 0, 0, 1) ->
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
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSHR(T1-s, Q=0) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VSHR<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftRight (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>D<imm6><vd>< 0>LQM1<vm> *) (* VSHR - T1-s (Q=1) *)
  | (_sz, 0, 1, 1) ->
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
     let dt = VfpSignedInt esize in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSHR(T1, Q=1) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VSHR<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftRight (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>D<imm6><vd>< 1>LQM1<vm> *) (* VSRA - T1-s (Q=0) *)
  | (_sz, 1, 0, 1) ->
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
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSRA(T1-s, Q=0) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VSRA<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>D<imm6><vd>< 1>LQM1<vm> *) (* VSRA - T1-s (Q=1) *)
  | (_sz, 1, 1, 1) ->
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
                    STR "VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSRA(T1-s, Q=1) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VSRA<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>D<imm6><vd>< 3>LQM1<vm> *) (* VRSRA - T1-s (Q=0) *)
  | (_sz, 3, 0, 1) ->
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
                    STR "VRSRA: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VRSRA(T1-s, Q=0) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VRSRA<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorRoundingShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>D<imm6><vd>< 3>LQM1<vm> *) (* VRSRA - T1-s (Q=1) *)
  | (_sz, 3, 1, 1) ->
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
                    STR "VRSRA: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpSignedInt esize in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VRSRA(T1-s, Q=1) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VRSRA<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorRoundingShiftRightAccumulate (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>D<imm6><vd>< 5>LQM1<vm> *) (* VSHL - T1 (Q=0) *)
  | (_sz, 5, 0, 1) ->
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
                    STR "VSHL: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpInt esize in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSHL(T1, Q=0) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VSHL<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftLeft (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>D<imm6><vd>< 5>LQM1<vm> *) (* VSHL - T1 (Q=1) *)
  | (_sz, 5, 1, 1) ->
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
       | (p, q) ->
          raise
            (ARM_undefined
               ("VSHL(T1): (L, imm6-prefix) = ("
                ^ (string_of_int p)
                ^ ", "
                ^ (string_of_int q)
                ^ ")")) in
     let dt = VfpInt esize in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSHL(T1, Q=1) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VSHL<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftLeft (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>D<imm6><vd>< 8>00M1<vm> *) (* VSHRN - T1 *)
  | (_sz, 8, 0, 1) ->
     let imm6 = b 21 16 in
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let (esize, sam) =
       match (b 21 19) with
       | 1 -> (8, 16 - imm6)
       | 2 | 3 -> (16, 32 - imm6)
       | 4 | 5 | 6 | 7 -> (32, 64 - imm6)
       | p ->
          raise (ARM_undefined ("VSHRN: imm6-prefix: " ^ (string_of_int p))) in
     let dt = VfpInt (2 * esize) in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSHRN(T1) at "; iaddr#toPretty]))
         (mk_arm_immediate_op true 4 (mkNumerical sam)) in
     (* VSHRN<c>.<dt> <Dd>, <Qm>, #<imm> *)
     VectorShiftRightNarrow (cc, dt, vd WR, vm RD, imm)

  (* < 29><15>Dsz<vn><vd>< 0>N0M0<vm> *) (* VADDL - T1-s *)
  | (((0 | 1 | 2) as sz), 0, 0, 0) ->
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

  (* < 29><15>Dsz<vn><vd>< 1>N0M0<vm> *) (* VADDW - T1-s *)
  | (((0 | 1 | 2) as sz), 1, 0, 0) ->
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

  (* < 29><15>Dsz<vn><vd>< 2>N1M0<vm> *)  (* VMLAL (by scalar) - T2-s (sz=1) *)
  | (1, 2, 1, 0) ->
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

  (* < 29><15>Dsz<vn><vd>< 2>N1M0<vm> *)  (* VMLAL (by scalar) - T2-s (sz=2) *)
  | (2, 2, 1, 0) ->
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

  (* < 29><15>Dsz<vn><vd>< 8>N0M0<vm> *)  (* VMLAL (integer) - T2-s *)
  | (((0 | 1 | 2) as sz), 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt (8 lsl sz) in
     (* VMLAL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorMultiplyAccumulateLong (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><15>Dsz<vn><vd><10>N1M0<vm> *)  (* VMULL (by scalar) - T2-s (sz=1) *)
  | (1, 10, 1, 0) ->
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

  (* < 29><15>Dsz<vn><vd><10>N1M0<vm> *)  (* VMULL (by scalar) - T2-s (sz=2) *)
  | (2, 10, 1, 0) ->
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

  (* < 29><15>Dsz<vn><vd><12>N0M0<vm> *) (* VMULL (integer) - T2-s *)
  | (((0 | 1 | 2) as sz), 12, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSignedInt (8 lsl sz) in
     (* VMULL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, vm RD)

  (* < 29><15>D00<vn><vd><14>N0M0<vm> *) (* VMULL (polynomial) - T2-p *)
  | (0, 14, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpPolynomial 8 in
     (* VMULL<c>.<dt>, <Qd>, <Dn>, <Dm> *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, vm RD)

  (* VMULL (polynomial) - T2 (crypto extension) *)
  (* < 29><15>D10<vn><vd><14>N0M0<vm> *)
  | (2, 14, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpPolynomial 64 in
     (* VMULL<c>.<dt>, <Qd>, <Dn>, <Dm> *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, vm RD)

  | (a, b, c, d) ->
     NotRecognized (
         "parse_thumb32_29_15:"
           ^ (string_of_int a)
           ^ "_"
           ^ (string_of_int b)
           ^ "_"
           ^ (string_of_int c)
           ^ "_"
           ^ (string_of_int d),
           instr)


let parse_t32_30_0
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_ch: pushback_stream_int)
      (_iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let i = b 26 26 in
  let rd = arm_register_op (get_arm_reg (b 11 8)) in
  let setflags = (b 20 20) = 1 in
  let imm3 = b 14 12 in
  let imm8 = b 7 0 in
  let imm12 = (i lsl 11) + (imm3 lsl 8) + imm8 in
  let (imm32, _) = thumb_expand_imm_c imm12 0 in
  let imm32 = TR.tget_ok (make_immediate false 4 (mkNumerical imm32)) in
  let const = arm_immediate_op imm32 in

  match (b 25 21) with

  (* < 30>i<  0>S<rn>0<i><rd><-imm8->   AND (immediate) - T1 *)
  | 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* AND{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseAnd (setflags, cc, rd WR, rn RD, const, true)

  (* < 30>i<  1>S<rn>0<i><rd><-imm8->   BIC (immediate) - T1 *)
  | 1 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* BIC{S} <Rd>, <Rn>, #<const> *)
     BitwiseBitClear (setflags, cc, rd WR, rn RD, const, false)

  (* < 30>i<  2>S<15>0<i><rd><-imm8->   MOV.W (immediate) - T2 *)
  | 2 when (b 19 16) = 15 ->
     (* MOV{S}<c>.W <Rd>, #<const> *)
     Move (setflags, cc, rd WR, const, true, false)

  (* < 30>i<  2>S<rn>0<i><rd><-imm8->   ORR (immediate) - T1 *)
  | 2 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* ORR{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseOr (setflags, cc, rd WR, rn RD, const, false)

  (* < 30>i<  3>S<15>0<i><rd><-imm8->   MVN (immediate) - T1 *)
  | 3 when (b 19 16) = 15 ->
     (* MVN{S}<c> <Rd>, #<const> *)
     BitwiseNot (setflags, cc, rd WR, const, false)

  (* < 30>i<  3>S<rn>0<i><rd><-imm8->   ORN (immediate) - T1 *)
  | 3 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* ORN{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseOrNot (setflags, cc, rd WR, rn RD, const)

  (* < 30>i<  4>S<rn>0<i><rd><-imm8->   EOR (immediate) - T1 *)
  | 4 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* EOR{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseExclusiveOr (setflags, cc, rd WR, rn RD, const, false)

  (* < 30>i<  8>S<rn>0<i><rd><-imm8->   ADD.W (immediate) - T3 *)
  | 8 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* ADD{S}<c>.W <Rd>, <Rn>, #<const> *)
     Add (setflags, cc, rd WR, rn RD, const, true)

  (* < 30>i< 10>S<rn>0<i><rd><-imm8->   ADC (immediate) - T1 *)
  | 10 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* ADC{S}<c> <Rd>, <Rn>, #<const> *)
     AddCarry (setflags, cc, rd WR, rn RD, const, true)

  (* < 30>i< 11>S<rn>0<i><rd><-imm8->   SBC (immediate) - T1 *)
  | 11 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* SBC{S}<c> <Rd>, <Rn>, #<const> *)
     SubtractCarry (setflags, cc, rd WR, rn RD, const, false)

  (* < 30>i< 13>1<rn>0<i><15><-imm8->   CMP (immediate) - T2 *)
  | 13 when setflags && (b 11 8) = 15 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let imm = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm = thumb_expand_imm imm 0 in
     let imm = TR.tget_ok (make_immediate false 4 (mkNumerical imm)) in
     let imm = arm_immediate_op imm in
     (* CMP<c>.W <Rn>, #<const> *)
     Compare (cc, rn RD, imm, true)

  (* < 30>i< 13>S<rn>0<i><rd><-imm8->   SUB (immediate) - T3 *)
  | 13 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let imm = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm = thumb_expand_imm imm 0 in
     let imm = TR.tget_ok (make_immediate false 4 (mkNumerical imm)) in
     let imm = arm_immediate_op imm in
     (* SUB{S}<c>.W <Rd>, <Rn>, #<const> *)
     Subtract (setflags, cc, rd WR, rn RD, imm, true, false)

  (* < 30>i< 14>S<rn>0<i><rd><-imm8->   RSB (immediate) - T2 *)
  | 14 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let imm = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm = thumb_expand_imm imm 0 in
     let imm = TR.tget_ok (make_immediate false 4 (mkNumerical imm)) in
     let imm = arm_immediate_op imm in
     (* RSB{S}<c>.W <Rd>, <Rn>, #<const> *)
     ReverseSubtract (setflags, cc, rd WR, rn RD, imm, true)

  (* < 30>i< 16>0<rn>0<i><rd><-imm8->   ADD (immediate) - T4 *)
  | 16 when not setflags ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let imm32 = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm32 = TR.tget_ok (make_immediate false 4 (mkNumerical imm32)) in
     let imm12 = arm_immediate_op imm32 in
     (* ADDW<c> <Rd>, <Rn>, #<imm12> *)
     Add (false, cc, rd WR, rn RD, imm12, false)

  (* < 30>i< 18>0<ii>0<i><rd><-imm8->   MOVW (immediate) - T3 *)
  | 18 when not setflags ->
     let imm4 = b 19 16 in
     let imm16 = (imm4 lsl 12) + (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm16 = TR.tget_ok (make_immediate false 4 (mkNumerical imm16)) in
     let imm16 = arm_immediate_op imm16 in
     Move (false, cc, rd WR, imm16, false, true)

  (* < 30>i< 21>0<13>0<i><rd><-imm8->   SUB (SP minus immediate) - T3 *)
  | 21 when (not setflags) && (b 19 16) = 13  ->
     let imm32 = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let sp = arm_register_op (get_arm_reg 13) in
     let imm32 = TR.tget_ok (make_immediate false 4 (mkNumerical imm32)) in
     let imm12 = arm_immediate_op imm32 in
     (* SUBW<c> <Rd>, SP #<imm12> *)
     Subtract (false, cc, rd WR, sp RD, imm12, false, true)

  (* < 30>i< 21>0<rn>0<i><rd><-imm8->   SUBW (immediate) - T4 *)
  | 21 when (not setflags) ->
     let imm32 = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let imm32 = TR.tget_ok (make_immediate false 4 (mkNumerical imm32)) in
     let imm12 = arm_immediate_op imm32 in
     (* SUBW<c> <Rd>, <Rn>, #<imm12> *)
     Subtract (false, cc, rd WR, rn RD, imm12, false, true)

  (* < 30>i< 22>0<ii>0<i><rd><-imm8->   MOVT - T1 *)
  | 22 when not setflags ->
     let imm4 = b 19 16 in
     let imm16 = (imm4 lsl 12) + (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm16 = TR.tget_ok (make_immediate false 4 (mkNumerical imm16)) in
     let imm16 = arm_immediate_op imm16 in
     (* MOVT<c> <Rd>, #<imm16> *)
     MoveTop (cc, rd WR, imm16)

  (* < 30>0< 26>0<rn>0<i><rd>i20<wm1>   SBFX - T1 *)
  | 26 when i = 0 ->
     let lsb = (imm3 lsl 2) + (b 7 6) in
     let widthm1 = b 4 0 in
     let rn = mk_arm_reg_bit_sequence_op (get_arm_reg (b 19 16)) lsb widthm1 in
     SignedBitFieldExtract (cc, rd WR, rn RD)

  (* < 30>0< 27>0<15>0<i><rd>i20<msb>   BFC - T1 *)
  | 27 when i = 0 && (b 19 16) = 15 ->
     let lsb = (imm3 lsl 2) + (b 7 6) in
     let msb = b 4 0 in
     let width = (msb - lsb) + 1 in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     (* BFC<c> <Rd>, #<lsb>, #<width> *)
     BitFieldClear (cc, rd WR, lsb, width, msb)

  (* < 30>0< 27>0<rn>0<i><rd>i20<msb>   BFI - T1 *)
  | 27 when i = 0 ->
     let lsb = (imm3 lsl 2) + (b 7 6) in
     let msb = b 4 0 in
     let width = (msb - lsb) + 1 in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* BFI<c> <Rd>, <Rn>, #<lsb>, #<width> *)
     BitFieldInsert (cc, rd WR, rn RD, lsb, width, msb)

  (* < 30>0< 28>0<rn>0<i><rd>i20<imm>   USAT - T1 *)
  | 28 when i = 0 ->
     let imm = TR.tget_ok (make_immediate false 4 (mkNumerical (b 4 0))) in
     let immop = arm_immediate_op imm in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let shimm = ((b 14 12) lsl 2) + (b 7 6) in
     let (_, shift_n) = decode_imm_shift 0 shimm in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = mk_arm_imm_shifted_register_op rnreg 0 shift_n in
     (* USAT<c> <Rd>, #<imm>, <Rn[, <shift>] *)
     UnsignedSaturate (cc, rd WR, immop, rn RD)

  (* < 30>0< 30>0<rn>0<i><rd>i20<wm1>   UBFX - T1 *)
  | 30 when i = 0 ->
     let lsb = (imm3 lsl 2) + (b 7 6) in
     let widthm1 = b 4 0 in
     let rn = mk_arm_reg_bit_sequence_op (get_arm_reg (b 19 16)) lsb widthm1 in
     (* UBFX<c> <Rd>, <Rn>, #<lsb>, #<width> *)
     UnsignedBitFieldExtract (cc, rd WR, rn RD)

  | tag ->
     NotRecognized ("t32_30_0:" ^ (string_of_int tag), instr)

let parse_t32_branch
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let not_eor (j:int) (s:int) =
    match (j, s) with
    | (0, 0) -> 1
    | (0, 1) -> 0
    | (1, 0) -> 0
    | (1, 1) -> 1
    | _ -> raise (BCH_failure (STR "not_eor in parse_t32_branch")) in
  match ((b 14 14), (b 12 12)) with

  (* < 30>01110111111100011110101<op>   DMB *)
  | (0, 0) when
         (b 13 13) = 0
         && (b 11 8) = 15
         && (b 7 4) = 5
         && (b 19 16) = 15
         && (b 26 23) = 7
         && (b 22 20) = 3 ->
     DataMemoryBarrier (cc, arm_dmb_option_from_int_op (b 3 0))

  (* < 30>011101011111000000000000000   NOP.W *)
  | (0, 0) when
         (b 7 0) = 0
         && (b 11 8) = 0
         && (b 13 13) = 0
         && (b 19 16) = 15
         && (b 26 23) = 7
         && (b 22 20) = 2 ->
     NoOperation cc

  (* < 30>S<cc><imm6>10J0J<--imm11-->   B (encoding T3) *)
  | (0, 0) ->
     let s = b 26 26 in
     let imm6 = b 21 16 in
     let j1 = b 13 13 in
     let j2 = b 11 11 in
     let imm11 = b 10 0 in
     let imm32 =
       (s lsl 20) + (j2 lsl 19) + (j1 lsl 18) + (imm6 lsl 12) + (imm11 lsl 1) in
     let imm32 = sign_extend 32 21 imm32 in
     let tgt = (iaddr#add_int 4)#add_int imm32 in
     (try
        let tgtop = arm_absolute_op tgt RD in
        let cond = get_opcode_cc (b 25 22) in
        (* B<c>.W <label> *)
        Branch (cond, tgtop, true)
      with
      | Invalid_argument s ->
         NotRecognized ("error in B (T3): " ^ s, instr))

  (* < 30>S<--imm10->10J1J<--imm11-->   B (encoding T4) *)
  | (0,1) ->
     let s = b 26 26 in
     let j1 = b 13 13 in
     let j2 = b 11 11 in
     let i1 = not_eor j1 s in
     let i2 = not_eor j2 s in
     let imm32 =
       (s lsl 24)
       + (i1 lsl 23)
       + (i2 lsl 22)
       + ((b 25 16) lsl 12)
       + ((b 10 0) lsl 1) in
     let imm32 = sign_extend 32 25 imm32 in
     let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
     let tgt = (iaddr#add_int 4)#add_int imm32 in
     (try
        let tgtop = arm_absolute_op tgt RD in
        (* B<c>.W <label> *)
        Branch (cc, tgtop, true)
      with
      | Invalid_argument s ->
         NotRecognized ("error in B (T4): " ^ s, instr))

  (* < 30>S<-imm10H->11J0J<-imm10L->H   BLX (immediate) - T2 *)
  | (1, 0) ->
     let s = b 26 26 in
     let j1 = b 13 13 in
     let j2 = b 11 11 in
     let i1 = not_eor j1 s in
     let i2 = not_eor j2 s in
     let imm32 =
       (s lsl 24)
       + (i1 lsl 23)
       + (i2 lsl 22)
       + ((b 25 16) lsl 12)
       + (4 * (b 10 1)) in
     let imm32 = sign_extend 32 25 imm32 in
     let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
     let tgt = ((iaddr#to_int + 4) / 4) * 4 in
     let tgt = TR.tget_ok (int_to_doubleword (tgt + imm32)) in
     (try
        let tgtop = arm_absolute_op tgt RD in
        (* BLX<c> <label> *)
        BranchLinkExchange (cc, tgtop)
      with
      | Invalid_argument s ->
         NotRecognized ("error in BLX (imm, T2): " ^ s, instr))

  (* < 30>S<--imm10->11J1J<--imm11-->   BL (immediate) - T1 *)
  | (1, 1) ->
     let s = b 26 26 in
     let j1 = b 13 13 in
     let j2 = b 11 11 in
     let i1 = not_eor j1 s in
     let i2 = not_eor j2 s in
     let imm32 =
       (s lsl 24)
       + (i1 lsl 23)
       + (i2 lsl 22)
       + ((b 25 16) lsl 12)
       + (2 * (b 10 0)) in
     let imm32 = sign_extend 32 25 imm32 in
     let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
     let tgt = iaddr#to_int + 4 in
     let tgt = TR.tget_ok (int_to_doubleword (tgt + imm32)) in
     (try
        let tgtop = arm_absolute_op tgt RD in
        (* BL<c> <label> *)
        BranchLink (cc, tgtop)
      with
      | Invalid_argument s ->
         NotRecognized ("error in BL (imm, T1): " ^ s, instr))

  | (k, l) ->
     NotRecognized
       ("t32_branch:"
        ^ (string_of_int k)
        ^ "_"
        ^ (string_of_int l),
        instr)


let parse_thumb32_30
      ?(in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  match b 15 15 with
  | 0 -> parse_t32_30_0 ~_in_it:in_it ~cc ch iaddr instr
  | 1 -> parse_t32_branch ~_in_it:in_it ~cc ch iaddr instr
  | _ ->
     NotRecognized ("parse_thumb32_30", instr)


let parse_thumb32_31_0
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  let rnreg = get_arm_reg (b 19 16) in
  let rn = arm_register_op rnreg in
  let rt = arm_register_op (get_arm_reg (b 15 12)) in
  let rm = arm_register_op (get_arm_reg (b 3 0)) in
  let offset = ARMImmOffset (b 11 0) in
  (* let mem ?(size=4) ?(align=4) mode =
    mk_arm_offset_address_op
      ~size ~align rnreg offset ~isadd:true ~isindex:true ~iswback:false mode in *)
  match (b 24 20) with
  (* < 31>00<  0><rn><rt>000000i2<rm>   STRB (register) - T2 *)
  | 0 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = arm_shifted_index_offset (get_arm_reg (b 3 0)) reg_srt in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:1 ~isadd:true ~isindex:true ~iswback:false in
     (* STRB<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     StoreRegisterByte (cc, rt RD, rn RD, rm RD, mem WR, true)

  (* < 31>00<  0><rn><rt>1puw<-imm8->   STRB (immediate) - T3 *)
  | 0 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let imm = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical (b 7 0))) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem =
       mk_arm_offset_address_op ~size:1 rnreg offset ~isadd ~isindex ~iswback in
     (* STRB<c> <Rt>, [<Rn>, #-<imm8>]
        STRB<c> <Rt>, [<Rn>], #+/-<imm8>
        STRB<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     StoreRegisterByte (cc, rt RD, rn RD, imm, mem WR, true)

  (* < 31>000U001<15><15><--imm12--->   (PLD (literal) - T1) *)
  | 1 | 9 when (b 19 16) = 15 && (b 15 12) = 15 ->
     let imm = b 11 0 in
     let is_add = (b 23 23) = 1 in
     let pcreg = arm_register_op (get_arm_reg 15) in
     let immop = arm_literal_op ~is_add (iaddr#add_int 4) imm in
     PreloadData (false, cc, pcreg RD, immop)

  (* < 31>00<  1><rn><rt>000000i2<rm>   LDRB (register) - T2 *)
  | 1 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = arm_shifted_index_offset (get_arm_reg (b 3 0)) reg_srt in
     let mem =
       mk_arm_offset_address_op
         ~size:1 rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDRB<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegisterByte (cc, rt WR, rn RD, rm RD, mem RD, true)

  (* < 31>00<  1><rn><rt>1puw<-imm8->   LDRB (immediate) - T3 *)
  | 1 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let imm = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical (b 7 0))) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem =
       mk_arm_offset_address_op
         ~size:1 rnreg offset ~isadd ~isindex ~iswback in
     (* LDRB<c>.W <Rt>, [<Rn>{, #+/-<imm8>}]     Offset: (index,wback) = (T,F)
      * LDRB<c>.W <Rt>, [<Rn>, #+/-<imm8>]!      Pre-x : (index,wback) = (T,T)
      * LDRB<c>.W <Rt>, [<Rn>], #+/-<imm8>       Post-x: (index,wback) = (F,T)  *)
     LoadRegisterByte (cc, rt WR, rn RD, imm, mem RD, true)

  (* < 31>00<  2><rn><rt>000000i2<rm>    STRH (register) - T2 *)
  | 2 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = arm_shifted_index_offset (get_arm_reg (b 3 0)) reg_srt in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:2 ~isadd:true ~isindex:true ~iswback:false in
     (* STRH<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     StoreRegisterHalfword (cc, rt RD, rn RD, rm RD,  mem WR, true)

  (* < 31>00<  2><rn><rt>1puw<-imm8->   STRH (immediate) - T3*)
  | 2 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem =
       mk_arm_offset_address_op ~size:2 rnreg offset ~isadd ~isindex ~iswback in
     (* STRH<c> <Rt>, [<Rn>, #-<imm8>]
        STRH<c> <Rt>, [<Rn>], #+/-<imm8>
        STRH<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     StoreRegisterHalfword (cc, rt RD, rn RD, rm RD, mem WR, true)

  (* < 31>00<  3><rn><rt>000000i2<rm>   LDRH (register) - T2 *)
  | 3 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = arm_shifted_index_offset (get_arm_reg (b 3 0)) reg_srt in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:2 ~isadd:true ~isindex:true ~iswback:false in
     (* LDRH<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegisterHalfword (cc, rt WR, rn RD, rm RD, mem RD, true)

  (* < 31>00<  3><rn><rt>1puw<-imm8->   LDRH (immediate) - T3 *)
  | 3 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int (b 7 0))) in
     let mem =
       mk_arm_offset_address_op ~size:2 rnreg offset ~isadd ~isindex ~iswback in
     (* LDRH<c>.W <Rt>, [<Rn>{, #+/-<imm8>}]    Offset: (index,wback) = (T,F)
      * LDRH<c>.W <Rt>, [<Rn>, #+/-<imm8>]!     Pre-x : (index,wback) = (T,T)
      * LDRH<c>.W <Rt>, [<Rn>], #+/-<imm8>      Post-x: (index,wback) = (F,T)  *)
     LoadRegisterHalfword (cc, rt WR, rn RD, imm, mem RD, true)

  (* < 31>00<  4><13><rt>110100000100   PUSH.W  - T3 *)
  | 4 when (b 19 16) = 13 && (b 11 11) = 1 && (b 10 8) = 3 && (b 7 0) = 4 ->
     let sp = arm_register_op (get_arm_reg 13) RW in
     let rl = arm_register_list_op [ (get_arm_reg (b 15 12)) ] RD in
     Push (cc, sp, rl, true)

  (* < 31>00<  4><rn><rt>000000i2<rm>   STR (register) - T2 *)
  | 4 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = arm_shifted_index_offset (get_arm_reg (b 3 0)) reg_srt in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* STR<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     StoreRegister (cc, rt RD, rn RD, rm RD, mem WR, true)

  (* < 31>00<  4><rn><rt>1puw<-imm8->   STR (immediate) - T4 *)
  | 4 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical (b 7 0))) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* STR<c> <Rt>, [<Rn>, #-<imm8>]
        STR<c> <Rt>, [<Rn>], #+/-<imm8>
        STR<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     StoreRegister (cc, rt RD, rn RD, immop, mem WR, true)

  (* < 31>00<  5><13><rt>101100000100   POP - T3 *)
  | 5 when (b 19 16) = 13 && (b 11 11) = 1 && (b 10 8) = 3 && (b 7 0) = 4 ->
     let sp = arm_register_op (get_arm_reg 13) RW in
     let rl = arm_register_list_op [ (get_arm_reg (b 15 12))] WR in
     Pop (cc, sp, rl, true)

  (* < 31>000U101<15><rt><--imm12--->   LDR (literal, U=0) *)
  | 5 when (b 19 16) = 15 ->
     let pcreg = get_arm_reg 15 in
     let pc = arm_register_op pcreg RD in
     let imm = b 11 0 in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
     let addrop = arm_literal_op ~is_add:false (iaddr#add_int 4) imm in
     (* LDR<c>.W <Rt>, <label> *)
     LoadRegister (cc, rt WR, pc, immop, addrop, true)

  (* < 31>00<  5><rn><rt>000000i2<rm>   LDR (register) - T2 *)
  | 5 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = decode_imm_shift 0 (b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let rmreg = get_arm_reg (b 3 0) in
     let offset = arm_shifted_index_offset rmreg reg_srt in
     let memi =
       mk_arm_offset_address_op
         ~align:1 rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDR<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegister (cc, rt WR, rn RD, rm RD, memi RD, true)

  (* < 31>00<  5><rn><rt>1PUW<-imm8->   LDR (immediate) - T4 *)
  | 5 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical (b 7 0))) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem =
       mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* LDR<c>.W <Rt>, [<Rn>{, #+/-<imm8>}]     Offset: (index,wback) = (T,F)
      * LDR<c>.W <Rt>, [<Rn>, #+/-<imm8>]!      Pre-x : (index,wback) = (T,T)
      * LDR<c>.W <Rt>, [<Rn>], #+/-<imm8>       Post-x: (index,wback) = (F,T)  *)
     LoadRegister (cc, rt WR, rn RD, immop, mem RD, true)

  (* < 31>00<  8><rn><rt><--imm12--->   STRB (immediate) - T2 *)
  | 8 ->
     (* STRB<c>.W <Rt>, [<Rn, #<imm12>] *)
     let immop =
       TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical (b 11 0))) in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:1 ~isadd:true ~isindex:true ~iswback:false in
     StoreRegisterByte (cc, rt RD, rn RD, immop, mem WR, true)

  (* < 31>00010W1<rn><15><--imm12--->   PLD (immediate, T1) *)
  | 9 | 11 when (b 15 12) = 15 ->
     let iswrite = (b 21 21) = 1 in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     PreloadData (iswrite, cc, rn RD, mem WR)

  (* < 31>00<  9><rn><rt><--imm12--->   LDRB (immediate) - T2 *)
  | 9 ->
     (* LDRB<c>.W <Rt>, [<Rn>, #<imm12>] *)
     let immop =
       TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical (b 11 0))) in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:1 ~isadd:true ~isindex:true ~iswback:false in
     LoadRegisterByte (cc, rt WR, rn RD, immop, mem RD, true)

  (* < 31>00< 10><rn><rt><--imm12--->   STRH (immediate) - T2 *)
  | 10 ->
     (* STRH<c>.W <Rt>, [<Rn>, #<imm12>] *)
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:2 ~isadd:true ~isindex:true ~iswback:false in
     StoreRegisterHalfword (cc, rt RD, rn RD, rm RD, mem WR, true)

  (* < 31>00< 11><rn><rt><--imm12--->   LDRH (immediate) - T2 *)
  | 11 ->
     (* LDRH<c>.W <Rt>, [<Rn>{, #<imm12>} *)
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:2 ~isadd:true ~isindex:true ~iswback:false in
     LoadRegisterHalfword (cc, rt WR, rn RD, rm RD, mem RD, true)

  (* < 31>00< 12><rn><rt><--imm12--->   STR (immediate) - T3 *)
  | 12 ->
     (* STR<c>.W <Rt>, [<Rn>, #<imm12>] *)
     let immop =
       TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical (b 11 0))) in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     StoreRegister (cc, rt RD, rn RD, immop, mem WR, true)

  (* < 31>000U101<15><rt><--imm12--->   LDR (literal, U=1) *)
  | 13 when (b 19 16) = 15 ->
     let pcreg = get_arm_reg 15 in
     let pc = arm_register_op pcreg RD in
     let imm = b 11 0 in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
     let addrop = arm_literal_op (iaddr#add_int 4) imm in
     (* LDR.W<c> <Rt>, <label> *)
     LoadRegister (cc, rt WR, pc, immop, addrop, true)

  (* < 31>00< 13><rn><rt><--imm12--->   LDR (immediate) - T3 *)
  | 13 ->
     (* LDR<c>.W <Rt>, [<Rn>{, #<imm12>}] *)
     let immop =
       TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical (b 11 0))) in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     LoadRegister (cc, rt WR, rn RD, immop, mem RD, true)

  (* < 31>00< 17><rn><rt>000000i2<rm>   LDRSB (register) - T2 *)
  | 17 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = decode_imm_shift 0 (b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = arm_register_op rmreg in
     let offset = arm_shifted_index_offset rmreg reg_srt in
     let memi =
       mk_arm_offset_address_op
         rnreg offset ~size:1 ~align:1 ~isadd:true ~isindex:true ~iswback:false in
     (* LDRSB<c>.W, <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegisterSignedByte (cc, rt WR, rn RD, rm RD, memi RD, true)

  (* < 31>00< 17><rn><rt>1puw<-imm8->   LDRSB (immediate) - T2 *)
  | 17 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let imm =
       arm_immediate_op (TR.tget_ok (signed_immediate_from_int (b 7 0))) in
     let mem =
       mk_arm_offset_address_op
         ~size:1 ~align:1 rnreg offset ~isadd ~isindex ~iswback in
     (* LDRSB<c> <Rt>, [<Rn>, #-<imm8>]
        LDRSB<c> <Rt>, [<Rn>], #+/-<imm8>
        LDRSB<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     LoadRegisterSignedByte (cc, rt WR, rn RD, imm, mem RD, false)

  (* < 31><1>0D00<rn><vd><ty>szal<rm>   VST1 (multiple single elements) T1 *)
  | 16 | 20 ->
     let rnreg = b 19 16 in
     let rn = arm_register_op (get_arm_reg rnreg) in
     let d = bv 22 in
     let vd = prefix_bit d (b 15 12) in
     let rmreg = b 3 0 in
     let rm = get_arm_reg rmreg in
     let rmop = arm_register_op rm RD in
     let ty = b 11 8 in
     let sz = b 7 6 in
     let align = b 5 4 in
     (match ty with
      | 2 | 6 | 7 | 10 ->
         let alignment = if align = 0 then 1 else 8 * (4 lsl align) in
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
           (* < 31>0010D10<rn><vd>0111szal<rm> *) (* 1 register *)
           | 7 -> arm_simd_reg_list_op XDouble [vd]
           (* < 31>0010D10<rn><vd>1010szal<rm> *) (* 2 registers *)
           | 10 -> arm_simd_reg_list_op XDouble [vd; vd + 1]
           (* < 31>0010D10<rn><vd>0110szal<rm> *) (* 3 registers *)
           | 6 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2]
           (* < 31>0010D10<rn><vd>0010szal<rm> *) (* 4 registers *)
           | 2 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2; vd + 3]
           | _ ->
              raise (BCH_failure (STR "VectorLoadOne: not reachable")) in
         (* VST1<c>.<size> <list>, [<Rn>{:<align>}]{!} *)
         (* VST1<c>.<size> <list>, [<Rn>{:<align>}], <Rm> *)
         VectorStoreOne (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)
      | _ ->
         NotRecognized (
             "arm_vector_structured_sotre_0:" ^ (string_of_int ty), instr))

  (* < 31>0010D10<rn><vd><ty>szal<rm>   VLD1/VLD4 (multiple single elements) T1 *)
  | 18 | 22 ->
     let rnreg = b 19 16 in
     let rn = arm_register_op (get_arm_reg rnreg) in
     let d = bv 22 in
     let vd = prefix_bit d (b 15 12) in
     let rmreg = b 3 0 in
     let rm = get_arm_reg rmreg in
     let rmop = arm_register_op rm RD in
     let ty = b 11 8 in
     let sz = b 7 6 in
     let align = b 5 4 in
     (match ty with
      | 0 | 1 ->
       let alignment = if align = 0 then 1 else 8 * (4 lsl align) in
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
         (* <15>01000D10<rn><vd>0000szal<rm> *) (* inc = 1 *)
         | 0 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2; vd + 3]
         (* <15>01000D10<rn><vd>0001szal<rm> *) (* inc = 2 *)
         | 1 -> arm_simd_reg_list_op XDouble [vd; vd + 2; vd + 4; vd + 6]
         | _ ->
            raise (BCH_failure (STR "VectorLoadFour: not reachable")) in
       (* VLD4<c>.<size> <list>, [<Rn>{:<align>}]{!} *)
       (* VLD4<c>.<size> <list>, [<Rn>{:<align>}], <Rm> *)
       VectorLoadFour (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)

      | 2 | 6 | 7 | 10 ->
         let alignment = if align = 0 then 1 else 8 * (4 lsl align) in
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
           (* < 31>0010D10<rn><vd>0111szal<rm> *) (* 1 register *)
           | 7 -> arm_simd_reg_list_op XDouble [vd]
           (* < 31>0010D10<rn><vd>1010szal<rm> *) (* 2 registers *)
           | 10 -> arm_simd_reg_list_op XDouble [vd; vd + 1]
           (* < 31>0010D10<rn><vd>0110szal<rm> *) (* 3 registers *)
           | 6 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2]
           (* < 31>0010D10<rn><vd>0010szal<rm> *) (* 4 registers *)
           | 2 -> arm_simd_reg_list_op XDouble [vd; vd + 1; vd + 2; vd + 3]
           | _ ->
              raise (BCH_failure (STR "VectorLoadOne: not reachable")) in
         (* VLD1<c>.<size> <list>, [<Rn>{:<align>}]{!} *)
         (* VLD1<c>.<size> <list>, [<Rn>{:<align>}], <Rm> *)
         VectorLoadOne (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)
      | _ ->
         NotRecognized (
             "arm_vector_structured_load_0:" ^ (string_of_int ty), instr))

  (* < 31>00< 19><rn><rt>< 0>00i2<rm>   LDRSH (register) - T2 *)
  | 19 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = decode_imm_shift 0 (b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = arm_register_op rmreg in
     let offset = arm_shifted_index_offset rmreg reg_srt in
     let memi =
       mk_arm_offset_address_op
         rnreg offset ~size:2 ~align:2 ~isadd:true ~isindex:true ~iswback:false in
     (* LDRSH<c>.W, <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegisterSignedHalfword (cc, rt WR, rn RD, rm RD, memi RD, true)

  (* < 31>00< 19><rn><rt>1puw<-imm8->   LDRSH (immediate) - T2 *)
  | 19 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let imm =
       arm_immediate_op (TR.tget_ok (signed_immediate_from_int (b 7 0))) in
     let mem =
       mk_arm_offset_address_op
         ~size:2 ~align:2 rnreg offset ~isadd ~isindex ~iswback in
     (* LDRSH<c> <Rt>, [<Rn>, #-<imm8>]
        LDRSH<c> <Rt>, [<Rn>], #+/-<imm8>
        LDRSH<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     LoadRegisterSignedHalfword (cc, rt WR, rn RD, imm, mem RD, false)

  (* < 31>00< 25><rn><rt><--imm12--->   LDRSB (immediate) - T1 *)
  | 25 ->
     let imm12 = b 11 0 in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int imm12)) in
     let offset = ARMImmOffset imm12 in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:2 ~align:1 ~isadd:true ~isindex:true ~iswback:false in
     (* LDRSB<c> <Rt>, [<Rn>, #<imm12>] *)
     LoadRegisterSignedByte (cc, rt WR, rn RD, imm, mem RD, false)

  (* < 31><1>1D00<rn><vd>sz00<ia><rm>  VST1 (single elt from one lane *)
  | 24 | 28 when (b 9 8) = 0 ->
    let sz = b 11 10 in
    let index_align = b 7 4 in
    let rnreg = b 19 16 in
    let rn = arm_register_op (get_arm_reg rnreg) in
    let rmreg = b 3 0 in
    let rm = get_arm_reg rmreg in
    let rmop = arm_register_op rm RD in
    let d = bv 22 in
    let vd = prefix_bit d (b 15 12) in
    let (ebytes, esize, index, alignment) =
      match sz with
      | 0 -> (1, 8, index_align lsr 1, 1)
      | 1 -> (2, 16, index_align lsr 2, 16)
      | 2 -> (4, 32, index_align lsr 3, 1)
      | _ -> raise (BCH_failure (STR "VectorStoreOne: not reachable")) in
    let (wb, wback) =
      match rmreg with
      | 15 -> (false, SIMDNoWriteback)
      | 13 -> (true, SIMDBytesTransferred ebytes)
      | _ -> (true, SIMDAddressOffsetRegister rm) in
    let rnop = if wb then rn WR else rn RD in
    let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
    let rlist = arm_simd_reg_elt_list_op XDouble [vd] index esize in
    (* VST1<c>.<size> <list>, [<Rn>{:align}]{!} *)
    (* VST1<c>.<size> <list>, [<Tn>{:align}], <Rm> *)
    VectorStoreOne (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)

  (* < 31><1>1D00<rn><vd>sz11<ia><rm>   VST4 (single 4-elt from one lane *)
  | 24 | 28 when (b 9 8) = 3 && (b 11 10) < 3->
     let sz = b 11 10 in
     let index_align = b 7 4 in
     let ia_0 = bv 4 in
     let ia_1 = bv 5 in
     let ia_2 = bv 6 in
     let ia_10 = b 5 4 in
     let rnreg = b 19 16 in
     let rn = arm_register_op (get_arm_reg rnreg) in
     let rmreg = b 3 0 in
     let rm = get_arm_reg rmreg in
     let rmop = arm_register_op rm RD in
     let d = bv 22 in
     let vd = prefix_bit d (b 15 12) in
     let (ebytes, esize, index, inc, alignment) =
       match sz with
       | 0 -> (1, 8, index_align lsr 1, 1, if ia_0 = 0 then 1 else 4)
       | 1 ->
          (2, 16, index_align lsr 2, (if ia_1 = 0 then 1 else 2),
           if ia_0 = 0 then 1 else 8)
       | 2 ->
          (4, 32, index_align lsr 3,
           (if ia_2 = 0 then 1 else 2),
           if ia_10 = 0 then 1 else 4 lsl ia_10)
       | _ -> raise (BCH_failure (STR "VectorStoreFour: not reachable")) in
     let (wb, wback) =
       match rmreg with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred ebytes)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let rnop = if wb then rn WR else rn RD in
     let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
     let rlist =
       arm_simd_reg_elt_list_op
         XDouble [vd; vd + inc; vd + (2 * inc); vd + (3 * inc)] index esize in
     VectorStoreFour (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)

  (* < 31><1>1D10<rn><vd>sz11<ia><rm> VLD4 single 4-elt to one lane *)
  | 26 | 30 when (b 9 8) = 3 && (b 11 10) < 3 ->
     let sz = (b 11 10) in
     let index_align = b 7 4 in
     let rnreg = b 19 16 in
     let rn = arm_register_op (get_arm_reg rnreg) in
     let rmreg = b 3 0 in
     let rm = get_arm_reg rmreg in
     let rmop = arm_register_op rm RD in
     let d = bv 22 in
     let vd = prefix_bit d (b 15 12) in
     let (ebytes, esize, index, inc, alignment) =
       match sz with
       | 0 -> (1, 8, index_align lsr 1, 1, if (bv 4) = 0 then 1 else 4)
       | 1 ->
          (2,
           16,
           index_align lsr 2,
           (if (bv 5) = 1 then 1 else 2),
           (if (bv 4) = 1 then 1 else 8))
       | 2 ->
          (4,
           32,
           index_align lsr 3,
           (if (bv 6) = 0 then 1 else 2),
           (if (b 5 4) = 0 then 1 else 4 lsl (b 5 4)))
       | _ ->
          raise (BCH_failure (STR "VectorLoadFour: not reachable")) in
     let (wb, wback) =
       match rmreg with
       | 15 -> (false, SIMDNoWriteback)
       | 13 -> (true, SIMDBytesTransferred ebytes)
       | _ -> (true, SIMDAddressOffsetRegister rm) in
     let rnop = if wb then rn WR else rn RD in
     let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
     let rlist =
       arm_simd_reg_elt_list_op
         XDouble [vd; vd + inc; vd + (2 * inc); vd + (3 * inc)] index esize in
     VectorLoadFour (wb, cc, VfpSize esize, rlist RD, rnop, mem WR, rmop)

  (* < 31><1>1D10<rn><vd><12>szTa<rm> *)(* VLD1 (single elt to all lanes) - T1 *)
  | 26 | 30 when (b 11 8) = 12 ->
    let sz = b 7 6 in
    let t = bv 5 in
    let a = bv 4 in
    let ebytes = 1 lsl sz in
    let esize = 8 * ebytes in
    let elements = 8 / ebytes in
    let alignment = if a = 0 then 16 else 32 in
    let rnreg = b 19 16 in
    let rn = arm_register_op (get_arm_reg rnreg) in
    let rmreg = b 3 0 in
    let rm = get_arm_reg rmreg in
    let rmop = arm_register_op rm RD in
    let d = bv 22 in
    let vd = prefix_bit d (b 15 12) in
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
        arm_simd_reg_rep_elt_list_op XDouble [vd; vd + 1] esize elements in
    (* VLD1<c>.<size> <list>, [<Rn>{:align>}]{!} *)
    (* VLD1<c>.<size> <list>, [<Rn>{:align>}], <Rm> *)
    VectorLoadOne (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)

  (* < 31><1>1D10<rn><vd>sz00<ia><rm>  VLD1 (single elt to one lane *)
  | 26 | 30 when (b 9 8) = 0 ->
    let sz = b 11 10 in
    let index_align = b 7 4 in
    let rnreg = b 19 16 in
    let rn = arm_register_op (get_arm_reg rnreg) in
    let rmreg = b 3 0 in
    let rm = get_arm_reg rmreg in
    let rmop = arm_register_op rm RD in
    let d = bv 22 in
    let vd = prefix_bit d (b 15 12) in
    let (ebytes, esize, index, alignment) =
      match sz with
      | 0 -> (1, 8, index_align lsr 1, 1)
      | 1 -> (2, 16, index_align lsr 2, 16)
      | 2 -> (4, 32, index_align lsr 3, 1)
      | _ -> raise (BCH_failure (STR "VectorLoadOne: not reachable")) in
    let (wb, wback) =
      match rmreg with
      | 15 -> (false, SIMDNoWriteback)
      | 13 -> (true, SIMDBytesTransferred ebytes)
      | _ -> (true, SIMDAddressOffsetRegister rm) in
    let rnop = if wb then rn WR else rn RD in
    let mem = mk_arm_simd_address_op (get_arm_reg rnreg) alignment wback in
    let rlist = arm_simd_reg_elt_list_op XDouble [vd] index esize in
    (* VLD1<c>.<size> <list>, [<Rn>{:align}]{!} *)
    (* VLD1<c>.<size> <list>, [<Tn>{:align}], <Rm> *)
    VectorLoadOne (wb, cc, VfpSize esize, rlist WR, rnop, mem RD, rmop)

  (* < 31>00< 27><rn><rt><--imm12--->   LDRSH (immediate) - T1 *)
  | 27 ->
     let imm12 = b 11 0 in
     let imm = arm_immediate_op (TR.tget_ok (signed_immediate_from_int imm12)) in
     let offset = ARMImmOffset imm12 in
     let mem =
       mk_arm_offset_address_op
         rnreg offset ~size:2 ~align:2 ~isadd:true ~isindex:true ~iswback:false in
     (* LDRSH<c> <Rt>, [<Rn>, #<imm12>] *)
     LoadRegisterSignedHalfword (cc, rt WR, rn RD, imm, mem RD, false)

  | s ->
     NotRecognized ("parse_thumb32_31_0:" ^ (string_of_int s), instr)


let parse_thumb32_31_1
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_ch: pushback_stream_int)
      (_iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let rnreg = get_arm_reg (b 19 16) in
  let rn = arm_register_op rnreg in
  let rd = arm_register_op (get_arm_reg (b 11 8)) in
  let rm = arm_register_op (get_arm_reg (b 3 0)) in

  match (b 24 20) with
  (* < 31>01<  0><15><15><rd>10ro<rm>   SXTH - T2 *)
  | 0 when (b 19 16) = 15 && (b 15 12) = 15 && (b 7 6) = 2 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rotation = (b 5 4) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg (b 3 0)) rotation in
     (* SXTH.W <Rd>, <Rm>{, <rotation>} *)
     SignedExtendHalfword (cc, rd WR, rm RD, true)

  (* < 31>010000S<rn><15><rd>0000<rm>   LSL (register) - T2 *)
  | 0 | 1 when (b 15 12) = 15 && (b 7 4) = 0 ->
     let setflags = (b 20 20) = 1 in
     (* LSL{S}<c>.W <Rd>, <Rn>, <Rm> *)
     LogicalShiftLeft (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 31>01<  1><15><15><rd>10ro<rm>   UXTH.W - T2 *)
  | 1 when (b 19 16) = 15 && (b 15 12) = 15 && (b 7 6) = 2 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rotation = (b 5 4) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg (b 3 0)) rotation in
     (* UXTH.W <Rd>, <Rm>{, <rotation>} *)
     UnsignedExtendHalfword (cc, rd WR, rm RD, true)

  (* < 31>01<  1><rn><15><rd>10ro<rm>  UXTAH - T1 *)
  | 1 when (b 15 12) = 15 && (b 7 6) = 2 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rotation = (b 5 4) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg (b 3 0)) rotation in
     (* UXTAH<c> <Rd>, <Rn>, <Rm>{, <rotation>} *)
     UnsignedExtendAddHalfword (cc, rd WR, rn RD, rm RD)

  (* < 31>010001S<rn><15><rd>0000<rm>   LSR (register) - T2 *)
  | 2 | 3 when (b 15 12) = 15 && (b 7 4) = 0 ->
     let setflags = (b 20 20) = 1 in
     (* LSR{S}<c>.W <Rd>, <Rn>, <Rm> *)
     LogicalShiftRight (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 31>010010S<rn><15><rd>0000<rm>   ASR (register) - T2 *)
  | 4 | 5 when (b 15 12) = 15 && (b 7 4) = 0 ->
     let setflags = (b 20 20) = 1 in
     (* ASR{S}<c>.W <Rd>, <Rn>, <Rm> *)
     ArithmeticShiftRight (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 31><2><3>S<rn><15><rd>< 0><rm>   ROR (register) - T2 *)
  | 6 | 7 when (b 15 12) = 15 && (b 7 4) = 0 ->
     let setflags = (b 20 20) = 1 in
     (* ROR{S}.W <Rd>, <Rn>, <Rm> *)
     RotateRight (setflags, cc, rd WR, rn RD, rm RD, true)

  (* < 31>01<  4><15><15><rd>10ro<rm>   SXTB.W - T2 *)
  | 4 when (b 19 16) = 15 && (b 15 12) = 15 && (b 7 6) = 2 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rotation = (b 5 4) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg (b 3 0)) rotation in
     (* SXTB<c>.W <Rd>, <Rm>{, rotation} *)
     SignedExtendByte (cc, rd WR, rm RD, true)

  (* < 31>01<  5><15><15><rd>10ro<rm>   UXTB.W - T2 *)
  | 5 when (b 19 16) = 15 && (b 15 12) = 15 && (b 7 6) = 2 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rotation = (b 5 4) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg (b 3 0)) rotation in
     (* UXTB<c>.W <Rd>, <Rm>{, rotation} *)
     UnsignedExtendByte (cc, rd WR, rm RD, true)

  (* < 31>01<  5><rn><15><rd>10ro<rm>   UXTAB - T1 *)
  | 5 when (b 15 12) = 15 && (b 7 6) = 2 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rotation = (b 5 4) lsl 3 in
     let rm = mk_arm_rotated_register_op (get_arm_reg (b 3 0)) rotation in
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* UXTAB<c> <Rd>, <Rn>, <Rm>{, rotation} *)
     UnsignedExtendAddByte (cc, rd WR, rn RD, rm RD)

  (* < 31><2>< 8><rn><15><rd>< 4><rm>   UADD8 - T1 *)
  | 8 when (b 15 12) = 15 && (b 7 4) = 4 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     UnsignedAdd8 (cc, rd WR, rn RD, rm RD)

  (* < 31><2>< 9><rm><15><rd>< 8><rm>   REV.W - T2 *)
  | 9 when (b 15 12) = 15 && (b 7 4) = 8 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* REV<c>.W <Rd>, <Rm>  *)
     ByteReverseWord (cc, rd WR, rm RD, true)

  (* < 31><2>< 9><rm><15><rd>< 9><rm>   REV16.W - T2 *)
  | 9 when (b 15 12) = 15 && (b 7 4) = 9 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* REV16<c>.W <Rd>, <Rm>  *)
     ByteReversePackedHalfword (cc, rd WR, rm RD, true)

  (* < 31><2>< 9><rm><15><rd><10><rm>   RBIT - T1 *)
  | 9 when (b 15 12) = 15 && (b 7 4) = 10 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* RBIT<c> <Rd>, <Rm> *)
     ReverseBits (cc, rd WR, rm RD)

  (* < 31>01< 10><rn><15><rd>1000<rm>   SEL - T1 *)
  | 10 when (b 15 12) = 15 && (b 7 4) = 8 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* SEL<c> <Rd>, <Rn>, <Rm> *)
     SelectBytes (cc, rd WR, rn RD, rm RD)

  (* < 31>01< 11><rm><15><rd>1000<rm>   CLZ - T1 *)
  | 11 when (b 15 12) = 15 && (b 7 4) = 8 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* CLZ<c> <Rd>, <Rm> *)
     CountLeadingZeros (cc, rd WR, rm RD)

  (* < 31>01< 12><rn><15><rd>0101<rm>   UQSUB8 - T1 *)
  | 12 when (b 15 12) = 15 && (b 7 4) = 5 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* UQSUB8<c> <Rd>, <Rn>, <Rm> *)
     UnsignedSaturatingSubtract8 (cc, rd WR, rn RD, rm RD)

  (* < 31>01< 16><rn><15><rd>0000<rm>   MUL - T2 *)
  | 16 when (b 15 12) = 15 && (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* MUL<c> <Rd>, <Rn>, <Rm> *)
     Multiply (false, cc, rd WR, rn RD, rm RD)

  (* < 31>01< 16><rn><ra><rd>0000<rm>   MLA - T1 *)
  | 16 when (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let ra = arm_register_op (get_arm_reg (b 15 12)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* MLA<c> <Rd>, <Rn>, <Rm>, <Ra> *)
     MultiplyAccumulate (false, cc, rd WR, rn RD, rm RD, ra RD)

  (* < 31>01< 16><rn><ra><rd>0001<rm>   MLS - T1 *)
  | 16 when (b 7 4) = 1 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let ra = arm_register_op (get_arm_reg (b 15 12)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* MLS<c> <Rd>, <Rn>, <Rm>, <Ra> *)
     MultiplySubtract (cc, rd WR, rn RD, rm RD, ra RD)

  (* < 31>01< 17><rn><ra><rd>0000<rm>   SMLABB - T1 *)
  | 17 when (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let ra = arm_register_op (get_arm_reg (b 15 12)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* MLS<c> <Rd>, <Rn>, <Rm>, <Ra> *)
     SignedMultiplyAccumulateBB (cc, rd WR, rn RD, rm RD, ra RD)

  (* < 31>01< 24><rn><lo><hi>0000<rm>   SMULL - T1 *)
  | 24 when (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rdlo = arm_register_op (get_arm_reg (b 15 12)) in
     let rdhi = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* SMULL<c> <RdLo>, <RdHi>, <Rn>, <Rm> *)
     SignedMultiplyLong (false, cc, rdlo WR, rdhi WR, rn RD, rm RD)

  (* < 31>01< 26><rn><lo><hi>0000<rm>   UMULL - T1 *)
  | 26 when (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rdlo = arm_register_op (get_arm_reg (b 15 12)) in
     let rdhi = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     UnsignedMultiplyLong (false, cc, rdlo WR, rdhi WR, rn RD, rm RD)

  (* < 31><3><11><rn><15><rd><15><rm>   UDIV -- T1 *)
  | 27 when (b 15 12) = 15 && (b 7 4) = 15 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     (* UDIV<c> <Rd>, <Rn>, <Rm> *)
     UnsignedDivide (cc, rd WR, rn RD, rm RD)

  (* < 31>01< 28><rn><rd><rd>0000<rm>   SMLAL - T1 *)
  | 28 when (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rdlo = arm_register_op (get_arm_reg (b 15 12)) in
     let rdhi = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* SMLAL<c> <RdLo>, <RdHi>, <Rn>, <Rm> *)
     SignedMultiplyAccumulateLong (false, cc, rdlo WR, rdhi WR, rn RD, rm RD)

  (* < 31>01< 30><rn><lo><hi>0000<rm>   UMLAL - T1 *)
  | 30 when (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rdlo = arm_register_op (get_arm_reg (b 15 12)) in
     let rdhi = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* UMLAL<c> <RdLo>, <RdHi>, <Rn>, <Rm> *)
     UnsignedMultiplyAccumulateLong (false, cc, rdlo WR, rdhi WR, rn RD, rm RD)

  | s ->
     NotRecognized ("parse_thumb32_31_1:" ^ (string_of_int s), instr)


let parse_thumb32_31_2
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_ch: pushback_stream_int)
      (_iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in
  if (b 11 9) != 5 then
    if (b 24 20) = 5 then
      (* < 31><4>< 5><r2><rt><cp><op><cm>   MRRC - T1 *)
      let coproc = b 11 8 in
      let opc = b 7 4 in
      let crm = b 3 0 in
      let rt = arm_register_op (get_arm_reg (b 15 12)) in
      let rt2 = arm_register_op (get_arm_reg (b 19 16)) in
      (* MRRC2<c> <coproc>, <opc>, <Rt>, <Rt2>, <CRm> *)
      MoveTwoRegisterCoprocessor (cc, coproc, opc, rt WR, rt2 WR, crm)
    else
      let isindex = (bv 24) = 1 in
      let isadd = (bv 23) = 1 in
      let iswback = (bv 21) = 1 in
      let islong = (bv 22) = 1 in
      let crd = b 15 12 in
      let coproc = b 11 8 in
      let imm32 = 4 * (b 7 0) in
      let offset = ARMImmOffset imm32 in
      let rnreg = get_arm_reg (b 19 16) in
      let mem =
        mk_arm_offset_address_op
          ~align:4 rnreg offset ~isadd ~isindex ~iswback in
      if (bv 20) = 0 then
        (* STC2{L}<c> <coproc>, <CRd>, [<Rn>, #+/-<imm>]{!} *)
        StoreCoprocessor (islong, true, cc, coproc, crd, mem WR, None)
      else
        (* LDC2{L}<c> <coproc>, <CRd>, [<Rn>, #+-<imm>}{!} *)
        LoadCoprocessor (islong, true, cc, coproc, crd, mem RD, None)
  else
    match (b 24 20) with
    | s ->
       NotRecognized ("parse_thumb32_31_2:" ^ (string_of_int s), instr)


let parse_thumb32_31_110
      ?(_in_it: bool=false)
      ?(_cc: arm_opcode_cc_t=ACCAlways)
      (_ch: pushback_stream_int)
      (_iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  match (b 22 20) with
  | s ->
     NotRecognized
       ("parse_thumb32_31_110:" ^ (string_of_int s), instr)


let parse_thumb32_31_14
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in

  let isz = b 21 20 in
  let cmode = b 11 8 in
  let q = bv 6 in
  let b4 = bv 4 in
  match (isz, cmode, q, b4) with

  (* < 31><14>D00<vn><vd>< 1>NQM1<vm> *)   (* VEOR - T1 (Q=0) *)
  | (0, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     (* VEOR<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseExclusiveOr (cc, vd WR, vn RD, vm RD)

  (* < 31><14>D00<vn><vd>< 1>NQM1<vm> *)   (* VEOR - T1 (Q=1) *)
  | (0, 1, 1, 1) ->
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

  (* < 31><7>0D00<vn><vd><12>NQM0<vm> *)   (* SHA256H - T1 (v8-crypto) *)
  | (0, 12, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA256H.32 <Qd>, <Qn>, <Qm> *)
     SHA256HashUpdatePart1 (cc, dt, vd WR, vn RD, vm RD)

  (* < 31><7>0D01<vn><vd><12>NQM0<vm> *)   (* SHA256H2 - T1 (v8-crypto) *)
  | (1, 12, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA256H2.32 <Qd>, <Qn>, <Qm> *)
     SHA256HashUpdatePart2 (cc, dt, vd WR, vn RD, vm RD)

  (* < 31><7>0D10<vn><vd><12>NQM0<vm> *)   (* SHA256SU1 - T1 (v8-crypto) *)
  | (2, 12, 1, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA256SU1.32 <Qd>, <Qn>, <Qm> *)
     SHA256ScheduleUpdate1 (cc, dt, vd WR, vn RD, vm RD)

  (* < 31><7>0D01<vn><vd>< 1>N0M1<vm> *)   (* VBSL - T1-64 (v8-crypto) *)
  | (1, 1, 0, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpNone in
     (* VBSL<c> <Dd>, <Dn>, <Dm> *)
     VectorBitwiseSelect (cc, dt, vd WR, vn RD, vm RD)

  (* < 31><7>0D01<vn><vd>< 1>N1M1<vm> *)   (* VBSL - T1-128 (v8-crypto) *)
  | (1, 1, 1, 1) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XQuad (n / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpNone in
     (* VBSL<c> <Qd>, <Qn>, <Qm> *)
     VectorBitwiseSelect (cc, dt, vd WR, vn RD, vm RD)

  (* < 31><7>0Dsz<vn><vd>< 1>NQM0<vm> *)  (* VRHADD - T1-u *)
  | ((0 | 1 | 2), 1, (0 | 1), 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let dt = VfpUnsignedInt (8 lsl isz) in
     if q = 0 then
       let vd = arm_extension_register_op XDouble d in
       let vn = arm_extension_register_op XDouble n in
       let vm = arm_extension_register_op XDouble m in
       (* VRHADD<c>.<dt> <Dd>, <Dn>, <Dm> *)
       VectorRoundingHalvingAdd (cc, dt, vd WR, vn RD, vm RD)
     else
       let vd = arm_extension_register_op XQuad (d / 2) in
       let vn = arm_extension_register_op XQuad (n / 2) in
       let vm = arm_extension_register_op XQuad (m / 2) in
       (* VRHADD<c>.<dt> <Qd>, <Qn>, <Qm> *)
       VectorRoundingHalvingAdd (cc, dt, vd WR, vn RD, vm RD)

  | (3, 1, (0 | 1), 0) ->
     raise
       (ARM_undefined ("Thumb:VRHADD: sz=3 (" ^ iaddr#to_hex_string ^ ")"))

  | (a, b, c, d) ->
     NotRecognized (
         "parse_thumb32_31_14:"
         ^ (string_of_int a)
         ^ "_"
         ^ (string_of_int b)
         ^ "_"
         ^ (string_of_int c)
         ^ "_"
         ^ (string_of_int d), instr)


let parse_thumb32_31_15
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let bv = instr#get_bitval in

  let isz = b 21 20 in
  let cmode = b 11 8 in
  let q = bv 6 in
  let b4 = bv 4 in
  match (isz, cmode, q, b4) with

  (* < 31><15>D000<i><vd><cm>0011<i4) *) (* VORR (immediate) - T1-1 (Q=0) *)
  | (0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 0, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
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

  (* < 31><15>D000<i><vd><cm>0111<i4) *) (* VORR (immediate) - T1-1 (Q=1) *)
  | (0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 1, 1)
       when (bv 19 = 0) && (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in

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

  (* < 31><15>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - T1-1-0 (Q=1) *)
  | (0, cm, 1, 1) when (bv 19) = 0  && (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 cm "VMOV" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, immop)

  (* < 31><15>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - T1-1-1 (Q=0) *)
  | (0, 14, 0, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 14 "VMOV" in
     let vd = arm_extension_register_op XDouble d in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, immop)

  (* < 31><15>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - T1-1-1 (Q=1) *)
  | (0, 14, 1, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 14 "VMOV" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, immop)

  (* < 31><15>D000<i><vd><cm>0001<i4> *) (* VMOV (immediate) - T1-1-0 (Q=0) *)
  | (0, cm, 0, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 cm "VMOV" in
     let vd = arm_extension_register_op XDouble d in
     (* VMOV<c>.<dt> <Dd>, #<imm> *)
     VectorMoveDS (cc, dt, vd WR, immop)

  (* < 31><15>D000<i><vd><cm>0Q11<i4> *)  (* VBIC (immediate) - T1-1 (Q=0) *)
  | (0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 0, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immval = adv_simd_expand_imm 1 cm imm8 in
     let (dt, immop) =
       match cm with
       | 1 | 3 | 5 | 7 ->
          (VfpInt 32, TR.tget_ok (mk_arm_immediate_op false 4 (immval#shift_right 32)))
       | 9 | 11 ->
          VfpInt 16, TR.tget_ok (mk_arm_immediate_op false 4 (immval#shift_right 48))
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:VBIC-immediate: not reachable"])) in
     let vd = arm_extension_register_op XDouble d in
     (* VBIC<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseBitClear (cc, dt, vd WR, vd RD, immop)

  (* < 31><15>D000<i><vd><cm>0Q11<i4> *)  (* VBIC (immediate) - T1-1 (Q=1) *)
  | (0, ((1 | 3 | 5 | 7 | 9 | 11) as cm), 1, 1)
       when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((b 18 16) lsl 4) + (b 3 0) in
     let immval = adv_simd_expand_imm 1 cm imm8 in
     let (dt, immop) =
       match cm with
       | 1 | 3 | 5 | 7 ->
          (VfpInt 32, TR.tget_ok (mk_arm_immediate_op false 4 (immval#shift_right 32)))
       | 9 | 11 ->
          VfpInt 16, TR.tget_ok (mk_arm_immediate_op false 4 (immval#shift_right 48))
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [STR "ARM:VBIC-immediate: not reachable"])) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VBIC<c>.<dt> <Qd>, #<imm> *)
     VectorBitwiseBitClear (cc, dt, vd WR, vd RD, immop)

  (* < 31><15>D000<i><vd><cm>0011<i4> *)  (* VMVN (immediate) - T1-1 (Q=0) *)
  | (0, cm, 0, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let _ =
       if cm = 15 then
         raise (ARM_undefined "VMVN immediate with cmode=15") in
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 cm "VMVN" in
     let vd = arm_extension_register_op XDouble d in
     (* VMVN<c>.<dt> <Dd>, #<imm> *)
     VectorBitwiseNot (cc, dt, vd WR, immop)

  (* < 31><15>D000<i><vd><cm>0111<i4> *)  (* VMVN (immediate) - T1-1 (Q=1) *)
  | (0, cm, 1, 1) when (bv 19) = 0 && (bv 7) = 0 && (bv 5) = 1 ->
     let _ =
       if cm = 15 then
         raise (ARM_undefined "VMVN immediate with cmode=15") in
     let d = prefix_bit (bv 22) (b 15 12) in
     let imm8 = ((bv 24) lsl 7) + ((b 18 16) lsl 4) + (b 3 0) in
     let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
     let dt = adv_simd_mod_dt 0 cm "VMVN" in
     let vd = arm_extension_register_op XQuad (d / 2) in
     (* VMVN<c>.<dt> <Qd>, #<imm> *)
     VectorBitwiseNot (cc, dt, vd WR, immop)

  (* < 31><15>D001000<vd><10>00M1<vm> *) (* VMOVL - T1-u (imm3=1) *)
  | (0, 10, 0, 1) when  (b 19 16) = 8 && (bv 7) = 0 ->
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

  (* < 31><15>D010000<vd><10>00M1<vm> *) (* VMOVL - T1-u (imm3=2) *)
  | (1, 10, 0, 1) when  (b 19 16) = 0 && (bv 7) = 0 ->
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

  (* < 31><15>D100000<vd><10>00M1<vm> *) (* VMOVL - T1-u (imm3=4) *)
  | (2, 10, 0, 1) when  (b 19 16) = 0 && (bv 7) = 0 ->
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

  (* < 31><15>11<i4><vd><12>0QM0<vm> *)  (* VDUP (scalar) - T1 (Q=0) *)
  | (3, 12, 0, 0) when (bv 7) = 0 ->
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

  (* < 31><15>11<i4><vd><12>0QM0<vm> *)  (* VDUP (scalar) - T1 (Q=1) *)
  | (3, 12, 1, 0) when (bv 7) = 0 ->
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

  (* < 31><7>1D11sz10<vd>< 3>10M0<vm>*)   (* SHA1SU1 - T1 (armv8-crypto) *)
  | (3, 3, 0, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1SU1.32 <Qd>, <Qm> *)
     SHA1ScheduleUpdate1 (cc, dt, vd WR, vm RD)

  (* < 31><7>1D11sz10<vd>< 3>11M0<vm>*)   (* SHA256SU0 - T1 (armv8-crypto) *)
  | (3, 3, 1, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA256SU0.32 <Qd>, <Qm> *)
     SHA256ScheduleUpdate0 (cc, dt, vd WR, vm RD)

  (* < 31><15>D11<vn><vd>< 8>N0M0<vm> *)  (* VTBL - T1-1 *)
  | (3, 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let xlst = arm_extension_register_list_op XDouble n 1 in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize 8 in
     (* VTBL<c>.8 <Dd>, <list>, <Dm> *)
     VectorTableLookup (cc, dt, vd WR, xlst RD, vm RD)

  (* < 31><15>D11<vn><vd>< 9>N0M0<vm> *)  (* VTBL - T1-2 *)
  | (3, 9, 0, 0) ->
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

  (* < 31><15>D11<vn><vd><10>N0M0<vm> *)  (* VTBL - T1-3 *)
  | (3, 10, 0, 0) ->
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

  (* < 31><15>D11<vn><vd><11>N0M0<vm> *)  (* VTBL - T1-4 *)
  | (3, 11, 0, 0) ->
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

  (* <31><15>D11sz00<vd>< 0>0QM0<vm> *)   (* VREV64 - T1 (Q=0) *)
  | (3, 0, 0, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VREV64.<size> <Dd>, <Dm> *)
     VectorReverseDoublewords (cc, dt, vd WR, vm RD)

  (* <31><15>D11sz00<vd>< 0>0QM0<vm> *)   (* VREV64 - T1 (Q=1) *)
  | (3, 0, 1, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VREV64.<size> <Qd>, <Qm> *)
     VectorReverseDoublewords (cc, dt, vd WR, vm RD)

  (* <31><15>D11sz00<vd>< 0>1QM0<vm> *)   (* VREV32 - T1 (Q=0) *)
  | (3, 0, 0, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let sz = b 19 18 in
     let dt = VfpSize (8 lsl sz) in
     (* VREV32.<size> <Dd>, <Dm> *)
     VectorReverseWords (cc, dt, vd WR, vm RD)

  (* <31><15>D11sz00<vd>< 0>1QM0<vm> *)   (* VREV32 - T1 (Q=1) *)
  | (3, 0, 1, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let sz = b 19 18 in
     let dt = VfpSize (8 lsl sz) in
     (* VREV32.<size> <Qd>, <Qm> *)
     VectorReverseWords (cc, dt, vd WR, vm RD)

  (* <31><15>D11sz00<vd>< 1>0QM0<vm> *)   (* VREV16 - T1 (Q=0) *)
  | (3, 1, 0, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let sz = b 19 18 in
     let dt = VfpSize (8 lsl sz) in
     (* VREV16.<size> <Dd>, <Dm> *)
     VectorReverseHalfwords (cc, dt, vd WR, vm RD)

  (* <31><15>D11sz00<vd>< 1>0QM0<vm> *)   (* VREV16 - T1 (Q=1) *)
  | (3, 1, 1, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let sz = b 19 18 in
     let dt = VfpSize (8 lsl sz) in
     (* VREV16.<size> <Qd>, <Qm> *)
     VectorReverseHalfwords (cc, dt, vd WR, vm RD)

  (* <31><15>D11sz10<vd>< 0>1QM0<vm> *)   (* VTRN - T1 (Q=0) *)
  | (3, 0, 0, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VTRN.<size> <Dd>, <Dm> *)
     VectorTranspose (cc, dt, vd WR, vm RD)

  (* <31><15>D11sz10<vd>< 0>1QM0<vm> *)   (* VTRN - T1 (Q=1) *)
  | (3, 0, 1, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VTRN.<size> <Qd>, <Qm> *)
     VectorTranspose (cc, dt, vd WR, vm RD)

  (* <31><15>D11sz10<vd>< 1>1QM0<vm> *)   (* VZIP - T1 (Q=0) *)
  | (3, 1, 0, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VZIP.<size> <Dd>, <Dm> *)
     VectorZip (cc, dt, vd RW, vm RW)

  (* <31><15>D11sz10<vd>< 1>1QM0<vm> *)   (* VZIP - T1 (Q=1) *)
  | (3, 1, 1, 0) when (b 17 16) = 2 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize (8 lsl (b 19 18)) in
     (* VZIP.<size> <Qd>, <Qm> *)
     VectorZip (cc, dt, vd RW, vm RW)

  (* <31><15>D11sz10<vd>< 2>00M0<vm> *)   (* VMOVN - T1 *)
  | (3, 2, 0, 0) when (b 17 16) = 2 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let sz = b 19 18 in
     let vd = arm_extension_register_op XDouble d in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt =
       match sz with
       | 0 -> VfpInt 16
       | 1 -> VfpInt 32
       | 2 -> VfpInt 64
       | _ -> raise (ARM_undefined ("VMOVN: sz > 2")) in
     (* VMOVN.<size> <Dd>, <Qm> *)
     VectorMoveNarrow (cc, dt, vd WR, vm RD)

  (* < 31><15>D11sz00<vd>< 3>00M0<vm> *) (* AESE - T1 *)
  | (3, 3, 0, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 8 in
     (* AESE.<dt> <Qd>, <Qm> *)
     AESSingleRoundEncryption (cc, dt, vd WR, vm RD)

  (* < 31><15>D11sz00<vd>< 3>01M0<vm> *) (* AESD - T1 *)
  | (3, 3, 1, 0) when (b 17 16) = 0 && (bv 7) = 0 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 8 in
     (* AESE.<dt> <Qd>, <Qm> *)
     AESSingleRoundDecryption (cc, dt, vd WR, vm RD)

  (* < 31><15>D11sz00<vd>< 3>10M0<vm> *) (* AESMC - T1 *)
  | (3, 3, 0, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 8 in
     (* AESMC.<dt> <Qd>, <Qm> *)
     AESMixColumns (cc, dt, vd WR, vm RD)

  (* < 31><15>D11sz00<vd>< 3>11M0<vm> *) (* AESIMC - T1 *)
  | (3, 3, 1, 0) when (b 17 16) = 0 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 8 in
     (* AESIMC.<dt> <Qd>, <Qm> *)
     AESInverseMixColumns (cc, dt, vd WR, vm RD)

  (* < 31><15>D11sz01<vd>< 2>11M0<vm> *)  (* SHA1H - T1 *)
  | (3, 2, 1, 0) when (b 17 16) = 1 && (bv 7) = 1 ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vm = arm_extension_register_op XQuad (m / 2) in
     let dt = VfpSize 32 in
     (* SHA1H.<dt> <Qd>, <Qm> *)
     SHA1FixedRotate (cc, dt, vd WR, vm RD)

  (* <31><15>D<imm6><vd>< 0>LQM1<vm> *)   (* VSHR - T1-u (Q=0) *)
  | (_sz, 0, 0, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
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
                    STR "31:VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpUnsignedInt esize in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSHR(T1-u, Q=0) at "; iaddr#toPretty]))
         (mk_arm_immediate_op false 4 (mkNumerical sam)) in
     (* VSHR<c>.<dt> <Dd>, <Dm>, #<imm> *)
     VectorShiftRight (cc, dt, vd WR, vm RD, imm)

  (* <31><15>D<imm6><vd>< 0>LQM1<vm> *)   (* VSHR - T1-u (Q=1) *)
  | (_sz, 0, 1, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
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
                    STR "31:VSHR: ";
                    INT (bv 7);
                    STR ", ";
                    INT (b 21 19)])) in
     let dt = VfpUnsignedInt esize in
     let imm =
       fail_tvalue
         (trerror_record
            (LBLOCK [STR "VSHR(T1-u, Q=1) at "; iaddr#toPretty]))
         (mk_arm_immediate_op false 4 (mkNumerical sam)) in
     (* VSHR<c>.<dt> <Qd>, <Qm>, #<imm> *)
     VectorShiftRight (cc, dt, vd WR, vm RD, imm)

  (* <31><15>D<imm6><vd>< 4>LQM1<vm> *)  (* VSRI - T1 (Q=0) *)
  | (_, 4, 0, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
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
       let imm =
         fail_tvalue
           (trerror_record
              (LBLOCK [STR "VSRI(T1, Q=0) at "; iaddr#toPretty]))
           (mk_arm_immediate_op false 4 (mkNumerical sam)) in
       (* VSRI<c>.<size> <Dd>, <Dm>, #<imm> *)
       VectorShiftRightInsert (cc, dt, vd WR, vm RD, imm)

  (* <31><15>D<imm6><vd>< 4>LQM1<vm> *)  (* VSRI - T1 (Q=1) *)
  | (_, 4, 1, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
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
       let imm =
         fail_tvalue
           (trerror_record
              (LBLOCK [STR "VSRI(T1, Q=1) at "; iaddr#toPretty]))
           (mk_arm_immediate_op false 4 (mkNumerical sam)) in
       (* VSRI<c>.<size> <Qd>, <Qm>, #<imm> *)
       VectorShiftRightInsert (cc, dt, vd WR, vm RD, imm)

  (* <31><15>D<imm6><vd>< 5>LQM1<vm> *)  (* VSLI - T1 (Q=0) *)
  | (_, 5, 0, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
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
                      STR "31:VSLI: ";
                      INT (bv 7);
                      STR ", ";
                      INT (b 21 19)])) in
       let dt = VfpSize esize in
       let imm =
         fail_tvalue
           (trerror_record
              (LBLOCK [STR "VSLI(T1, Q=0) at "; iaddr#toPretty]))
           (mk_arm_immediate_op false 4 (mkNumerical sam)) in
       (* VSLI<c>.<size> <Dd>, <Dm>, #<imm> *)
       VectorShiftLeftInsert (cc, dt, vd WR, vm RD, imm)

  (* <31><15>D<imm6><vd>< 5>LQM1<vm> *)  (* VSLI - T1 (Q=1) *)
  | (_, 5, 1, 1) when ((bv 7) = 1 || (b 21 19) > 0) ->
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
                      STR "31:VSLI: ";
                      INT (bv 7);
                      STR ", ";
                      INT (b 21 19)])) in
       let dt = VfpSize esize in
       let imm =
         fail_tvalue
           (trerror_record
              (LBLOCK [STR "VSLI(T1, Q=1) at "; iaddr#toPretty]))
           (mk_arm_immediate_op false 4 (mkNumerical sam)) in
       (* VSLI<c>.<size> <Qd>, <Qm>, #<imm> *)
       VectorShiftLeftInsert (cc, dt, vd WR, vm RD, imm)

  (* <31><15>Dsz<vn><vd>< 0>N0M0<vm> *)  (* VADDL - T1-u *)
  | (((0 | 1 | 2) as sz), 0, 0, 0) ->
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

  (* <31><15>Dsz<vn><vd>< 1>N0M0<vm> *)  (* VADDW - T1-u *)
  | (((0 | 1 | 2) as sz), 1, 0, 0) ->
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

  (* <31><15>Dsz<vn><vd>< 2>N1M0<vm> *)   (* VMLAL (by scalar) - T2 (sz=1) *)
  | (1, 2, 1, 0) ->
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

  (* <31><15>Dsz<vn><vd>< 2>N1M0<vm> *)   (* VMLAL (by scalar) - T2 (sz=2) *)
  | (2, 2, 1, 0) ->
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

  (* <31><15>Dsz<vn><vd>< 8>N0M0<vm> *)   (* VMLAL (integer) - T2-u *)
  | (((0 | 1 | 2) as sz), 8, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt (8 lsl sz) in
     (* VMLAL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorMultiplyAccumulateLong (cc, dt, vd WR, vn RD, vm RD)

  (* <31><15>Dsz<vn><vd><10>N1M0<vm> *)   (* VMULL (by scalar) - T2 (sz=1) *)
  | (1, 10, 1, 0) ->
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

  (* <31><15>Dsz<vn><vd><10>N1M0<vm> *)   (* VMULL (by scalar) - T2 (sz=2) *)
  | (2, 10, 1, 0) ->
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

  (* <31><15>Dsz<vn><vd><12>N0M0<vm> *)   (* VMULL (integer) - T2-u *)
  | (((0 | 1 | 2) as sz), 12, 0, 0) ->
     let d = prefix_bit (bv 22) (b 15 12) in
     let n = prefix_bit (bv 7) (b 19 16) in
     let m = prefix_bit (bv 5) (b 3 0) in
     let vd = arm_extension_register_op XQuad (d / 2) in
     let vn = arm_extension_register_op XDouble n in
     let vm = arm_extension_register_op XDouble m in
     let dt = VfpUnsignedInt (8 lsl sz) in
     (* VMULL<c>.<dt> <Qd>, <Dn>, <Dm> *)
     VectorMultiplyLong (cc, dt, vd WR, vn RD, vm RD)

  | (a, b, c, d) ->
     NotRecognized (
         "parse_thumb32_31_15:"
         ^ (string_of_int a)
         ^ "_"
         ^ (string_of_int b)
         ^ "_"
         ^ (string_of_int c)
         ^ "_"
         ^ (string_of_int d), instr)


let parse_thumb32_opcode
      ?(in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  match (b 31 27) with
  | 29 ->
     (match (b 26 25) with
      | 0 -> parse_thumb32_29_0 ~_in_it:in_it ~cc ch iaddr instr
      | 1 -> parse_thumb32_29_1 ~_in_it:in_it ~cc ch iaddr instr
      | 2 -> parse_thumb32_29_2 ~_in_it:in_it ~cc ch iaddr instr
      | 3 ->
         (match (b 24 23) with
          | 0 | 1 -> parse_thumb32_29_110 ~in_it ~cc ch iaddr instr
          | 2 -> parse_thumb32_29_14 ~_in_it:in_it ~cc ch iaddr instr
          | 3 -> parse_thumb32_29_15 ~_in_it:in_it ~cc ch iaddr instr
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [STR "Unexpected value in parse_thumb32:29"])))
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [STR "Unexpected value in parse_thumb32:29"])))

  | 30 -> parse_thumb32_30 ~in_it ~cc ch iaddr instr
  | 31 ->
     (match (b 26 25) with
      | 0 ->  parse_thumb32_31_0 ~_in_it:in_it ~cc ch iaddr instr
      | 1 ->  parse_thumb32_31_1 ~_in_it:in_it ~cc ch iaddr instr
      | 2 ->  parse_thumb32_31_2 ~_in_it:in_it ~cc ch iaddr instr
      | 3 ->
         (match (b 24 23) with
          | 0 | 1 -> parse_thumb32_31_110 ~_in_it:in_it ~_cc:cc ch iaddr instr
          | 2 -> parse_thumb32_31_14 ~_in_it:in_it ~cc ch iaddr instr
          | 3 -> parse_thumb32_31_15 ~_in_it:in_it ~cc ch iaddr instr
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [STR "Unexpected value in parse_thumb32:31"])))
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [STR "Unexpected value in parse_thumb32:31"])))
  | p ->
     raise
       (BCH_failure
          (LBLOCK [STR "Unexpected prefix in parse_thumb32_opcode: "; INT p]))


let parse_t16_00
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let r (i: int) (m: arm_operand_mode_t) =
    match i with
    | 0 -> arm_register_op (get_arm_reg (b 10 8)) m
    | 1 -> arm_register_op (get_arm_reg (b 8 6)) m
    | 2 -> arm_register_op (get_arm_reg (b 5 3)) m
    | 3 -> arm_register_op (get_arm_reg (b 2 0)) m
    | _ -> raise (BCH_failure (LBLOCK [STR "reg: "; INT i])) in
  let imm3 () =
    let i = TR.tget_ok (make_immediate false 4 (mkNumerical (b 8 6))) in
    arm_immediate_op i in
  let imm5 ty =
    let (_, shift_n) = decode_imm_shift ty (b 10 6) in
    let i = TR.tget_ok (make_immediate false 4 (mkNumerical shift_n)) in
    arm_immediate_op i in
  let imm8 () =
    let i = TR.tget_ok (make_immediate false 4 (mkNumerical (b 7 0))) in
    arm_immediate_op i in

  match (b 13 11) with

  (* 0000000000<r><r>  MOV (register) - T1 *)
  | 0 when (b 10 6) = 0 ->
     let _ = if in_it then unpredictable iaddr "MOV (register) in IT block" in
     (* MOVS <Rd>, <Rm> *)
     Move (true, cc, r 3 WR, r 2 RD, false, false)

  (* 00000<im5><r><r>  LSL (immediate) - T1 *)
  | 0 ->
  (* LSLS <Rd>, <Rm>, #<imm> (outside IT block) *)
  (* LSL<c> <Rd>, <Rm>, #<imm> (inside IT block) *)
     LogicalShiftLeft (not in_it, cc, r 3 WR, r 2 RD, imm5 0, false)

  (* 00001<im5><r><r>  LSR (immediate) - T1 *)
  | 1 ->
     (* LSRS <Rd>, <Rm>, #<imm> (outside IT block) *)
     (* LSR<c> <Rd>, <Rm>, #<imm> (inside IT block) *)
     LogicalShiftRight (not in_it, cc, r 3 WR, r 2 RD, imm5 1, false)

  (* 00010<im5><r><r>  ASR (immediate) - T1 *)
  | 2 ->
     (* ASRS <Rd>, <Rm>, #<imm> (outside IT block) *)
     (* ASR<c> <Rd>, <Rm>, #<imm> (inside IT block) *)
     ArithmeticShiftRight (not in_it, cc, r 3 WR, r 2 RD, imm5 2, false)

  (* 0001100<r><r><r>  ADD (register) - T1 *)
  | 3 when (b 10 9) = 0 ->
     (* ADDS <Rd>, <Rn>, <Rm> (outside IT block) *)
     (* ADD<c> <Rd>, <Rn>, <Rm> (inside IT block) *)
     Add (not in_it, cc, r 3 WR, r 2 RD, r 1 RD, false)

  (* 0001101<r><r><r>  SUB (register) - T1 *)
  | 3 when (b 10 9) = 1 ->
     (* SUBS <Rd>, <Rn>, <Rm> (outside IT block) *)
     (* SUB<c> <Rd>, <Rn>, <Rm> (inside IT block) *)
     Subtract (not in_it, cc, r 3 WR, r 2 RD, r 1 RD, false, false)

  (* 0001110<i><r><r>  ADD (immediate) - T1 *)
  | 3 when (b 10 9) = 2 ->
     (* ADDS <Rd>, <Rn>, #<imm3> (outside IT block) *)
     (* ADD<c> <Rd>, <Rn>, #<imm3> (inside IT block) *)
     Add (not in_it, cc, r 3 WR, r 2 RD, imm3 (), false)

  (* 0001111<i><r><r>  SUB (immediate) - T1 *)
  | 3 when (b 10 9) = 3 ->
     (* SUBS <Rd>, <Rn>, #<imm3> (outside IT block) *)
     (* SUB<c> <Rd>, <Rn>, #<imm3> (inside IT block) *)
     Subtract (not in_it, cc, r 3 WR, r 2 RD, imm3 (), false, false)

  (* 00100<r><-imm8->  MOV (immediate) - T1 *)
  | 4 ->
     (* MOVS <Rd>, #<imm8> (outside IT block) *)
     (* MOV<c> <Rd>, #<imm8> (inside IT block) *)
     Move (not in_it, cc, r 0 WR, imm8 (), false, false)

  (* 00101<r><-imm8->  CMP (immediate) - T1 *)
  | 5 ->
     (* CMP<c> <Rn>, #<imm8> *)
     Compare (cc, r 0 WR, imm8 (), false)

  (* 00110<r><-imm8->  ADD (immediate) - T2 *)
  | 6 ->
     (* ADDS <Rdn>, #<imm8>  (outside IT block) *)
     (* ADD<c> <Rdn>, #<imm8>  (inside IT block) *)
     Add (not in_it, cc, r 0 WR, r 0 RD, imm8 (), false)

  (* 00111<r><-imm8->  SUB (immediate) - T2 *)
  | 7 ->
     (* SUBS <Rdn>, #<imm8> (outside IT block) *)
     (* SUB<c> <Rdn>, #<imm8> (inside IT block) *)
     Subtract (not in_it, cc, r 0 WR, r 0 RD, imm8 (), false, false)

  | tag -> NotRecognized ("t16_00:" ^ (stri tag), instr)


let parse_t16_01
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let r (i: int) (m: arm_operand_mode_t) =
    match i with
    | 0 -> arm_register_op (get_arm_reg (b 5 3)) m
    | 1 -> arm_register_op (get_arm_reg (b 2 0)) m
    | _ -> raise (BCH_failure (LBLOCK [STR "reg: "; INT i])) in
  match (b 9 6) with

(* 0100000000<r><r>  AND (register) - T1 *)
  | 0 ->
     (* ANDS <Rdn>, <Rm> (outside IT block) *)
     (* AND<c> <Rdn>, <Rm> (inside IT block) *)
     BitwiseAnd (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000001<r><r>  EOR (register) - T1 *)
  | 1 ->
     (* EORS <Rdn>, <Rm> (outside IT block) *)
     (* EOR<c>, <Rdn>, <Rm> (inside IT block) *)
     BitwiseExclusiveOr (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000010<r><r>  LSL (register) - T1 *)
  | 2 ->
     (* LSLS <Rdn>, <Rm> (outside IT block) *)
     (* LSL<c> <Rdn>, <Rm> (inside IT block) *)
     LogicalShiftLeft (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000011<r><r>  LSR (register) - T1 *)
  | 3 ->
     (* LSRS <Rdn>, <Rm> (outside IT block) *)
     (* LSR<c> <Rdn>, <Rm> (inside IT block) *)
     LogicalShiftRight (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000100<r><r>  ASR (register) - T1 *)
  | 4 ->
     (* ASRS <Rdn>, <Rm> (outside IT block) *)
     (* ASR<c> <Rdn>, <Rm> (inside IT block) *)
     ArithmeticShiftRight (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000101<r><r>  ADC (register) - T1 *)
  | 5 ->
     (* ADCS <Rdn>, <Rm> (outside IT block) *)
     (* ADC<c> <Rdn>, <Rm> (inside IT block) *)
     AddCarry (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000110<r><r>  SBC (register) - T1 *)
  | 6 ->
     (* SBCS <Rdn>, <Rm> (outside IT block) *)
     (* SBC<c> <Rdn>, <Rm> (inside IT block) *)
     SubtractCarry (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000111<r><r>  ROR (register) - T1 *)
  | 7 ->
     (* RORS <Rdn>, <Rm> (outside IT block) *)
     (* ROR<c> <Rdn>, <Rm> (inside IT block) *)
     RotateRight (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100001000<r><r>  TST (register) - T1 *)
  | 8 ->
     (* TST<c> <Rn>, <Rm> *)
     Test (cc, r 1 RD, r 0 RD, false)

  (* 0100001001<r><r>  RSB (immediate) - T1 *)
  | 9 ->
     (* RSBS <Rd>, <Rn>, #0 (inside IT block *)
     (* RSB<c> <Rd>, <Rn>, #0 (outside IT block *)
     let imm0 = arm_immediate_op imm0 in
     ReverseSubtract (not in_it, cc, r 1 WR, r 0 RD, imm0, false)

  (* 0100001010<r><r>  CMP (register) - T1 *)
  | 10 ->
  (* CMP<c> <Rn>, <Rm> *)
     Compare (cc, r 1 RD, r 0 RD, false)

  (* 0100001011<r><r>  CMN (register) - T1 *)
  | 11 ->
     (* CMN<c> <Rn>, <Rm> *)
     CompareNegative (cc, r 1 RD, r 0 RD)

  (* 0100001100<r><r>  ORR (register) - T1 *)
  | 12 ->
     (* ORRS <Rdn>, <Rm> (outside IT block) *)
     (* ORR<c> <Rdn>, <Rm> (inside IT block_ *)
     BitwiseOr (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100001101<r><r>  MUL - T1 *)
  | 13 ->
     (* MULS <Rdm>, <Rn>, <Rdm> (outside IT block) *)
     (* MUL<c> <Rdm>, <Rn>, <Rdm> (inside IT block) *)
     Multiply (not in_it, cc, r 1 WR, r 0 RD, r 1 RD)

  (* 0100001110<r><r>  BIC (register) - T1 *)
  | 14 ->
     (* BICS <Rdn>, <Rm> (outside IT block) *)
     (* BIC<c> <Rdn>, <Rm> (inside IT block) *)
     BitwiseBitClear (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100001111<r><r>  MVN (register) - T1 *)
  | 15 ->
     (* MVNS <Rd>, <Rm> (outside IT block) *)
     (* MVN<c> <Rd>, <Rm> (inside IT block) *)
     BitwiseNot (not in_it, cc, r 1 WR, r 1 RD, false)

  | tag -> NotRecognized ("t16_01:" ^ (stri tag) , instr)


let parse_t16_01_1
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let r (i: int) (m: arm_operand_mode_t) =
    match i with
    | 0 -> arm_register_op (get_arm_reg (b 6 3)) m
    | 1 -> arm_register_op (get_arm_reg (b 2 0)) m
    | 2 -> arm_register_op (get_arm_reg (b 8 6)) m
    | 3 -> arm_register_op (get_arm_reg (b 5 3)) m
    | 13 -> arm_register_op (get_arm_reg 13) m
    | _ -> raise (BCH_failure (LBLOCK [STR "reg: "; INT i])) in
  let rr (i: int) (m: arm_operand_mode_t) =
    arm_register_op (get_arm_reg i) m in
  match (b 9 8) with

  (* 010001001<rm>101  ADD (SP plus register) - T2 *)
  | 0 when (b 7 7) = 1 && (b 2 0) = 5 ->
     (* ADD<c> SP, <Rm> *)
     Add (false, cc, r 13 WR, r 13 RD, r 0 RD, false)

  (* 01000100D<13><r>  ADD (SP plus register) - T1 *)
  | 0 when (b 6 3) = 13 ->
     let d = rr ((8 * (b 7 7)) + (b 2 0)) in
     (* ADD<c> <Rdm>, SP, <Rdm> *)
     Add (false, cc, d WR, r 13 RD, d RD, false)

  (* 01000100D<rm><r>  ADD (register) - T2 *)
  | 0 ->
     let d = rr ((8 * (b 7 7)) + (b 2 0)) in
     (* ADD<c> <Rdn>, <Rm> *)
     Add (not in_it, cc, d WR, d RD, r 0 RD, false)

  (* 01000101N<rm><r>  CMP (register) - T2 *)
  | 1 ->
     let n = rr ((8 * (b 7 7)) + (b 2 0)) in
     (* CMP<c> <Rn>, <Rm> *)
     Compare (cc, n RD, r 0 RD, false)

  (* 01000110D<rm><r>  MOV (register) - T1 *)
  | 2 ->
     let d = rr ((8 * (b 7 7)) + (b 2 0)) in
     (* MOV<c> <Rd>, <Rm> *)
     Move (false, cc, d WR, r 0 RD, false, false)

  (* 010001110<rm>000  BX - T1 *)
  | 3 when (b 7 7) = 0 ->
     (* BX<c> <Rm> *)
     let regop = r 0 RD in
     (* let _ =
       if regop#is_pc_register then
         system_info#set_arm_thumb_switch (iaddr#add_int 4) "A" in *)
     BranchExchange (cc, regop)

  (* 010001111<rm>000  BLX (register) *)
  | 3 when (b 7 7) = 1 ->
     (* BLX<c> <Rm> *)
     BranchLinkExchange (cc, r 0 RD)

  | tag -> NotRecognized ("t16_01_1:" ^ (stri tag), instr)


let parse_t16_load_store_reg
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let reg (i: int): arm_reg_t = get_arm_reg i in
  let regop (r: arm_reg_t) = arm_register_op r in
  let rmreg = reg (b 8 6) in
  let rm = regop rmreg in
  let rnreg = reg (b 5 3) in
  let rn = regop rnreg in
  let rtreg = reg (b 2 0) in
  let rt = regop rtreg in
  let reg_srt = ARMImmSRT (SRType_LSL, 0) in
  let offset = arm_shifted_index_offset rmreg reg_srt in
  let mem ?(size=4) (mode: arm_operand_mode_t) =
    mk_arm_offset_address_op
      ~size rnreg offset ~isadd:true ~isindex:true ~iswback:false mode in

  match (b 11 9) with

  (* 0101000<r><r><r>  STR (register) - T1 *)
  | 0 ->
     (* STR<c> <Rt>, [<Rn>, <Rm>] *)
     StoreRegister (cc, rt RD, rn RD, rm RD, mem WR, false)

  (* 0101001<r><r><r>  STRH (register) - T1 *)
  | 1 ->
     (* STRH<c> <Rt>, [<Rn>, <Rm>] *)
     StoreRegisterHalfword (cc, rt RD, rn RD, rm RD, mem ~size:2 WR, false)

  (* 0101010<r><r><r>  STRB (register) - T1 *)
  | 2 ->
     (* STRB<c> <Rt>, [<Rn>, <Rm>] *)
     StoreRegisterByte (cc, rt RD, rn RD, rm RD, mem ~size:1 WR, false)

  (* 0101011<r><r><r>  LDRSB (register) - T1 *)
  | 3 ->
     (* LDRSB<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegisterSignedByte (cc, rt WR, rn RD, rm RD, mem ~size:1 RD, false)

  (* 0101100<r><r><r>  LDR (register) - T1 *)
  | 4 ->
     (* LDR<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegister (cc, rt WR, rn RD, rm RD, mem RD, false)

  (* 0101101<r><r><r>  LDRH (register) - T1 *)
  | 5 ->
  (* LDRH<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegisterHalfword (cc, rt WR, rn RD, rm RD, mem ~size:2 RD, false)

  (* 0101110<r><r><r>  LDRB (register) - T1 *)
  | 6 ->
     (* LDRB<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegisterByte (cc, rt WR, rn RD, rm RD, mem ~size:1 RD, false)

  (* 0101111<r><r><r>  LDRSH (register) - T1 *)
  | 7 ->
     (* LDRSH<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegisterSignedHalfword (cc, rt WR, rn RD, rm RD, mem ~size:2 RD, false)

  | tag -> NotRecognized ("t16_load_store_reg:" ^ (stri tag), instr)


let parse_t16_load_literal
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let rt = arm_register_op (get_arm_reg (b 10 8)) WR in
  let pc = arm_register_op (get_arm_reg 15) RD in
  let imm = (4 * (b 7 0)) in
  let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
  let addrop = arm_literal_op (iaddr#add_int 4) imm in
  (* 01001<r><-imm8->    LDR (literal) - T1 *)
  (* LDR<c> <Rt>, <label> *)
  LoadRegister (cc, rt, pc, immop, addrop, false)


let parse_t16_load_store_imm
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      ?(hw: bool=false)
      (_iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let reg (i: int): arm_reg_t = get_arm_reg i in
  let regop (r: arm_reg_t) = arm_register_op r in
  let rnreg = reg (b 5 3) in
  let rn = regop rnreg in
  let rtreg = reg (b 2 0) in
  let rt = regop rtreg in
  let imm (mult: int) =
    arm_immediate_op
      (TR.tget_ok (signed_immediate_from_int (mult * (b 10 6)))) in
  let offset (m:int) = ARMImmOffset (m * (b 10 6)) in
  let mem (mult: int) ?(size=4) (mode: arm_operand_mode_t) =
    mk_arm_offset_address_op
      rnreg (offset mult) ~size ~isadd:true ~isindex:true ~iswback:false mode in

  match (b 12 11) with
  (* 10000<imm><r><r>  STRH (immediate) - T1 *)
  | 0 when hw ->
     let immop = imm 2 in
     (* STRH<c> <Rt>, [<Rn>, #<imm>] *)
     StoreRegisterHalfword (cc, rt RD, rn RD, immop, mem 2 ~size:2 WR, false)

  (* 01100<imm><r><r>  STR (immediate) - T1 *)
  | 0 ->
     let immop = imm 4 in
     (* STR<c> <Rt>, [<Rn>, #<imm>] *)
     StoreRegister (cc, rt RD, rn RD, immop, mem 4 WR, false)

  (* 10001<imm><r><r>  LDRH (immediate) - T1 *)
  | 1 when hw ->
     let immop = imm 2 in
     (* LDRH<c> <Rt>, [<Rn>, #<imm>] - T1 *)
     LoadRegisterHalfword (cc, rt WR, rn RD, immop, mem 2 ~size:2 RD, false)

  (* 01101<imm><r><r>  LDR (immediate) - T1 *)
  | 1 ->
     let immop = imm 4 in
     (* LDR<c> <Rt>, [<Rn>, #<imm>] *)
     LoadRegister (cc, rt WR, rn RD, immop, mem 4 RD, false)

  (* 01110<imm><r><r>  STRB (immediate) - T1 *)
  | 2 ->
     let immop = imm 1 in
     (* STRB<c> <Rt>, [<Rn>, #<imm5>] *)
     StoreRegisterByte (cc, rt RD, rn RD, immop, mem 1 ~size:1 WR, false)

  (* 01111<imm><r><r>  LDRB (immediate) - T1*)
  | 3 ->
     let immop = imm 1 in
     (* LDRB<c> <Rt>, [<Rn>, #<imm5>] *)
     LoadRegisterByte (cc, rt WR, rn RD, immop, mem 1 ~size:1 RD, false)

  | tag -> NotRecognized ("t16_load_store_imm:" ^ (stri tag), instr)


let parse_t16_load_store_imm_relative
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let reg (i: int): arm_reg_t = get_arm_reg i in
  let regop (r: arm_reg_t) = arm_register_op r in
  let rt = regop (reg (b 10 8)) in
  let spreg = reg 13 in
  let sp = regop (reg 13) in
  let offset m = ARMImmOffset (m * (b 7 0)) in
  let imm = TR.tget_ok (make_immediate false 4 (mkNumerical (4 * (b 7 0)))) in
  let immop = arm_immediate_op imm in
  let imm7 = TR.tget_ok (make_immediate false 4 (mkNumerical (4 * (b 6 0)))) in
  let imm7op = arm_immediate_op imm7 in
  let mem (mult: int) m =
    mk_arm_offset_address_op
      spreg (offset mult) ~isadd:true ~isindex:true ~iswback:false m in

  match (b 13 11) with

  (* 10010<r><-imm8->  STR (immediate) - T2 *)
  | 2 ->
     (* STR<c> <Rt>, [SP, #<imm>] *)
     StoreRegister (cc, rt RD, sp RD, immop, mem 4 WR, false)

  (* 10011<r><-imm8->  LDR (immediate) - T2 *)
  | 3 ->
     (* LDR<c> <Rt>, [SP, #<imm>] *)
     LoadRegister (cc, rt WR, sp RD, immop, mem 4 RD, false)

  (* 10100<r><-imm8->  ADR - T1 *)
  | 4 ->
     let imm = align_dw (iaddr#add_int (4 + (4 * (b 7 0)))) 4 in
     (try
        let imm = arm_absolute_op imm in
        (* ADR<c> <Rd>, <label> *)
        Adr (cc, rt WR, imm RD)
      with
      | Invalid_argument s ->
         NotRecognized ("error in ADR (T1): " ^ s, instr))

  (* 10101<r><-imm8->  ADD (SP plus immediate) - T1 *)
  | 5 ->
     (* ADD<c> <Rd>, SP #<imm> *)
     Add (false, cc, rt WR, sp RD, immop, false)

  (* 101100000<imm7->  ADD (SP plus immediate) - T2 *)
  | 6 when (b 10 7) = 0 ->
     (* ADD<c> SP, SP, #<imm> *)
     Add (false, cc, sp WR, sp RD, imm7op, false)

  (* 101100001<imm7->  SUB (SP minus immediate) - T1 *)
  | 6 when (b 10 7) = 1 ->
     (* SUB<c> SP, SP, #<imm> *)
     Subtract (false, cc, sp WR, sp RD, imm7op, false, false)

  | tag ->
     NotRecognized ("t16_load_store_imm_relative:" ^ (stri tag) , instr)


let parse_t16_push_pop
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let regs s = (b 7 0) + ((b 8 8) lsl s) in
  let rlist s = get_reglist_from_int 16 (regs s) in
  let rl s = arm_register_list_op (rlist s) RD in
  let sp = arm_register_op (get_arm_reg 13) RW in
  match (b 11 9) with

  (* 1011010M<rlist->  PUSH - T1 *)
  | 2 ->
     (* PUSH<c> <registers> *)
     Push (cc, sp, rl 14, false)

  (* 1011110p<rlist->  POP - T1 *)
  | 6 ->
     (* POP<c> <registers> *)
     Pop (cc, sp, rl 15, false)

  | _ -> NotRecognized ("t16_push_pop", instr)


let parse_t16_compare_branch
      ?(_in_it: bool=false)
      ?(_cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let imm = ((b 9 9) lsl 6) + (2 * (b 7 3)) in
  let tgtaddr = iaddr#add_int (4 + imm) in
  let tgtop = arm_absolute_op tgtaddr RD in
  let rn = arm_register_op (get_arm_reg (b 2 0)) RD in
  match (b 11 11) with

  (* 101100i1<-i5><r>  CBZ - T1 *)
  | 0 ->
     (try
        (* CBZ <Rn>, <label> *)
        CompareBranchZero (rn, tgtop)
      with
      | Invalid_argument s ->
         NotRecognized ("error in CBZ (T1): " ^ s, instr))

  (* 101110i1<-i5><r>  CBNZ - T1 *)
  | 1 ->
     (try
        (* CBNZ <Rn>, <label> *)
        CompareBranchNonzero (rn, tgtop)
      with
      | Invalid_argument s ->
         NotRecognized ("error in CBNZ (T1): " ^ s, instr))

  | _ -> NotRecognized ("t16_compare_branch", instr)


let parse_t16_misc7
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  match (b 8 8) with

  (* 10111110<-imm8->  BKPT - T1 *)
  | 0 ->
     let imm32 = TR.tget_ok (make_immediate false 4 (mkNumerical (b 7 0))) in
     let immop = arm_immediate_op imm32 in
     (* BKTP #<imm8> *)
     Breakpoint immop

  (* 1011111100000000  NOP - T1 *)
  | 1 when (b 7 0) = 0 ->
     (* NOP<c> *)
     NoOperation cc

  | 1 ->
     let firstcond = b 7 4 in
     let firstcc = get_opcode_cc firstcond in
     let mask = b 3 0 in
     let itconditionlist = get_it_condition_list firstcond mask in
     let _ = itblock#set_condition_list itconditionlist in
     let xyz = itblock#get_xyz in
     (* 10111111<cc><ms>  IT - T1 *)
     (* IT{<x>{<y>{<z>}}} <firstcond> *)
     IfThen (firstcc, xyz)

  | _ ->
     NotRecognized ("t16_misc7", instr)

let parse_t16_bit_extract
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let rd = arm_register_op (get_arm_reg (b 2 0)) in
  let rm = arm_register_op (get_arm_reg (b 5 3)) in
  match (b 7 6) with
  (* 1011001000<r><r>  SXTH - T1 *)
  | 0 ->
  (* SXTH<c> <Rd>, <Rm> *)
     SignedExtendHalfword (cc, rd WR, rm RD, false)

  (* 1011001001<r><r>  SXTB - T1 *)
  | 1 ->
     (* SXTB<c> <Rd>, <Rm> *)
     SignedExtendByte (cc, rd WR, rm RD, false)

  (* 1011001010<r><r>  UXTH - T1 *)
  | 2 ->
     (* UXTH<c> <Rd>, <Rm> *)
     UnsignedExtendHalfword (cc, rd WR, rm RD, false)

  (* 1011001011<r><r>  UXTB - T1 *)
  | 3 ->
     (* UXTB<c> <Rd>, <Rm> *)
     UnsignedExtendByte (cc, rd WR, rm RD, false)

  | tag ->
     NotRecognized ("t16_bit_extract:" ^ (string_of_int tag), instr)


let parse_t16_misc
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let opc = b 11 9 in
  match opc with
  | 2 | 6 -> parse_t16_push_pop ~_in_it:in_it ~cc iaddr instr

  (* 10110110011m0AIF  CPS - T1 *)
  | 3 when (b 8 5) = 3 && (b 3 3) = 0 ->
     let effect = if (b 4 4) = 0 then Interrupt_Enable else Interrupt_Disable in
     let effect = arm_cps_effect_op effect in
     let iflags = get_interrupt_flags (b 2 0) in
     (match iflags with
      | IFlag_None -> NotRecognized ("t16_misc:CPS:zero iflags", instr)
      | _ ->
         let iflags = arm_interrupt_flags_op iflags in
         (* CPS<effect> <iflags> *)
         ChangeProcessorState (cc, effect, iflags, None, false))

  (* 1011101000<m><d>  REV - T1 *)
  | 5 when (b 8 6) = 0 ->
     let rm = arm_register_op (get_arm_reg (b 5 3)) in
     let rd = arm_register_op (get_arm_reg (b 2 0)) in
     (* REV<c> <Rd>, <Rm> *)
     ByteReverseWord (cc, rd WR, rm RD, false)

  (* 1011101001<m><d>  REV16 - T1 *)
  | 5 when (b 8 6) = 1 ->
     let rm = arm_register_op (get_arm_reg (b 5 3)) in
     let rd = arm_register_op (get_arm_reg (b 2 0)) in
     (* REV16<c> <Rd>, <Rm> *)
     ByteReversePackedHalfword (cc, rd WR, rm RD, false)

  | 7 -> parse_t16_misc7 ~_in_it:in_it ~cc iaddr instr

  | _ when (b 8 8) = 1 ->
     parse_t16_compare_branch ~_in_it:in_it ~_cc:cc iaddr instr

  | 1 -> parse_t16_bit_extract ~_in_it:in_it ~cc iaddr instr

  | tag ->
     NotRecognized ("t16_misc_" ^ (string_of_int tag), instr)


let parse_t16_store_load_multiple
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (_iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let rnreg = get_arm_reg (b 10 8) in
  let rn = arm_register_op rnreg in
  let regs = get_reglist_from_int 16 (b 7 0) in
  let rl = arm_register_list_op regs in
  let mmem = mk_arm_mem_multiple_op rnreg (List.length regs) in
  match (b 11 11) with
  (* 11000<r><rlist->  STM/STMIA/STMEA - T1 *)
  | 0 ->
     (* STM<c> <Rn>!, <registers> *)
     StoreMultipleIncrementAfter (true, cc, rn RW, rl RD, mmem WR, false)

  (* 11001<r><rlist->  LDM/LDMIA/LDMFD - T1 *)
  | 1 ->
     (* LDM<c> <Rn>, <registers> *)
     (* LDM<c> <Rn>!, <registers> *)
     let wback = not (List.mem rnreg regs) in
     let regmode = if wback then RW else RD in
     LoadMultipleIncrementAfter (wback, cc, rn regmode, rl WR, mmem RD)

  | _ ->
     NotRecognized ("t16_store_load_multiple", instr)


let parse_t16_conditional
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  match (b 11 8) with
  (* 11011110<-imm8->  UDF - T1 *)
  | 14 ->
     let imm8 =
       arm_immediate_op (TR.tget_ok (signed_immediate_from_int (b 7 0))) in
     (* UDF<c> #<imm8> *)
     PermanentlyUndefined (cc, imm8)

  (* 11011111<-imm8->  SVC - T1 *)
  | 15 ->
     let imm8 =
       arm_immediate_op (TR.tget_ok (signed_immediate_from_int (b 7 0))) in
     (* SVC<c> #<imm8> *)
     SupervisorCall (cc, imm8)

  (* 1101<cc><-imm8->  B - T1 *)
  | cond ->
     let c = get_opcode_cc cond in
     let imm32 = sign_extend 32 9 (2 * (b 7 0)) in
     let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
     let tgt = iaddr#add_int (imm32 + 4) in
     (try
        let tgtop = arm_absolute_op tgt RD in
        (* B<c> <label> *)
        Branch (c, tgtop, false)
      with
      | Invalid_argument s ->
         NotRecognized ("error in B (T1): " ^ s, instr))


let parse_t16_unconditional
      ?(_in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let imm32 = sign_extend 32 12 (2 * (b 10 0)) in
  let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
  let tgt = iaddr#add_int (imm32 + 4) in
  (try
     let tgtop = arm_absolute_op tgt RD in
     (* 11100<--imm11-->    B - T2 *)
     (* B<c> <label> *)
     Branch (cc, tgtop, false)
   with
   | Invalid_argument s ->
      NotRecognized ("error in B (T2): " ^ s, instr))


let parse_thumb16_opcode
      ?(in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (_ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let op = b 15 14 in
  let is_imm_relative () =
    let c1 = b 13 11 in
    let c2 = b 10 8 in
    c1 = 2 || c1 = 3 || c1 = 4 || c1 = 5 || (c1 = 6 && c2 = 0) in
  match op with
  | 0 -> parse_t16_00 ~in_it ~cc iaddr instr
  | 1 when (b 13 10) = 0 ->
     parse_t16_01 ~in_it ~cc iaddr instr
  | 1 when (b 13 10) = 1 ->
     parse_t16_01_1 ~in_it ~cc iaddr instr
  | 1 when (b 13 12) = 1 ->
     parse_t16_load_store_reg ~_in_it:in_it ~cc iaddr instr
  | 1 when (b 13 13) = 0 ->
     parse_t16_load_literal ~_in_it:in_it ~cc iaddr instr
  | 1 when (b 13 13) = 1 ->
     parse_t16_load_store_imm ~_in_it:in_it ~cc iaddr instr
  | 2 when (b 13 12) = 0 ->
     parse_t16_load_store_imm ~hw:true ~_in_it:in_it ~cc iaddr instr
  | 2 when is_imm_relative () ->
     parse_t16_load_store_imm_relative ~_in_it:in_it ~cc iaddr instr
  | _ when (b 15 12) = 11 ->
     parse_t16_misc ~in_it ~cc iaddr instr
  | _ when (b 15 12) = 12 ->
     parse_t16_store_load_multiple ~_in_it:in_it ~cc iaddr instr
  | _ when (b 15 12) = 13 ->
     parse_t16_conditional ~_in_it:in_it ~cc iaddr instr
  | _ when (b 15 11) = 28 ->
     parse_t16_unconditional ~_in_it:in_it ~cc iaddr instr
  | _ -> NotRecognized ("thumb16_opcode", instr)


let parse_thumb_opcode
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instrbytes: int): arm_opcode_t =
  let prefix = instrbytes lsr 11 in
  let in_it = itblock#is_in_it in
  let cc =
    if in_it then
      itblock#consume_condition
    else
      ACCAlways in
  match prefix with
  | 29 | 30 | 31 ->
     if system_info#is_trampoline_wrapper (iaddr#add_int 2) then
       let _ = chlog#add "skip 4-byte thumb-2 instruction" (iaddr#toPretty) in
       NoOperation ACCAlways
     else
       let sndhalfword = ch#read_ui16 in
       let instr32 = (instrbytes lsl 16) + sndhalfword in
       let instr32 = TR.tget_ok (int_to_doubleword instr32) in
       parse_thumb32_opcode ~in_it ~cc ch iaddr instr32
  | _ ->
     let instr16 = TR.tget_ok (int_to_doubleword instrbytes) in
     parse_thumb16_opcode ~in_it ~cc ch iaddr instr16


let disassemble_thumb_instruction
      (ch:pushback_stream_int) (iaddr:doubleword_int) (instrbytes:int) =
  try
    parse_thumb_opcode ch iaddr instrbytes
  with
  | ARM_undefined s ->
     begin
       ch_error_log#add
         "Thumb instruction:UNDEFINED"
         (LBLOCK [iaddr#toPretty; STR ": "; STR s]);
       OpcodeUndefined s
     end
  | ARM_unpredictable s ->
     begin
       ch_error_log#add
         "Thumb instruction:UNPREDICTABLE"
         (LBLOCK [iaddr#toPretty; STR ": "; STR s]);
       OpcodeUnpredictable s
     end
  | BCH_failure p ->
     begin
       ch_error_log#add
         "disassembly - thumb"
         (LBLOCK [
              STR "Error in disassembling thumb: ";
              iaddr#toPretty;
              STR ": ";
              p]);
       raise (BCH_failure p)
     end
  | Invalid_argument s ->
     begin
       ch_error_log#add
         "Thumb instruction:Invalid_argument"
         (LBLOCK [iaddr#toPretty; STR ": "; STR s]);
       raise
         (BCH_failure
            (LBLOCK [iaddr#toPretty; STR ": Invalid_argument: "; STR s]))
     end

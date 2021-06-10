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

(* chlib *)
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHDoubleword
open BCHImmediate
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMDisassemblyUtils
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMPseudocode
open BCHARMTypes

module B = Big_int_Z

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

(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16

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
  
let parse_thumb32_29
      ?(in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let mk_imm5 i3 i2 = (i3 lsl 2) + i2 in
  let mk_imm_shift_reg reg ty imm =
    mk_arm_imm_shifted_register_op reg ty imm in
  let op = b 26 21 in
  match op with
  (* 111010000100<rn><rt><rd><-imm8->   STREX *)
  | 2 when (b 20 20) = 0 ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (b 7 0) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* STREX<c> <Rd>, <Rt>, [<Rn>{, #<imm>}] *)
     StoreRegisterExclusive (cc, rd WR, rt RD, rn RD, mem WR)

  (* 111010000101<rn><rt>1111<-imm8->   LDREX *)
  | 2 when (b 20 20) = 1 && (b 11 8) = 15 ->
     let rt = arm_register_op (get_arm_reg (b 15 12)) in
     let rnreg = get_arm_reg (b 19 16) in
     let rn = arm_register_op rnreg in
     let offset = ARMImmOffset (b 7 0) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDREX<c> <Rt>, [<Rn>{, #<imm>}] *)
     LoadRegisterExclusive (cc, rt WR, rn RD, mem RD)

  (* 1110100010W0<rn>0m0<---rlist--->   STM/STMIA/STMEA *)
  | 4 when (b 15 15) = 0 && (b 13 13) = 0 ->
     let regs = ((b 14 14) lsl 14) + (b 12 0) in
     let reglist = get_reglist_from_int 16 regs in
     let rl = arm_register_list_op reglist in
     let rnreg = get_arm_reg (b 19 16) in
     let mem = mk_arm_mem_multiple_op rnreg (List.length reglist) in
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let wback = (b 21 21) = 1 in
     let rn = if wback then rn RW else rn RD in
     (* STM<c>.W <Rn>{!}, <registers> *)
     StoreMultipleIncrementAfter (wback, cc, rn, rl RD , mem WR, true)

  (* 1110100010111101pm0<---rlist--->   POP.W *)
  | 5 ->
     let reglist = get_reglist_from_int 16 (b 15 0) in
     let rl = arm_register_list_op reglist in
     let sp = arm_register_op (get_arm_reg 13) in
     (* POP<c>.W <registers> *)
     Pop (cc, sp RW, rl WR, true)

  (* 111010001101<rn>111100000000<rm>   TBB *)
  | 6 when (b 20 20) = 1 && (b 15 12) = 15 && (b 11 5) = 0 && (b 4 4) = 0 ->
     let rnreg = get_arm_reg (b 19 16) in
     let rmreg = get_arm_reg (b 3 0) in
     let rn = arm_register_op rnreg in
     let rm = arm_register_op rmreg in
     let offset = ARMIndexOffset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* TBB<c> [<Rn>, <Rm>] *)
     TableBranchByte (cc, rn RD, rm RD, mem RD)

  (* 111010001101<rn>111100000001<rm>   TBH *)
  | 6 when (b 20 20) = 1 && (b 15 12) = 15 && (b 11 5) = 0 && (b 4 4) = 1 ->
     let rnreg = get_arm_reg (b 19 16) in
     let rmreg = get_arm_reg (b 3 0) in
     let rn = arm_register_op rnreg in
     let rm = arm_register_op rmreg in
     let offset = ARMIndexOffset rmreg in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* TBB<c> [<Rn>, <Rm>] *)
     TableBranchHalfword (cc, rn RD, rm RD, mem RD)

  (* 1110100100W0<rn>0m0<---rlist--->   STMDB/STMFD *)
  | 8 when (b 15 15) = 0 && (b 13 13) = 0 ->
     let regs = ((b 14 14) lsl 14) + (b 12 0) in
     let reglist = get_reglist_from_int 16 regs in
     let rl = arm_register_list_op reglist in
     let rnreg = get_arm_reg (b 19 16) in
     let mem = mk_arm_mem_multiple_op rnreg (List.length reglist) in
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let wback = (b 21 21) = 1 in
     let rn = if wback then rn RW else rn RD in
     (* STM<c>.W <Rn>{!}, <registers> *)
     StoreMultipleDecrementBefore (wback, cc, rn, rl RD , mem WR, true)

  (* 11101001001011010M0<---rlist--->   PUSH.W *)
  | 9 ->
     let reglist = get_reglist_from_int 16 (b 15 0) in
     let rl = arm_register_list_op reglist in
     let sp = arm_register_op (get_arm_reg 13) in
     (* PUSH<c>.W <registers> *)
     Push (cc, sp RW, rl RD, true)

  (* 11101010000S<rn>0<i><rd>i2ty<rm>   AND (register) *)
  | 16 when (b 15 15) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     let setflags = (b 20 20) = 1 in
     (* AND{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseAnd (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 11101010001S<rn>0<i><rd>i2ty<rm>   BIC (register) *)
  | 17 when (b 15 15) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     let setflags = (b 20 20) = 1 in
     (* BIC{S}<c>.W <Rd>, <Rn>, <Rm>{, <shifht>} *)
     BitwiseBitClear (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 11101010010S11110<i><rd>i210<rm>   ASR (immediate) *)
  | 18 when (b 19 16) = 15 && (b 15 15) = 0 && (b 5 4) = 2 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     let imm = ((b 14 12) lsl 2) + (b 7 6) in
     let (_, shift_n) = decode_imm_shift 2 imm in
     let imm = mk_arm_immediate_op false 4 (mkNumerical shift_n) in
     let setflags = (b 20 20) = 1 in
     (* ASR{S}<c>.W <Rd>, <Rm>, #<imm> *)
     ArithmeticShiftRight (setflags, cc, rd WR, rm RD, imm, true)

  (* 11101010010S11110000<rd>0000<rm>   MOV (register) *)
  | 18 when (b 19 16) = 15 && (b 15 15) = 0 && (b 7 4) = 0 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     let setflags = (b 20 20) = 1 in
     (* MOV{S}<c>.W <Rd>, <Rm> *)
     Move (setflags, cc, rd WR, rm RD, true)

  (* 11101010010S11110<i><rd>i200<rm>   LSL (immediate) *)
  | 18 when (b 19 16) = 15 && (b 15 15) = 0 && (b 5 4) = 0 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     let imm = ((b 14 12) lsl 2) + (b 7 6) in
     let (_, shift_n) = decode_imm_shift 1 imm in
     let imm = mk_arm_immediate_op false 4 (mkNumerical shift_n) in
     let setflags = (b 20 20) = 1 in
     (* LSL{S}<c>.W <Rd>, <Rm>, #<imm> *)
     LogicalShiftLeft (setflags, cc, rd WR, rm RD, imm, true)

  (* 11101010010S11110<i><rd>i201<rm>   LSR (immediate) *)
  | 18 when (b 19 16) = 15 && (b 15 15) = 0 && (b 5 4) = 1 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     let imm = ((b 14 12) lsl 2) + (b 7 6) in
     let (_, shift_n) = decode_imm_shift 1 imm in
     let imm = mk_arm_immediate_op false 4 (mkNumerical shift_n) in
     let setflags = (b 20 20) = 1 in
     (* LSR{S}<c>.W <Rd>, <Rm>, #<imm> *)
     LogicalShiftRight (setflags, cc, rd WR, rm RD, imm, true)

  (* 11101010010S<rn>0<i><rd>i2ty<rm>   ORR (register) *)
  | 18 when (b 15 15) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     let setflags = (b 20 20) = 1 in
     (* ORR{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseOr (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 11101010100S<rn>0<i><rd>i2ty<rm>   EOR (register) *)
  | 20 when (b 15 15) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     let setflags = (b 20 20) = 1 in
     (* EOR{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     BitwiseExclusiveOr (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 11101011000S<rn>0<i><rd>i2ty<rm>   ADD (register) *)
  | 24 when (b 15 15) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     let setflags = (b 20 20) = 1 in
     Add (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 11101011010S<rn>0<i><rd>i2ty<rm>   ADC (register) *)
  | 26 when (b 15 15) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     let setflags = (b 20 20) = 1 in
     (* ADC{S}<c>.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     AddCarry (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 11101011101S<rn>0<i><rd>i2ty<rm>   SUB (register) *)
  | 29 when (b 15 15) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     let setflags = (b 20 20) = 1 in
     (* SUB{S}.W <Rd>, <Rn>, <Rm>{, <shift>} *)
     Subtract (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 11101011110S<rn>0<i><rd>i2ty<rm>   RSB (register) *)
  | 30 when (b 15 15) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = mk_imm_shift_reg rmreg (b 5 4) (mk_imm5 (b 14 12) (b 7 6)) in
     let setflags = (b 20 20) = 1 in
     (* RSB{S}<c> <Rd>, <Rn>, <Rm>{, <shift>} *)
     ReverseSubtract (setflags, cc, rd WR, rn RD, rm RD, false)

  | _ ->
     NotRecognized ("parse_thumb32_29:" ^ (string_of_int op), instr)

let parse_t32_30_0
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let i = b 26 26 in
  let rd = arm_register_op (get_arm_reg (b 11 8)) in
  let setflags = (b 20 20) = 1 in
  let imm3 = b 14 12 in
  let imm8 = b 7 0 in
  let imm12 = (i lsl 11) + (imm3 lsl 8) + imm8 in
  let (imm32, _) = thumb_expand_imm_c imm12 0 in
  let imm32 = make_immediate false 4 (B.big_int_of_int imm32) in
  let const = arm_immediate_op imm32 in
                            
  match (b 25 21) with

  (* 11110i00000S<rn>0<i><rd><-imm8->   AND (immediate) *)
  | 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in     
     (* AND{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseAnd (setflags, cc, rd WR, rn RD, const, false)

  (* 11110i00001S<rn>0<i><rd><-imm8->   BIC (immediate) *)
  | 1 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* BIC{S} <Rd>, <Rn>, #<const> *)
     BitwiseBitClear (setflags, cc, rd WR, rn RD, const, false)

  (* 11110i00010S11110<i><rd><-imm8->   MOV.W (immediate) *)
  | 2 when (b 19 16) = 15 ->
     (* MOV{S}<c>.W <Rd>, #<const> *)
     Move (setflags, cc, rd WR, const, true)

  (* 11110i00010S<rn>0<i><rd><-imm8->   ORR (immediate) *)
  | 2 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* ORR{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseOr (setflags, cc, rd WR, rn RD, const, false)

  (* 11110i00011S11110<i><rd><-imm8->   MVN (immediate) *)
  | 3 when (b 19 16) = 15 ->
     (* MVN{S}<c> <Rd>, #<const> *)
     BitwiseNot (setflags, cc, rd WR, const)

  (* 11110i00011S<rn>0<i><rd><-imm8->   ORN (immediate) *)
  | 3 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* ORN{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseOrNot (setflags, cc, rd WR, rn RD, const)

  (* 11110i00100S<rn>0<i><rd><-imm8->   EOR (immediate) *)
  | 4 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* EOR{S}<c> <Rd>, <Rn>, #<const> *)
     BitwiseExclusiveOr (setflags, cc, rd WR, rn RD, const, false)

  (* 11110i01000S<rn>0<i><rd><-imm8->   ADD.W (immediate) *)
  | 8 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* ADD{S}<c>.W <Rd>, <Rn>, #<const> *)
     Add (setflags, cc, rd WR, rn RD, const, true)

  (* 11110i01010S<rn>0<i><rd><-imm8->   ADC (immediate) *)
  | 10 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* ADC{S}<c> <Rd>, <Rn>, #<const> *)
     AddCarry (setflags, cc, rd WR, rn RD, const, true)

  (* 11110i01011S<rn>0<i><rd><-imm8->   SBC (immediate) *)
  | 11 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     (* SBC{S}<c> <Rd>, <Rn>, #<const> *)
     SubtractCarry (setflags, cc, rd WR, rn RD, const)

  (* 11110i011011<rn>0<i>1111<-imm8->   CMP (immediate) *)
  | 13 when setflags && (b 11 8) = 15 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let imm = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm = thumb_expand_imm imm 0 in
     let imm = make_immediate false 4 (B.big_int_of_int imm) in
     let imm = arm_immediate_op imm in
     (* CMP<c>.W <Rn>, #<const> *)
     Compare (cc, rn RD, imm, true)

  (* 11110i01101S<rn>0<i><rd><-imm8->   SUB (immediate) *)
  | 13 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let imm = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm = thumb_expand_imm imm 0 in
     let imm = make_immediate false 4 (B.big_int_of_int imm) in
     let imm = arm_immediate_op imm in
     (* SUB{S}<c>.W <Rd>, <Rn>, #<const> *)
     Subtract (setflags, cc, rd WR, rn RD, imm, false)

  (* 11110i01110S<rn>0<i><rd><-imm8->   RSB (immediate) *)
  | 14 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let imm = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm = thumb_expand_imm imm 0 in
     let imm = make_immediate false 4 (B.big_int_of_int imm) in
     let imm = arm_immediate_op imm in
     (* RSB{S}<c>.W <Rd>, <Rn>, #<const> *)
     ReverseSubtract (setflags, cc, rd WR, rn RD, imm, true)

  (* 11110i100000<rn>0<i><rd><-imm8->   ADD (immediate) *)
  | 16 when not setflags ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let imm32 = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm32 = make_immediate false 4 (B.big_int_of_int imm32) in
     let imm12 = arm_immediate_op imm32 in
     (* ADDW<c> <Rd>, <Rn>, #<imm12> *)
     Add (false, cc, rd WR, rn RD, imm12, false)

  (* 11110i100100<ii>0<i><rd><-imm8->   MOVW (immediate) *)
  | 18 when not setflags ->
     let imm4 = b 19 16 in
     let imm16 = (imm4 lsl 12) + (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm16 = make_immediate false 4 (B.big_int_of_int imm16) in
     let imm16 = arm_immediate_op imm16 in
     MoveWide (cc, rd WR, imm16)

  (* 11110i10101011010<i><rd><-imm8->   SUB (SP minus immediate) *)
  | 21 when not setflags && (b 19 16) = 13  ->
     let imm32 = (i lsl 11) + (imm3 lsl 8) + imm8 in
     let sp = arm_register_op (get_arm_reg 13) in
     let imm32 = make_immediate false 4 (B.big_int_of_int imm32) in
     let imm12 = arm_immediate_op imm32 in
     (* SUBW<c> <Rd>, SP #<imm12> *)
     Subtract (false, cc, rd WR, sp RD, imm12, true)

  (* 11110i101100<ii>0<i><rd><-imm8->   MOVT *)
  | 22 when not setflags ->
     let imm4 = b 19 16 in
     let imm16 = (imm4 lsl 12) + (i lsl 11) + (imm3 lsl 8) + imm8 in
     let imm16 = make_immediate false 4 (B.big_int_of_int imm16) in
     let imm16 = arm_immediate_op imm16 in
     (* MOVT<c> <Rd>, #<imm16> *)
     MoveTop (cc, rd WR, imm16)

  (* 111100111100<rn>0<i><rd>i20<wm1>   UBFX *)
  | 30 when i = 0 ->
     let lsb = (imm3 lsl 2) + (b 7 6) in
     let widthm1 = b 4 0 in
     let rn = mk_arm_reg_bit_sequence_op (get_arm_reg (b 19 16)) lsb widthm1 in
     (* UBFX<c> <Rd>, <Rn>, #<lsb>, #<width> *)
     UnsignedBitFieldExtract (cc, rd WR, rn RD)
     
  | tag ->
     NotRecognized ("t32_30_0:" ^ (string_of_int tag), instr)

let parse_t32_branch
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (ch: pushback_stream_int)
      (base: doubleword_int)
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

  (* 1111001110111111100011110101<op>   DMB *)
  | (0, 0) when
         (b 13 13) = 0
         && (b 11 8) = 15
         && (b 7 4) = 5
         && (b 19 16) = 15
         && (b 26 23) = 7
         && (b 22 20) = 3 ->
     DataMemoryBarrier (cc, arm_dmb_option_from_int_op (b 3 0))

  (* 11110S<cc><imm6>10J0J<--imm11-->   B *)
  | (0, 0) ->
     let s = b 26 26 in
     let imm6 = b 21 16 in
     let j1 = b 13 13 in
     let j2 = b 11 11 in
     let imm11 = b 10 0 in
     let imm32 =
       (s lsl 20) + (j2 lsl 19) + (j1 lsl 18) + (imm6 lsl 12) + (imm11 lsl 1) in
     let imm32 = sign_extend 32 21 imm32 in
     let tgt = iaddr#add_int (imm32 + 2) in
     let tgtop = arm_absolute_op tgt RD in
     let cond = get_opcode_cc (b 25 22) in
     (* B<c>.W <label> *)
     Branch (cond, tgtop, true)

  (* 11110S<--imm10->10J1J<--imm11-->   B *)
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
       + (4 * (b 10 1)) in
     let imm32 = sign_extend 32 25 imm32 in
     let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
     let tgt = iaddr#add_int (imm32 + 2) in
     let tgtop = arm_absolute_op tgt RD in
     (* B<c>.W <label> *)
     Branch (cc, tgtop, true)

  (* 11110S<-imm10H->11J0J<-imm10L->H   BLX (immediate) *)
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
     let tgt = iaddr#add_int (imm32 + 2) in
     let tgtop = arm_absolute_op tgt RD in
     (* BLX<c> <label> *)
     BranchLinkExchange (cc, tgtop)
     
  (* 11110S<--imm10->11J1J<--imm11-->   BL  (immediate) *)
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
     let tgt = iaddr#add_int (imm32 + 2) in
     let tgtop = arm_absolute_op tgt RD in
     (* BL<c> <label> *)
     BranchLink (cc, tgtop)

  | (k, l) ->
     NotRecognized ("t32_branch: ("
                    ^ (string_of_int k)
                    ^ ", "
                    ^ (string_of_int l)
                    ^ ")", instr)
  

let parse_thumb32_30
      ?(in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  match b 15 15 with
  | 0 -> parse_t32_30_0 ~in_it ~cc ch base iaddr instr
  | 1 -> parse_t32_branch ~in_it ~cc ch base iaddr instr
  | _ ->
     NotRecognized ("parse_thumb32_30", instr)
    
let parse_thumb32_31
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  let rnreg = get_arm_reg (b 19 16) in
  let rn = arm_register_op rnreg in
  let rt = arm_register_op (get_arm_reg (b 15 12)) in
  let rd = arm_register_op (get_arm_reg (b 11 8)) in
  let rm = arm_register_op (get_arm_reg (b 3 0)) in
  let offset = ARMImmOffset (b 11 0) in
  let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
  match (b 26 20) with
  (* 111110000000<rn><rt>000000i2<rm>   STRB (register) *)
  | 0 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = ARMShiftedIndexOffset (get_arm_reg (b 3 0), reg_srt) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* STRB<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     StoreRegisterByte (cc, rt RD, rn RD, mem WR, true)

  (* 111110000000<rn><rt>1puw<-imm8->   STRB (immediate) *)
  | 0 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* STRB<c> <Rt>, [<Rn>, #-<imm8>]
        STRB<c> <Rt>, [<Rn>], #+/-<imm8>
        STRB<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     StoreRegisterByte (cc, rt RD, rn RD, mem WR, true)

  (* 111110000001<rn><rt>000000i2<rm>   LDRB (register) *)
  | 1 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = ARMShiftedIndexOffset (get_arm_reg (b 3 0), reg_srt) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDRB<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegisterByte (cc, rt WR, rn RD, mem RD, true)

  (* 111110000001<rn><rt>1puw<-imm8->   LDRB (immediate) *)
  | 1 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* LDRB<c>.W <Rt>, [<Rn>{, #+/-<imm8>}]          Offset: (index,wback) = (T,F)
      * LDRB<c>.W <Rt>, [<Rn>, #+/-<imm8>]!           Pre-x : (index,wback) = (T,T)
      * LDRB<c>.W <Rt>, [<Rn>], #+/-<imm8>            Post-x: (index,wback) = (F,T)  *)
     LoadRegisterByte (cc, rt WR, rn RD, mem RD, true)

  (* 111110000010<rn><rt>00000i2<rm>    STRH (register)*)
  | 2 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = ARMShiftedIndexOffset (get_arm_reg (b 3 0), reg_srt) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* STRH<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     StoreRegisterHalfword (cc, rt RD, rn RD, rm RD,  mem WR, true)

  (* 111110000010<rn><rt>1puw<-imm8->   STRH (immediate) *)
  | 2 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* STRH<c> <Rt>, [<Rn>, #-<imm8>]
        STRH<c> <Rt>, [<Rn>], #+/-<imm8>
        STRH<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     StoreRegisterHalfword (cc, rt RD, rn RD, rm RD, mem WR, true)

  (* 111110000011<rn><rt>000000i2<rm>   LDRH (register) *)
  | 3 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = ARMShiftedIndexOffset (get_arm_reg (b 3 0), reg_srt) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDRH<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegisterHalfword (cc, rt WR, rn RD, rm RD, mem RD, true)

  (* 111110000011<rn><rt>1puw<-imm8->   LDRH (immediate) *)
  | 3 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let imm = arm_immediate_op (immediate_from_int (b 7 0)) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* LDRH<c>.W <Rt>, [<Rn>{, #+/-<imm8>}]          Offset: (index,wback) = (T,F)
      * LDRH<c>.W <Rt>, [<Rn>, #+/-<imm8>]!           Pre-x : (index,wback) = (T,T)
      * LDRH<c>.W <Rt>, [<Rn>], #+/-<imm8>            Post-x: (index,wback) = (F,T)  *)
     LoadRegisterHalfword (cc, rt WR, rn RD, imm, mem RD, true)

  (* 1111100001001101<rt>110100000100   PUSH.W *)
  | 4 when (b 19 16) = 13 && (b 11 11) = 1 && (b 10 8) = 3 && (b 7 0) = 4 ->
     let sp = arm_register_op (get_arm_reg 13) RW in
     let rl = arm_register_list_op [ (get_arm_reg (b 15 12)) ] RD in
     Push (cc, sp, rl, true)

  (* 111110000100<rn><rt>000000i2<rm>   STR (register) *)
  | 4 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = (SRType_LSL, b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let offset = ARMShiftedIndexOffset (get_arm_reg (b 3 0), reg_srt) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* STR<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     StoreRegister (cc, rt RD, rn RD, mem WR, true)

  (* 111110000100<rn><rt>1puw<-imm8->   STR (immediate) *)
  | 4 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* STR<c> <Rt>, [<Rn>, #-<imm8>] 
        STR<c> <Rt>, [<Rn>], #+/-<imm8>
        STR<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     StoreRegister (cc, rt RD, rn RD, mem WR, false)

  (* 1111100001011101<rt>101100000100   POP *)
  | 5 when (b 19 16) = 13 && (b 11 11) = 1 && (b 10 8) = 3 && (b 7 0) = 4 ->
     let sp = arm_register_op (get_arm_reg 13) RW in
     let rl = arm_register_list_op [ (get_arm_reg (b 15 12))] WR in
     Pop (cc, sp, rl, true)

  (* 111110000101<rn><rt>000000i2<rm>   LDR (register) *)
  | 5 ->
     let (shift_t, shift_n) = decode_imm_shift 0 (b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let rmreg = get_arm_reg (b 3 0) in
     let offset = ARMShiftedIndexOffset (rmreg, reg_srt) in
     let memi = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDR<c>.W <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegister (cc, rt WR, rn RD, memi RD, true)

  (* 111110001000<rn><rt><--imm12--->   STRB (immediate) *)
  | 8 ->
  (* STRB<c>.W <Rt>, [<Rn, #<imm12>] *)
     StoreRegisterByte (cc, rt RD, rn RD, mem WR, true)

  (* 111110001001<rn><rt><--imm12--->   LDRB (immediate) *)
  | 9 ->
     (* LDRB<c>.W <Rt>, [<Rn>, #<imm12>] *)
     LoadRegisterByte (cc, rt WR, rn RD, mem RD, true)

  (* 111110001010<rn><rt><--imm12--->   STRH (immediate) *)
  | 10 ->
     (* STRH<c>.W <Rt>, [<Rn>, #<imm12>] *)
     StoreRegisterHalfword (cc, rt RD, rn RD, rm RD, mem WR, true)

  (* 111110001011<rn><rt><--imm12--->   LDRH (immediate) *)
  | 11 ->
     (* LDRH<c>.W <Rt>, [<Rn>{, #<imm12>} *)
     LoadRegisterHalfword (cc, rt WR, rn RD, rm RD, mem RD, true)

  (* 111110001100<rn><rt><--imm12--->   STR (immediate) *)
  | 12 ->
     (* STR<c>.W <Rt>, [<Rn>, #<imm12>] *)
     StoreRegister (cc, rt RD, rn RD, mem WR, true)
    
  (* 111110001101<rn><rt><--imm12--->   LDR (immediate) *)
  | 13 ->
    (* LDR<c>.W <Rt>, [<Rn>{, #<imm12>}] *)
     LoadRegister (cc, rt WR, rn RD, mem RD, true)

  (* 111110010001<rn><rt>000000i2<rm>   LDRSB (register) *)
  | 17 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = decode_imm_shift 0 (b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = arm_register_op rmreg in
     let offset = ARMShiftedIndexOffset (rmreg, reg_srt) in
     let memi = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDRSB<c>.W, <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegisterSignedByte (cc, rt WR, rn RD, rm RD, memi RD, true)

  (* 111110010001<rn><rt>1puw<-imm8->   LDRSB (immediate) *)
  | 17 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let imm = arm_immediate_op (immediate_from_int (b 7 0)) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* LDRSB<c> <Rt>, [<Rn>, #-<imm8>]
        LDRSB<c> <Rt>, [<Rn>], #+/-<imm8>
        LDRSB<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     LoadRegisterSignedByte (cc, rt WR, rn RD, imm, mem RD, false)

  (* 111110010011<rn><rt>000000i2<rm>   LDRSH (register) *)
  | 19 when (b 11 6) = 0 ->
     let (shift_t, shift_n) = decode_imm_shift 0 (b 5 4) in
     let reg_srt = ARMImmSRT (shift_t, shift_n) in
     let rmreg = get_arm_reg (b 3 0) in
     let rm = arm_register_op rmreg in
     let offset = ARMShiftedIndexOffset (rmreg, reg_srt) in
     let memi = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDRSH<c>.W, <Rt>, [<Rn>, <Rm>{, LSL #<imm2>}] *)
     LoadRegisterSignedHalfword (cc, rt WR, rn RD, rm RD, memi RD, true)

  (* 111110010011<rn><rt>1puw<-imm8->   LDRSH (immediate) *)
  | 19 when (b 11 11) = 1 ->
     let offset = ARMImmOffset (b 7 0) in
     let isindex = (b 10 10) = 1 in
     let isadd = (b 9 9) = 1 in
     let iswback = (b 8 8) = 1 in
     let imm = arm_immediate_op (immediate_from_int (b 7 0)) in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd ~isindex ~iswback in
     (* LDRSH<c> <Rt>, [<Rn>, #-<imm8>]
        LDRSH<c> <Rt>, [<Rn>], #+/-<imm8>
        LDRSH<c> <Rt>, [<Rn>, #+/-<imm8>]! *)
     LoadRegisterSignedHalfword (cc, rt WR, rn RD, imm, mem RD, false)

  (* 111110011001<rn><rt><--imm12--->   LDRSB (immediate) *)
  | 25 ->
     let imm12 = b 11 0 in
     let imm = arm_immediate_op (immediate_from_int imm12) in
     let offset = ARMImmOffset imm12 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDRSB<c> <Rt>, [<Rn>, #<imm12>] *)
     LoadRegisterSignedByte (cc, rt WR, rn RD, imm, mem RD, false)

  (* 111110011011<rn><rt><--imm12--->   LDRSH (immediate) *)
  | 27 ->
     let imm12 = b 11 0 in
     let imm = arm_immediate_op (immediate_from_int imm12) in
     let offset = ARMImmOffset imm12 in
     let mem = mk_arm_offset_address_op rnreg offset ~isadd:true ~isindex:true ~iswback:false in
     (* LDRSH<c> <Rt>, [<Rn>, #<imm12>] *)
     LoadRegisterSignedHalfword (cc, rt WR, rn RD, imm, mem RD, false)

  (* 11111010000S<rn>1111<rd>0000<rm>   LSL (register) *)
  | 32 | 33 when (b 15 12) = 15 && (b 7 4) = 0->
     let setflags = (b 20 20) = 1 in
     (* LSL{S}<c>.W <Rd>, <Rn>, <Rm> *)
     LogicalShiftLeft (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 11111010001S<rn>1111<rd>0000<rm>   LSR (register) *)
  | 34 | 35 when (b 15 12) = 15 && (b 7 4) = 0 ->
     let setflags = (b 20 20) = 1 in
     (* LSR{S}<c>.W <Rd>, <Rn>, <Rm> *)
     LogicalShiftRight (setflags, cc, rd WR, rn RD, rm RD, true)

  (* 111110101011<rm>1111<rd>1000<rm>   CLZ *)
  | 43 when (b 15 12) = 15 && (b 7 4) = 8 ->
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* CLZ<c> <Rd>, <Rm> *)
     CountLeadingZeros (cc, rd WR, rm RD)

  (* 111110110000<rn>1111<rd>0000<rm>   MUL *)
  | 48 when (b 15 12) = 15 && (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rd = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* MUL<c> <Rd>, <Rn>, <Rm> *)
     Multiply (false, cc, rd WR, rn RD, rm RD)

  (* 111110111000<rn><lo><hi>0000<rm>   SMULL *)
  | 56 when (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rdlo = arm_register_op (get_arm_reg (b 15 12)) in
     let rdhi = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* SMULL<c> <RdLo>, <RdHi>, <Rn>, <Rm> *)
     SignedMultiplyLong (false, cc, rdlo WR, rdhi WR, rn RD, rm RD)

  (* 111110111100<rn><rd><rd>0000<rm>   SMLAL *)
  | 60 when (b 7 4) = 0 ->
     let rn = arm_register_op (get_arm_reg (b 19 16)) in
     let rdlo = arm_register_op (get_arm_reg (b 15 12)) in
     let rdhi = arm_register_op (get_arm_reg (b 11 8)) in
     let rm = arm_register_op (get_arm_reg (b 3 0)) in
     (* SMLAL<c> <RdLo>, <RdHi>, <Rn>, <Rm> *)
     SignedMultiplyAccumulateLong (false, cc, rdlo WR, rdhi WR, rn RD, rm RD)

  | s ->
     NotRecognized ("parse_thumb32_31:" ^ (string_of_int s), instr)
  
  
let parse_thumb32_opcode
      ?(in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): arm_opcode_t =
  let b = instr#get_segval in
  match (b 31 27) with
  | 29 -> parse_thumb32_29 ~in_it ~cc ch base iaddr instr
  | 30 -> parse_thumb32_30 ~in_it ~cc ch base iaddr instr
  | 31 -> parse_thumb32_31 ~in_it ~cc ch base iaddr instr
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
    let i = make_immediate false 4 (B.big_int_of_int (b 8 6)) in
    arm_immediate_op i in
  let imm5 ty =
    let (_, shift_n) = decode_imm_shift ty (b 10 6) in
    let i = make_immediate false 4 (B.big_int_of_int shift_n) in
    arm_immediate_op i in       
  let imm8 () =
    let i = make_immediate false 4 (B.big_int_of_int (b 7 0)) in
    arm_immediate_op i in
  
  match (b 13 11) with

  (* 0000000000<r><r>  MOV (register) *)
  | 0 when (b 10 6) = 0 ->
     let _ = if in_it then unpredictable iaddr "MOV (register) in IT block" in
     (* MOVS <Rd>, <Rm> *)
     Move (true, cc, r 3 WR, r 2 RD, false)

  (* 00000<im5><r><r>  LSL (immediate) *)
  | 0 ->
  (* LSLS <Rd>, <Rm>, #<imm> (outside IT block) *)
  (* LSL<c> <Rd>, <Rm>, #<imm> (inside IT block) *)
     LogicalShiftLeft (not in_it, cc, r 3 WR, r 2 RD, imm5 0, false)

  (* 00001<im5><r><r>  LSR (immediate) *)
  | 1 ->
     (* LSRS <Rd>, <Rm>, #<imm> (outside IT block) *)
     (* LSR<c> <Rd>, <Rm>, #<imm> (inside IT block) *)
     LogicalShiftRight (not in_it, cc, r 3 WR, r 2 RD, imm5 1, false)
    
  (* 00010<im5><r><r>  ASR (immediate) *)
  | 2 ->
     (* ASRS <Rd>, <Rm>, #<imm> (outside IT block) *)
     (* ASR<c> <Rd>, <Rm>, #<imm> (inside IT block) *)
     ArithmeticShiftRight (not in_it, cc, r 3 WR, r 2 RD, imm5 2, false)

  (* 0001100<r><r><r>  ADD (register) *)
  | 3 when (b 10 9) = 0 ->
     (* ADDS <Rd>, <Rn>, <Rm> (outside IT block) *)
     (* ADD<c> <Rd>, <Rn>, <Rm> (inside IT block) *)
     Add (not in_it, cc, r 3 WR, r 2 RD, r 1 RD, false)

  (* 0001101<r><r><r>  SUB (register) *)
  | 3 when (b 10 9) = 1 ->
     (* SUBS <Rd>, <Rn>, <Rm> (outside IT block) *)
     (* SUB<c> <Rd>, <Rn>, <Rm> (inside IT block) *)
     Subtract (not in_it, cc, r 3 WR, r 2 RD, r 1 RD, false)

  (* 0001110<i><r><r>  ADD (immediate) *)
  | 3 when (b 10 9) = 2 ->
     (* ADDS <Rd>, <Rn>, #<imm3> (outside IT block) *)
     (* ADD<c> <Rd>, <Rn>, #<imm3> (inside IT block) *)
     Add (not in_it, cc, r 3 WR, r 2 RD, imm3 (), false)

  (* 0001111<i><r><r>  SUB (immediate) *)
  | 3 when (b 10 9) = 3 ->
     (* SUBS <Rd>, <Rn>, #<imm3> (outside IT block) *)
     (* SUB<c> <Rd>, <Rn>, #<imm3> (inside IT block) *)
     Subtract (not in_it, cc, r 3 WR, r 2 RD, imm3 (), false)
    
  (* 00100<r><-imm8->  MOV (immediate) *)
  | 4 ->
     (* MOVS <Rd>, #<imm8> (outside IT block) *)
     (* MOV<c> <Rd>, #<imm8> (inside IT block) *)
     Move (not in_it, cc, r 0 WR, imm8 (), false)

  (* 00101<r><-imm8->  CMP (immediate) *)
  | 5 ->
     (* CMP<c> <Rn>, #<imm8> *)
     Compare (cc, r 0 WR, imm8 (), false)

  (* 00110<r><-imm8->  ADD (immediate) *)
  | 6 ->
     (* ADDS <Rdn>, #<imm8>  (outside IT block) *)
     (* ADD<c> <Rdn>, #<imm8>  (inside IT block) *)
     Add (not in_it, cc, r 0 WR, r 0 RD, imm8 (), false)

  (*00111<r><-imm8->  SUB (immediate) *)
  | 7 ->
     (* SUBS <Rdn>, #<imm8> (outside IT block) *)
     (* SUB<c> <Rdn>, #<imm8> (inside IT block) *)
     Subtract (not in_it, cc, r 0 WR, r 0 RD, imm8 (), false)

  | _ -> NotRecognized ("t16_00", instr)
  
let parse_t16_01
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let r (i: int) (m: arm_operand_mode_t) =
    match i with
    | 0 -> arm_register_op (get_arm_reg (b 5 3)) m
    | 1 -> arm_register_op (get_arm_reg (b 2 0)) m
    | _ -> raise (BCH_failure (LBLOCK [STR "reg: "; INT i])) in
  match (b 9 6) with

(* 0100000000<r><r>  AND (register) *)
  | 0 ->
     (* ANDS <Rdn>, <Rm> (outside IT block) *)
     (* AND<c> <Rdn>, <Rm> (inside IT block) *)
     BitwiseAnd (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000001<r><r>  EOR (register) *)
  | 1 ->
     (* EORS <Rdn>, <Rm> (outside IT block) *)
     (* EOR<c>, <Rdn>, <Rm> (inside IT block) *)
     BitwiseExclusiveOr (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)
    
  (* 0100000010<r><r>  LSL (register) *)
  | 2 ->
     (* LSLS <Rdn>, <Rm> (outside IT block) *)
     (* LSL<c> <Rdn>, <Rm> (inside IT block) *)
     LogicalShiftLeft (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000011<r><r>  LSR (register) *)
  | 3 ->
     (* LSRS <Rdn>, <Rm> (outside IT block) *)
     (* LSR<c> <Rdn>, <Rm> (inside IT block) *)
     LogicalShiftRight (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000100<r><r>  ASR (register) *)
  | 4 ->
     (* ASRS <Rdn>, <Rm> (outside IT block) *)
     (* ASR<c> <Rdn>, <Rm> (inside IT block) *)
     ArithmeticShiftRight (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000101<r><r>  ADC (register) *)
  | 5 ->
     (* ADCS <Rdn>, <Rm> (outside IT block) *)
     (* ADC<c> <Rdn>, <Rm> (inside IT block) *)
     AddCarry (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100000110<r><r>  SBC (register) *)
  | 6 ->
     (* SBCS <Rdn>, <Rm> (outside IT block) *)
     (* SBC<c> <Rdn>, <Rm> (inside IT block) *)
     SubtractCarry (not in_it, cc, r 1 WR, r 1 RD, r 0 RD)

  (* 0100000111<r><r>  ROR (register) *)
  | 7 ->
     (* RORS <Rdn>, <Rm> (outside IT block) *)
     (* ROR<c> <Rdn>, <Rm> (inside IT block) *)
     RotateRight (not in_it, cc, r 1 WR, r 1 RD, r 0 RD)

  (* 0100001000<r><r>  TST (register) *)
  | 8 ->
     (* TST<c> <Rn>, <Rm> *)
     Test (cc, r 1 RD, r 0 RD)

  (* 0100001001<r><r>  RSB (immediate) *)
  | 9 ->
     (* RSBS <Rd>, <Rn>, #0 (inside IT block *)
     (* RSB<c> <Rd>, <Rn>, #0 (outside IT block *)
     let imm0 = arm_immediate_op imm0 in
     ReverseSubtract (not in_it, cc, r 1 WR, r 0 RD, imm0, false)

  (* 0100001010<r><r>  CMP (register) *)
  | 10 ->
  (* CMP<c> <Rn>, <Rm> *)
     Compare (cc, r 1 RD, r 0 RD, false)

  (* 0100001011<r><r>  CMN (register) *)
  | 11 ->
     (* CMN<c> <Rn>, <Rm> *)
     CompareNegative (cc, r 1 RD, r 0 RD)

  (* 0100001100<r><r>  ORR (register) *)
  | 12 ->
     (* ORRS <Rdn>, <Rm> (outside IT block) *)
     (* ORR<c> <Rdn>, <Rm> (inside IT block_ *)
     BitwiseOr (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100001101<r><r>  MUL *)
  | 13 ->
     (* MULS <Rdm>, <Rn>, <Rdm> (outside IT block) *)
     (* MUL<c> <Rdm>, <Rn>, <Rdm> (inside IT block) *)
     Multiply (not in_it, cc, r 1 WR, r 0 RD, r 1 RD)

  (* 0100001110<r><r>  BIC (register) *)
  | 14 ->
     (* BICS <Rdn>, <Rm> (outside IT block) *)
     (* BIC<c> <Rdn>, <Rm> (inside IT block) *)
     BitwiseBitClear (not in_it, cc, r 1 WR, r 1 RD, r 0 RD, false)

  (* 0100001111<r><r>  MVN (register) *)
  | 15 ->
     (* MVNS <Rd>, <Rm> (outside IT block) *)
     (* MVN<c> <Rd>, <Rm> (inside IT block) *)
     BitwiseNot (not in_it, cc, r 1 WR, r 1 RD)
    
  | _ -> NotRecognized ("t16_01", instr)
  
let parse_t16_01_1
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
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
    
  (* 010001001<rm>101  ADD (SP plus register) *)
  | 0 when (b 7 7) = 1 && (b 2 0) = 5 ->
     (* ADD<c> SP, <Rm> *)
     Add (false, cc, r 13 WR, r 13 RD, r 0 RD, false)
                            
  (* 01000100D1101<r>  ADD (SP plus register) *)
  | 0 when (b 6 3) = 13 ->
     let d = rr ((8 * (b 7 7)) + (b 2 0)) in
     (* ADD<c> <Rdm>, SP, <Rdm> *)
     Add (false, cc, d WR, r 13 RD, d RD, false)

  (* 01000100D<rm><r>  ADD (register) *)
  | 0 ->
     let d = rr ((8 * (b 7 7)) + (b 2 0)) in
     (* ADD<c> <Rdn>, <Rm> *)     
     Add (not in_it, cc, d WR, d RD, r 0 RD, false)

  (* 01000101N<rm><r>  CMP (register) *)
  | 1 ->
     let n = rr ((8 * (b 7 7)) + (b 2 0)) in
     (* CMP<c> <Rn>, <Rm> *)
     Compare (cc, n RD, r 0 RD, false)

  (* 01000110D<rm><r>  MOV (register) *)
  | 2 ->
     let d = rr ((8 * (b 7 7)) + (b 2 0)) in
     (* MOV<c> <Rd>, <Rm> *)
     Move (false, cc, d WR, r 0 RD, false)

  (* 010001110<rm>000  BX *)
  | 3 when (b 7 7) = 0 ->
     (* BX<c> <Rm> *)
     BranchExchange (cc, r 0 RD)

  (* 010001111<rm>000  BLX (register) *)
  | 3 when (b 7 7) = 1 ->
     (* BLX<c> <Rm> *)
     BranchLinkExchange (cc, r 0 RD)
    
  | _ -> NotRecognized ("t16_01_1", instr)
     
let parse_t16_load_store_reg
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
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
  let offset = ARMShiftedIndexOffset (rmreg, reg_srt) in
  let mem m =
    mk_arm_offset_address_op
      rnreg offset ~isadd:true ~isindex:true ~iswback:false m in
               
  match (b 11 9) with

  (* 0101000<r><r><r>  STR (register) *)
  | 0 ->
     (* STR<c> <Rt>, [<Rn>, <Rm>] *)
     StoreRegister (cc, rt RD, rn RD, mem WR, false)

  (* 0101001<r><r><r>  STRH (register) *)
  | 1 ->
     (* STRH<c> <Rt>, [<Rn>, <Rm>] *)
     StoreRegisterHalfword (cc, rt RD, rn RD, rm RD, mem WR, false)

  (* 0101010<r><r><r>  STRB (register) *)
  | 2 ->
     (* STRB<c> <Rt>, [<Rn>, <Rm>] *)
     StoreRegisterByte (cc, rt RD, rn RD, mem WR, false)

  (* 0101011<r><r><r>  LDRSB (register) *)
  | 3 ->
     (* LDRSB<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegisterSignedByte (cc, rt WR, rn RD, rm RD, mem RD, false)

  (* 0101100<r><r><r>  LDR (register) *)
  | 4 ->
     (* LDR<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegister (cc, rt WR, rn RD, mem RD, false)

  (* 0101101<r><r><r>  LDRH (register) *)
  | 5 ->
  (* LDRH<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegisterHalfword (cc, rt WR, rn RD, rm RD, mem RD, false)

  (* 0101110<r><r><r>  LDRB (register) *)
  | 6 ->
     (* LDRB<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegisterByte (cc, rt WR, rn RD, mem RD, false)

  (* 0101111<r><r><r>  LDRSH (register) *)
  | 7 ->
     (* LDRSH<c> <Rt>, [<Rn>, <Rm>] *)
     LoadRegisterSignedHalfword (cc, rt WR, rn RD, rm RD, mem RD, false)

  | _ -> NotRecognized ("t16_load_store_reg", instr)

let parse_t16_load_literal
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let rt = arm_register_op (get_arm_reg (b 10 8)) WR in
  let pc = arm_register_op (get_arm_reg 15) RD in
  let imm = 4 * (b 7 0) in
  let offset = iaddr#add_int (2 + imm) in
  let addr = arm_absolute_op offset RD in
  (* LDR<c> <Rt>, <label> *)
  LoadRegister (cc, rt, pc, addr, false)
  

let parse_t16_load_store_imm
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      ?(hw: bool=false)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let reg (i: int): arm_reg_t = get_arm_reg i in
  let regop (r: arm_reg_t) = arm_register_op r in
  let rnreg = reg (b 5 3) in
  let rn = regop rnreg in    
  let rtreg = reg (b 2 0) in
  let rt = regop rtreg in
  let imm = arm_immediate_op (immediate_from_int (2 * (b 10 6))) in
  let offset (m:int) = ARMImmOffset (m * (b 10 6)) in
  let mem (mult: int) m =
    mk_arm_offset_address_op
      rnreg (offset mult) ~isadd:true ~isindex:true ~iswback:false m in

  match (b 12 11) with
  (* 10000<imm><r><r>  STRH (immediate) *)
  | 0 when hw ->
     (* STRH<c> <Rt>, [<Rn>, #<imm>] *)
     StoreRegisterHalfword (cc, rt RD, rn RD, imm, mem 2 WR, false)
    
  (* 01100<imm><r><r>  STR (immediate) *)
  | 0 ->
     (* STR<c> <Rt>, [<Rn>, #<imm>] *)
     StoreRegister (cc, rt RD, rn RD, mem 4 WR, false)

  (* 10001<imm><r><r>  LDRH (immediate) *)
  | 1 when hw ->
     (* LDRH<c> <Rt>, [<Rn>, #<imm>] *)
     LoadRegisterHalfword (cc, rt WR, rn RD, imm, mem 2 RD, false)
    
  (* 01101<imm><r><r>  LDR (immediate) *)
  | 1 ->
     (* LDR<c> <Rt>, [<Rn>, #<imm>] *)
     LoadRegister (cc, rt WR, rn RD, mem 4 RD, false)

  (* 01110<imm><r><r>  STRB (immediate) *)
  | 2 ->
     (* STRB<c> <Rt>, [<Rn>, #<imm5>] *)
     StoreRegisterByte (cc, rt RD, rn RD, mem 1 WR, false)

  (* 01111<imm><r><r>  LDRB (immediate) *)
  | 3 ->
     (* LDRB<c> <Rt>, [<Rn>, #<imm5>] *)
     LoadRegisterByte (cc, rt WR, rn RD, mem 1 RD, false)

  | _ -> NotRecognized ("t16_load_store_imm", instr)


let parse_t16_load_store_imm_relative
      ?(in_it: bool=false)
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
  let imm = make_immediate false 4 (B.big_int_of_int (4 * (b 7 0))) in
  let immop = arm_immediate_op imm in
  let imm7 = make_immediate false 4 (B.big_int_of_int (4 * (b 6 0))) in
  let imm7op = arm_immediate_op imm7 in
  let mem (mult: int) m =
    mk_arm_offset_address_op
      spreg (offset mult) ~isadd:true ~isindex:true ~iswback:false m in

  match (b 13 11) with

  (* 10010<r><-imm8->  STR (immediate) *)    
  | 2 ->
     (* STR<c> <Rt>, [SP, #<imm>] *)
     StoreRegister (cc, rt RD, sp RD, mem 4 WR, false)

  (* 10011<r><-imm8->  LDR (immediate) *)
  | 3 ->
     (* LDR<c> <Rt>, [SP, #<imm>] *)
     LoadRegister (cc, rt WR, sp RD, mem 4 RD, false)

  (* 10100<r><-imm8->  ADR *)
  | 4 ->
     let imm = arm_absolute_op (iaddr#add_int (2 + (4 * (b 7 0)))) in
     (* ADR<c> <Rd>, <label> *)
     Adr (cc, rt WR, imm RD)

  (* 10101<r><-imm8->  ADD (SP plus immediate) *)
  | 5 ->
     (* ADD<c> <Rd>, SP #<imm> *)
     Add (false, cc, rt WR, sp RD, immop, false)

  (* 101100000<imm7->  ADD (SP plus immediate) *)
  | 6 when (b 10 7) = 0 ->
     (* ADD<c> SP, SP, #<imm> *)
     Add (false, cc, sp WR, sp RD, imm7op, false)

  (* 101100001<imm7->  SUB (SP minus immediate) *)
  | 6 when (b 10 7) = 1 ->
     (* SUB<c> SP, SP, #<imm> *)
     Subtract (false, cc, sp WR, sp RD, imm7op, false)

  | _ -> NotRecognized ("t16_load_store_imm_relative", instr)


let parse_t16_push_pop
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let regs s = (b 7 0) + ((b 8 8) lsl s) in
  let rlist s = get_reglist_from_int 16 (regs s) in
  let rl s = arm_register_list_op (rlist s) RD in
  let sp = arm_register_op (get_arm_reg 13) RW in
  match (b 11 9) with

  (* 1011010M<rlist->  PUSH *)
  | 2 ->
     (* PUSH<c> <registers> *)
     Push (cc, sp, rl 14, false)

  (* 1011110p<rlist->  POP *)
  | 6 ->
     (* POP<c> <registers> *)
     Pop (cc, sp, rl 15, false)

  | _ -> NotRecognized ("t16_push_pop", instr)

let parse_t16_compare_branch
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let imm = ((b 9 9) lsl 6) + (2 * (b 7 3)) in
  let tgtaddr = iaddr#add_int (2 + imm) in
  let tgtop = arm_absolute_op tgtaddr RD in
  let rn = arm_register_op (get_arm_reg (b 2 0)) RD in
  match (b 11 11) with

  (* 101100i1<-i5><r>  CBZ *)
  | 0 ->
     (* CBZ <Rn>, <label> *)
     CompareBranchZero (rn, tgtop)

  (* 101110i1<-i5><r>  CBNZ *)
  | 1 ->
     (* CBNZ <Rn>, <label> *)
     CompareBranchNonzero (rn, tgtop)

  | _ -> NotRecognized ("t16_compare_branch", instr)


let parse_t16_misc7
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in  
  match (b 8 8) with

  (* 1011111100000000  NOP *)
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
     IfThen (firstcc, xyz)
       (*
     NotRecognized ("t16_it_"
                    ^ (get_cond_mnemonic_extension firstcc)
                    ^ "_"
                    ^ (string_of_int mask),
                    instr) *)
  | _ ->
     NotRecognized ("t16_misc7", instr)

let parse_t16_bit_extract
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let rd = arm_register_op (get_arm_reg (b 2 0)) in
  let rm = arm_register_op (get_arm_reg (b 5 3)) in
  match (b 7 6) with
  (* 1011001000<r><r>  SXTH *)
  | 0 ->
  (* SXTH<c> <Rd>, <Rm> *)
     SignedExtendHalfword (cc, rd WR, rm RD)

  (* 1011001001<r><r>  SXTB *)
  | 1 ->
     (* SXTB<c> <Rd>, <Rm> *)
     SignedExtendByte (cc, rd WR, rm RD)

  (* 1011001010<r><r>  UXTH *)
  | 2 ->
     (* UXTH<c> <Rd>, <Rm> *)
     UnsignedExtendHalfword (cc, rd WR, rm RD)
    
  (* 1011001011<r><r>  UXTB *)
  | 3 ->
     (* UXTB<c> <Rd>, <Rm> *)
     UnsignedExtendByte (cc, rd WR, rm RD)

  | tag -> NotRecognized ("t16_bit_extract_" ^ (string_of_int tag), instr)
  

let parse_t16_misc
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let opc = b 11 9 in
  match opc with
  | 2 | 6 -> parse_t16_push_pop ~in_it ~cc iaddr instr

  | 7 -> parse_t16_misc7 ~in_it ~cc iaddr instr

  | _ when (b 8 8) = 1 ->
     parse_t16_compare_branch ~in_it ~cc iaddr instr

  | 1 -> parse_t16_bit_extract ~in_it ~cc iaddr instr

  | tag -> NotRecognized ("t16_misc_" ^ (string_of_int tag), instr)

let parse_t16_store_load_multiple
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let rnreg = get_arm_reg (b 10 8) in
  let rn = arm_register_op rnreg in
  let regs = get_reglist_from_int 16 (b 7 0) in
  let rl = arm_register_list_op regs in
  let mmem = mk_arm_mem_multiple_op rnreg (List.length regs) in
  match (b 11 11) with
  (* 11000<r><rlist->  STM/STMIA/STMEA *)
  | 0 ->
     (* STM<c> <Rn>!, <registers> *)
     StoreMultipleIncrementAfter (true, cc, rn RW, rl RD, mmem WR, false)

       (* 11001<r><rlist->  LDM/LDMIA/LDMFD *)
  | 1 ->
     (* LDM<c> <Rn>, <registers> *)
     (* LDM<c> <Rn>!, <registers> *)
     let wback = List.mem rnreg regs in
     let regmode = if wback then RW else RD in
     LoadMultipleIncrementAfter (wback, cc, rn regmode, rl WR, mmem RD)

  | _ ->     
     NotRecognized ("t16_store_load_multiple", instr)

let parse_t16_conditional
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  match (b 11 8) with
  (* 11011110<-imm8->  UDF *)
  | 14 ->
     let imm8 = arm_immediate_op (immediate_from_int (b 7 0)) in
     (* UDF<c> #<imm8> *)
     PermanentlyUndefined (cc, imm8)
     
  (* 11011111<-imm8->  SVC *)
  | 15 ->
     let imm8 = arm_immediate_op (immediate_from_int (b 7 0)) in
     (* SVC<c> #<imm8> *)
     SupervisorCall (cc, imm8)

  (* 1101<cc><-imm8->  B *)
  | cond ->
     let c = get_opcode_cc cond in
     let imm32 = sign_extend 32 9 (2 * (b 7 0)) in
     let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
     let tgt = iaddr#add_int (imm32 + 2) in
     let tgtop = arm_absolute_op tgt RD in
     Branch (c, tgtop, false)


let parse_t16_unconditional
      ?(in_it: bool=false)
      ?(cc: arm_opcode_cc_t=ACCAlways)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_segval in
  let imm32 = sign_extend 32 12 (2 * (b 10 0)) in
  let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
  let tgt = iaddr#add_int (imm32 + 2) in
  let tgtop = arm_absolute_op tgt RD in
  Branch (ACCAlways, tgtop, false)

let parse_thumb16_opcode
      ?(in_it: bool = false)
      ?(cc: arm_opcode_cc_t = ACCAlways)
      (ch: pushback_stream_int)
      (base: doubleword_int)
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
     parse_t16_load_store_reg ~in_it ~cc iaddr instr
  | 1 when (b 13 13) = 0 ->
     parse_t16_load_literal ~in_it ~cc iaddr instr
  | 1 when (b 13 13) = 1 ->
     parse_t16_load_store_imm ~in_it ~cc iaddr instr
  | 2 when (b 13 12) = 0 ->
     parse_t16_load_store_imm ~hw:true ~in_it ~cc iaddr instr
  | 2 when is_imm_relative () ->
     parse_t16_load_store_imm_relative ~in_it ~cc iaddr instr
  | _ when (b 15 12) = 11 ->
     parse_t16_misc ~in_it ~cc iaddr instr
  | _ when (b 15 12) = 12 ->
     parse_t16_store_load_multiple ~in_it ~cc iaddr instr
  | _ when (b 15 12) = 13 ->
     parse_t16_conditional ~in_it ~cc iaddr instr
  | _ when (b 15 11) = 28 ->
     parse_t16_unconditional ~in_it ~cc iaddr instr
  | _ -> NotRecognized ("thumb16_opcode", instr)

let parse_thumb_opcode
      (ch: pushback_stream_int)
      (base: doubleword_int)
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
     let sndhalfword = ch#read_ui16 in
     let instr32 = (instrbytes lsl 16) + sndhalfword in
     let instr32 = int_to_doubleword instr32 in
     parse_thumb32_opcode ~in_it ~cc ch base iaddr instr32
  | _ ->
     let instr16 = int_to_doubleword instrbytes in
     parse_thumb16_opcode ~in_it ~cc ch base iaddr instr16

let disassemble_thumb_instruction
      (ch:pushback_stream_int) (base:doubleword_int) (instrbytes:int) =
  let iaddr = base#add_int ch#pos in
  try
    parse_thumb_opcode ch base iaddr instrbytes
  with
  | BCH_failure p ->
     begin
       ch_error_log#add
         "disassembly - thumb"
         (LBLOCK [STR "Error in disassembling thumb: ";
                  iaddr#toPretty]);
       raise (BCH_failure p)
     end

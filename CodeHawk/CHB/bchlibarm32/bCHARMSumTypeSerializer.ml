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
open CHLanguage
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHSumTypeSerializer

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


let cps_effect_mfts: cps_effect_t mfts_int =
  mk_mfts
    "cps_effect_t"
    [(Interrupt_Enable, "IE");
     (Interrupt_Disable, "ID");
     (Interrupt_NoChange, "NC")
    ]


let interrupt_flags_mfts: interrupt_flags_t mfts_int =
  mk_mfts
    "interrupt_flags_t"
    [(IFlag_A, "A");
     (IFlag_I, "I");
     (IFlag_F, "F");
     (IFlag_AI, "AI");
     (IFlag_AF, "AF");
     (IFlag_IF, "IF");
     (IFlag_AIF, "AIF");
     (IFlag_None, "N")
    ]


let dmb_option_mfts: dmb_option_t mfts_int =
  mk_mfts
    "dmb_option_t"
    [ (FullSystemRW, "SY");
      (FullSystemW, "ST");
      (InnerShareableRW, "ISH");
      (InnerShareableW, "ISHST");
      (NonShareableRW, "NSH");
      (NonShareableW, "NSHST");
      (OuterShareableRW, "OSH");
      (OuterShareableW, "OSHST") ]

let shift_rotate_type_mfts: shift_rotate_type_t mfts_int =
  mk_mfts
    "shift_rotate_type_t"
    [ (SRType_LSL, "LSL");
      (SRType_LSR, "LSR");
      (SRType_ASR, "ASR");
      (SRType_ROR, "ROR");
      (SRType_RRX, "RRX") ]


class vfp_datatype_mcts_t: [vfp_datatype_t] mfts_int =
object

  inherit [vfp_datatype_t] mcts_t "vfp_datatype_t"

  method ts (t:vfp_datatype_t) =
    match t with
    | VfpNone -> "n"
    | VfpSize _ -> "z"
    | VfpFloat _ -> "f"
    | VfpInt _ -> "i"
    | VfpPolynomial _ -> "p"
    | VfpSignedInt _ -> "s"
    | VfpUnsignedInt _ -> "u"

  method tags = ["f"; "i"; "n"; "p"; "s"; "u"; "z"]

end

let vfp_datatype_mcts: vfp_datatype_t mfts_int =
  new vfp_datatype_mcts_t


class register_shift_rotate_mcts_t: [ register_shift_rotate_t ] mfts_int =
object

  inherit [ register_shift_rotate_t ] mcts_t "register_shift_rotate_t"

  method ts (r:register_shift_rotate_t) =
    match r with
    | ARMImmSRT _ -> "i"
    | ARMRegSRT _ -> "r"

  method tags = [ "i"; "r" ]

end

let register_shift_rotate_mcts:register_shift_rotate_t mfts_int =
  new register_shift_rotate_mcts_t


class arm_memory_offset_mcts_t: [ arm_memory_offset_t ] mfts_int =
object

  inherit [ arm_memory_offset_t ] mcts_t "arm_memory_offset_t"

  method ts (f:arm_memory_offset_t) =
    match f with
    | ARMImmOffset _ -> "i"
    | ARMIndexOffset _ -> "x"
    | ARMShiftedIndexOffset _ -> "s"

  method tags = [ "i"; "s"; "x" ]

end

let arm_memory_offset_mcts:arm_memory_offset_t mfts_int =
  new arm_memory_offset_mcts_t


class arm_simd_writeback_mcts_t: [arm_simd_writeback_t] mfts_int =
object

  inherit [arm_simd_writeback_t] mcts_t "arm_simd_writeback_t"

  method ts (f: arm_simd_writeback_t) =
    match f with
    | SIMDNoWriteback -> "n"
    | SIMDBytesTransferred _ -> "b"
    | SIMDAddressOffsetRegister _ -> "r"

  method tags = ["b"; "n"; "r"]

end

let arm_simd_writeback_mcts: arm_simd_writeback_t mfts_int =
  new arm_simd_writeback_mcts_t


class arm_simd_list_element_mcts_t: [arm_simd_list_element_t] mfts_int =
object

  inherit [arm_simd_list_element_t] mcts_t "arm_simd_list_element_t"

  method ts (f: arm_simd_list_element_t) =
    match f with
    | SIMDReg _ -> "r"
    | SIMDRegElement _ -> "e"
    | SIMDRegRepElement _ -> "re"

  method tags = ["e"; "r"; "re"]

end

let arm_simd_list_element_mcts: arm_simd_list_element_t mfts_int =
  new arm_simd_list_element_mcts_t


class arm_opkind_mcts_t: [ arm_operand_kind_t ] mfts_int =
object

  inherit [ arm_operand_kind_t ] mcts_t "arm_operand_kind_t"

  method ts (k:arm_operand_kind_t) =
    match k with
    | ARMDMBOption _ -> "d"
    | ARMCPSEffect _ -> "ce"
    | ARMInterruptFlags _ -> "if"
    | ARMReg _ -> "r"
    | ARMDoubleReg _ -> "dr"
    | ARMWritebackReg _ -> "wr"
    | ARMSpecialReg _ -> "sr"
    | ARMExtensionReg _ -> "xr"
    | ARMDoubleExtensionReg _ -> "dxr"
    | ARMExtensionRegElement _ -> "xre"
    | ARMRegList _ -> "l"
    | ARMExtensionRegList _ -> "xl"
    | ARMRegBitSequence _ -> "b"
    | ARMShiftedReg _ -> "s"
    | ARMImmediate _ -> "i"
    | ARMFPConstant _ -> "c"
    | ARMAbsolute _ -> "a"
    | ARMLiteralAddress _ -> "p"
    | ARMMemMultiple _ -> "m"
    | ARMOffsetAddress _ -> "o"
    | ARMSIMDAddress _ -> "simda"
    | ARMSIMDList _ -> "simdl"

  method tags =
    ["a"; "b"; "c"; "ce"; "d"; "dr"; "dxr"; "i"; "if"; "l"; "m"; "o"; "p"; "r"; "r"; "s";
     "simda"; "simdl"; "sr"; "wr"; "xr"]

end

let arm_opkind_mcts:arm_operand_kind_t mfts_int = new arm_opkind_mcts_t

let arm_opcode_cc_mfts: arm_opcode_cc_t mfts_int =
  mk_mfts
    "arm_opcode_cc_t"
    [ (ACCEqual, "eq");
      (ACCNotEqual, "ne");
      (ACCCarrySet, "cs");
      (ACCCarryClear, "cc");
      (ACCNegative, "neg");
      (ACCNonNegative, "nneg");
      (ACCOverflow, "ov");
      (ACCNoOverflow, "nov");
      (ACCUnsignedHigher, "uh");
      (ACCNotUnsignedHigher, "nuh");
      (ACCSignedGE, "ge");
      (ACCSignedLT, "lt");
      (ACCSignedGT, "gt");
      (ACCSignedLE, "le");
      (ACCAlways, "a");
      (ACCUnconditional,"unc")]

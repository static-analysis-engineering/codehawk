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

class arm_instr_class_mcts_t: [ arm_instr_class_t ] mfts_int =
object

  inherit [ arm_instr_class_t ] mcts_t "arm_instr_class_t"

  method ts (c:arm_instr_class_t) =
    match c with
    | DataProcRegType _ -> "dpr"
    | DataProcImmType _ -> "dpi"
    | LoadStoreRegType _ -> "lsr"
    | LoadStoreImmType _ -> "lsi"
    | MediaType _ -> "m"
    | BlockDataType _ -> "bd"
    | BranchLinkType _ -> "bl"
    | SupervisorType _ -> "s"
    | LoadStoreCoprocType _ -> "lsc"
    | CoprocessorType _ -> "c"
    | UnconditionalType _ -> "u"

  method tags = [
      "bd"; "bl"; "c"; "dpi"; "dpr"; "lsc"; "lsi"; "lsr"; "m"; "s"; "u" ]

end

let arm_instr_class_mcts:arm_instr_class_t mfts_int = new arm_instr_class_mcts_t

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

class arm_opkind_mcts_t: [ arm_operand_kind_t ] mfts_int =
object

  inherit [ arm_operand_kind_t ] mcts_t "arm_operand_kind_t"

  method ts (k:arm_operand_kind_t) =
    match k with
    | ARMDMBOption _ -> "d"
    | ARMReg _ -> "r"
    | ARMRegList _ -> "l"
    | ARMRegBitSequence _ -> "b"
    | ARMShiftedReg _ -> "s"
    | ARMImmediate _ -> "i"
    | ARMAbsolute _ -> "a"
    | ARMMemMultiple _ -> "m"
    | ARMOffsetAddress _ -> "o"

  method tags = [ "a"; "b"; "d"; "i"; "l"; "m"; "o"; "r"; "r"; "s" ]

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

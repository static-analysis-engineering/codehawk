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

let arm_reg_mfts: arm_reg_t mfts_int =
  mk_mfts
    "arm_reg_t"
    [ (AR0, "R0");
      (AR1, "R1");
      (AR2, "R2");
      (AR3, "R3");
      (AR4, "R4");
      (AR5, "R5");
      (AR6, "R6");
      (AR7, "R7");
      (AR8, "R8");
      (AR9, "R9");
      (AR10, "R10");
      (AR11, "R11");
      (AR12, "R12");
      (ARSP, "SP");
      (ARLR, "LR");
      (ARPC, "PC") ]

class arm_opkind_mcts_t: [ arm_operand_kind_t ] mfts_int =
object

  inherit [ arm_operand_kind_t ] mcts_t "arm_operand_kind_t"

  method ts (k:arm_operand_kind_t) =
    match k with
    | ARMReg _ -> "r"
    | ARMRegList _ -> "l"
    | ARMShiftedReg _ -> "s"
    | ARMImmediate _ -> "i"
    | ARMAbsolute _ -> "a"
    | ARMOffsetAddress _ -> "o"

  method tags = [ "a"; "i"; "l"; "o"; "r"; "s" ]

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
      (ACCAlways, "a") ]

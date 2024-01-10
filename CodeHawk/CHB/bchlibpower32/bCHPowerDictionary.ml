(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs, LLC

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
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHStringIndexTable
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHLibTypes
open BCHSumTypeSerializer

(* bchlibpower32 *)
open BCHPowerOpcodeRecords
open BCHPowerOperand
open BCHPowerSumTypeSerializer
open BCHPowerTypes


let bd = BCHDictionary.bdictionary


class pwr_dictionary_t: pwr_dictionary_int =
object (self)

  val pwr_opkind_table = mk_index_table "pwr-opkind-table"
  val pwr_operand_table = mk_index_table "pwr-operand-table"
  val pwr_branch_prediction_table = mk_index_table "pwr-branch_prediction_table"
  val pwr_opcode_table = mk_index_table "pwr-opcode-table"
  val pwr_bytestring_table = mk_string_index_table "pwr-bytestring-table"

  val mutable tables = []

  initializer
    tables <- [
      pwr_opkind_table;
      pwr_operand_table;
      pwr_branch_prediction_table;
      pwr_opcode_table
    ]

  method index_pwr_opkind (k: pwr_operand_kind_t) =
    let tags = [pwr_opkind_mcts#ts k] in
    let key = match k with
      | PowerGPReg i -> (tags, [i])
      | PowerSpecialReg r -> (tags @ [pwr_spr_mfts#ts r], [])
      | PowerRegisterField r -> (tags @ [pwr_crf_mfts#ts r], [])
      | PowerConditionRegisterBit i -> (tags, [i])
      | PowerImmediate imm -> (tags @ [imm#to_numerical#toString], [])
      | PowerAbsolute a -> (tags, [bd#index_address a])
      | PowerIndReg (i, off) -> (tags @ [off#toString], [i])
      | PowerIndexedIndReg (i, ix) -> (tags, [i; ix]) in
    pwr_opkind_table#add key

  method index_pwr_operand (op: pwr_operand_int) =
    let key =
      ([pwr_operand_mode_to_string op#get_mode],
       [self#index_pwr_opkind op#get_kind]) in
    pwr_operand_table#add key

  method index_pwr_branch_prediction (p: pwr_branch_prediction_t) =
    let tags = [pwr_branch_prediction_mcts#ts p] in
    let key = match p with
      | BPNone -> (tags, [])
      | BPPlus i -> (tags, [i])
      | BPMinus i -> (tags, [i]) in
    pwr_branch_prediction_table#add key

  method index_pwr_opcode (opc: pwr_opcode_t) =
    let setb x = if x then 1 else 0 in
    let oi = self#index_pwr_operand in
    let pi = self#index_pwr_branch_prediction in
    let tags = [pwr_opcode_name opc] in
    let itags t = tags @ [pwr_itype_mfts#ts t] in
    let key = match opc with
      | Add (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
         (itags pit, [setb rc; setb oe; oi rd; oi ra; oi rb; oi cr; oi so; oi ov])
      | AddCarrying (pit, rc, oe, rd, ra, rb, cr, so, ov, ca) ->
         (itags pit,
          [setb rc; setb oe; oi rd; oi ra; oi rb; oi cr; oi so; oi ov; oi ca])
      | AddExtended (pit, rc, oe, rd, ra, rb, cr, so, ov, ca) ->
         (itags pit,
          [setb rc; setb oe; oi rd; oi ra; oi rb; oi cr; oi so; oi ov; oi ca])
      | AddImmediate (pit, s, op2, op16, rc, rd, ra, simm, cr) ->
         (itags pit,
          [setb s; setb op2; setb op16; setb rc; oi rd; oi ra; oi simm; oi cr])
      | AddImmediateCarrying (pit, rc, rd, ra, simm, cr, ca) ->
         (itags pit, [setb rc; oi rd; oi ra; oi simm; oi cr; oi ca])
      | AddMinusOneExtended (pit, rc, oe, rd, ra, cr, ca, so, ov) ->
         (itags pit,
          [setb rc; setb oe; oi rd; oi ra; oi cr; oi ca; oi so; oi ov])
      | AddZeroExtended (pit, rc, oe, rd, ra, cr, ca, so, ov) ->
         (itags pit,
          [setb rc; setb oe; oi rd; oi ra; oi cr; oi ca; oi so; oi ov])
      | And (pit, rc, ra, rs, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr])
      | AndComplement (pit, rc, ra, rs, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr])
      | AndImmediate (pit, s, op2, rc, ra, rs, uimm, cr) ->
         (itags pit, [setb s; setb op2; setb rc; oi ra; oi rs; oi uimm; oi cr])
      | BitClearImmediate (pit, rx, ui5) -> (itags pit, [oi rx; oi ui5])
      | BitGenerateImmediate (pit, rx, ui5) -> (itags pit, [oi rx; oi ui5])
      | BitMaskGenerateImmediate (pit, rx, ui5) -> (itags pit, [oi rx; oi ui5])
      | BitSetImmediate (pit, rx, ui5) -> (itags pit, [oi rx; oi ui5])
      | BitTestImmediate (pit, rx, uimm, cr) ->
         (itags pit, [oi rx; oi uimm; oi cr])
      | Branch (pit, tgt) -> (itags pit, [oi tgt])
      | BranchConditional (pit, aa, bo, bi, bd) ->
         (itags pit, [setb aa; bo; bi; oi bd])
      | BranchConditionalLink (pit, aa, bo, bi, bd, crf) ->
         (itags pit, [setb aa; bo; bi; oi bd; oi crf])
      | BranchConditionalLinkRegister (pit, bo, bi, bh, lr) ->
         (itags pit, [bo; bi; bh; oi lr])
      | BranchConditionalLinkRegisterLink (pit, bo, bi, bh, lr) ->
         (itags pit, [bo; bi; bh; oi lr])
      | BranchCountRegister (pit, ctr) -> (itags pit, [oi ctr])
      | BranchCountRegisterLink (pit, ctr) -> (itags pit, [oi ctr])
      | BranchLink (pit, tgt, lr) -> (itags pit, [oi tgt; oi lr])
      | BranchLinkRegister (pit, lr) -> (itags pit, [oi lr])
      | BranchLinkRegisterLink (pit, lr) -> (itags pit, [oi lr])
      | CBranchDecrementNotZero (pit, aa, bo, bi, bp, bd, ctr) ->
         (itags pit, [setb aa; bo; bi; pi bp; oi bd; oi ctr])
      | CBranchDecrementZero (pit, aa, bo, bi, bp, bd, ctr) ->
         (itags pit, [setb aa; bo; bi; pi bp; oi bd; oi ctr])
      | CBranchEqual (pit, aa, bo, bi, bp, cr, bd) ->
         (itags pit, [setb aa; bo; bi; pi bp; oi cr; oi bd])
      | CBranchEqualLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
         (itags pit, [bo; bi; bh; pi bp; oi cr; oi lr])
      | CBranchGreaterEqual (pit, aa, bo, bi, bp, cr, bd) ->
         (itags pit, [setb aa; bo; bi; pi bp; oi cr; oi bd])
      | CBranchGreaterEqualLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
         (itags pit, [bo; bi; bh; pi bp; oi cr; oi lr])
      | CBranchGreaterThan (pit, aa, bo, bi, bp, cr, bd) ->
         (itags pit, [setb aa; bo; bi; pi bp; oi cr; oi bd])
      | CBranchGreaterThanLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
         (itags pit, [bo; bi; bh; pi bp; oi cr; oi lr])
      | CBranchLessEqual (pit, aa, bo, bi, bp, cr, bd) ->
         (itags pit, [setb aa; bo; bi; pi bp; oi cr; oi bd])
      | CBranchLessEqualLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
         (itags pit, [bo; bi; bh; pi bp; oi cr; oi lr])
      | CBranchLessThan (pit, aa, bo, bi, bp, cr, bd) ->
         (itags pit, [setb aa; bo; bi; pi bp; oi cr; oi bd])
      | CBranchLessThanLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
         (itags pit, [bo; bi; bh; pi bp; oi cr; oi lr])
      | CBranchNotEqual (pit, aa, bo, bi, bp, cr, bd) ->
         (itags pit, [setb aa; bo; bi; pi bp; oi cr; oi bd])
      | CBranchNotEqualLinkRegister (pit, bo, bi, bh, bp, cr, lr) ->
         (itags pit, [bo; bi; bh; pi bp; oi cr; oi lr])
      | ClearLeftShiftLeftWordImmediate (pit, rc, ra, rs, mb, sh, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi mb; oi sh; oi cr])
      | ClearLeftWordImmediate (pit, rc, ra, rs, mb) ->
         (itags pit, [setb rc; oi ra; oi rs; oi mb])
      | ClearRightWordImmediate (pit, rc, ra, rs, me, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi me; oi cr])
      | CompareImmediate (pit, op16, cr, ra, simm) ->
         (itags pit, [setb op16; oi cr; oi ra; oi simm])
      | CompareLogical (pit, cr, ra, rb) ->
         (itags pit, [oi cr; oi ra; oi rb])
      | CompareLogicalImmediate (pit, op16, cr, ra, uimm) ->
         (itags pit, [setb op16; oi cr; oi ra; oi uimm])
      | CompareWord (pit, cr, ra, rb) ->
         (itags pit, [oi cr; oi ra; oi rb])
      | ComplementRegister (pit, rc, ra, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rb; oi cr])
      | ConditionRegisterClear (pit, crd) -> (itags pit, [oi crd])
      | ConditionRegisterNot (pit, crd, cra) -> (itags pit, [oi crd; oi cra])
      | ConditionRegisterOr (pit, crd, cra, crb) ->
         (itags pit, [oi crd; oi cra; oi crb])
      | ConvertFloatingPointDPSignedFraction (pit, rd, rb) ->
         (itags pit, [oi rd; oi rb])
      | CountLeadingZerosWord (pit, rc, ra, rs, cr0) ->
         (itags pit, [setb rc; oi ra; oi rs; oi cr0])
      | DivideWord (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
         (itags pit,
          [setb rc; setb oe; oi rd; oi ra; oi rb; oi cr; oi so; oi ov])
      | DivideWordUnsigned (pit, rc, eo, rd, ra, rb, cr, so, ov) ->
         (itags pit,
          [setb rc; setb eo; oi rd; oi ra; oi rb; oi cr; oi so; oi ov])
      | EnforceInOrderExecutionIO (pit, mo) -> (itags pit, [oi mo])
      | ExtendSignByte (pit, rc, ra, rs, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi cr])
      | ExtendSignHalfword (pit, rc, ra, rs, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi cr])
      | ExtendZeroByte (pit, rx) -> (itags pit, [oi rx])
      | ExtendZeroHalfword (pit, rx) -> (itags pit, [oi rx])
      | ExtractRightJustifyWordImmediate (pit, rc, ra, rs, n, b, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi n; oi b; oi cr])
      | FloatingPointDPCompareEqual (pit, crfd, ra, rb) ->
         (itags pit, [oi crfd; oi ra; oi rb])
      | FloatingPointDPCompareGreaterThan (pit, crfd, ra, rb) ->
         (itags pit, [oi crfd; oi ra; oi rb])
      | FloatingPointDPCompareLessThan (pit, crfd, ra, rb) ->
         (itags pit, [oi crfd; oi ra; oi rb])
      | FloatingPointSubtract (pit, rd, ra, rb) ->
         (itags pit, [oi rd; oi ra; oi rb])
      | InsertRightWordImmediate (pit, rc, ra, rs, sh, mb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi sh; oi mb; oi cr])
      | InstructionSynchronize pit -> (itags pit, [])
      | IntegerSelect (pit, rd, ra, rb, crb) ->
         (itags pit, [oi rd; oi ra; oi rb; oi crb])
      | IntegerSelectEqual (pit, rd, ra, rb, cr) ->
         (itags pit, [oi rd; oi ra; oi rb; oi cr])
      | IntegerSelectGreaterThan (pit, rd, ra, rb, cr) ->
         (itags pit, [oi rd; oi ra; oi rb; oi cr])
      | IntegerSelectLessThan (pit, rd, ra, rb, cr) ->
         (itags pit, [oi rd; oi ra; oi rb; oi cr])
      | LoadByteZero (pit, u, rd, ra, mem) ->
         (itags pit, [setb u; oi rd; oi ra; oi mem])
      | LoadByteZeroIndexed (pit, u, rd, ra, rb, mem) ->
         (itags pit, [setb u; oi rd; oi ra; oi rb; oi mem])
      | LoadHalfwordAlgebraic (pit, u, rd, ra, mem) ->
         (itags pit, [setb u; oi rd; oi ra; oi mem])
      | LoadHalfwordAlgebraicIndexed (pit, u, rd, ra, rb, mem) ->
         (itags pit, [setb u; oi rd; oi ra; oi rb; oi mem])
      | LoadHalfwordZero (pit, u, rd, ra, mem) ->
         (itags pit, [setb u; oi rd; oi ra; oi mem])
      | LoadHalfwordZeroIndexed (pit, u, rd, ra, rb, mem) ->
         (itags pit, [setb u; oi rd; oi ra; oi rb; oi mem])
      | LoadImmediate (pit, sg, sh, rd, imm) ->
         (itags pit, [setb sg; setb sh; oi rd; oi imm])
      | LoadMultipleVolatileGPRWord (pit, ra, mem) ->
         (itags pit, [oi ra; oi mem])
      | LoadMultipleVolatileSPRWord (pit, ra, mem, cr, lr, ctr, xer) ->
         (itags pit, [oi ra; oi mem; oi cr; oi lr; oi ctr; oi xer])
      | LoadMultipleVolatileSRRWord (pit, ra, mem, srr0, srr1) ->
         (itags pit, [oi ra; oi mem; oi srr0; oi srr1])
      | LoadMultipleWord (pit, rd, ra, mem) ->
         (itags pit, [oi rd; oi ra; oi mem])
      | LoadWordZero (pit, u, rd, ra, mem) ->
         (itags pit, [setb u; oi rd; oi ra; oi mem])
      | LoadWordZeroIndexed (pit, u, rd, ra, rb, mem) ->
         (itags pit, [setb u; oi rd; oi ra; oi rb; oi mem])
      | MemoryBarrier (pit, mo) -> (itags pit, [oi mo])
      | MoveConditionRegisterField (pit, crfd, crs) ->
         (itags pit, [oi crfd; oi crs])
      | MoveFromAlternateRegister (pit, rx, ary) -> (itags pit, [oi rx; oi ary])
      | MoveFromConditionRegister (pit, rd, cr) -> (itags pit, [oi rd; oi cr])
      | MoveFromCountRegister (pit, rx, ctr) -> (itags pit, [oi rx; oi ctr])
      | MoveFromExceptionRegister (pit, rd, xer) -> (itags pit, [oi rd; oi xer])
      | MoveFromLinkRegister (pit, rd, lr) -> (itags pit, [oi rd; oi lr])
      | MoveFromMachineStateRegister (pit, rd, msr) ->
         (itags pit, [oi rd; oi msr])
      | MoveFromSpecialPurposeRegister (pit, rd, spr) ->
         (itags pit, [oi rd; oi spr])
      | MoveRegister (pit, rc, rd, rs) -> (itags pit, [setb rc; oi rd; oi rs])
      | MoveToAlternateRegister (pit, arx, ry) -> (itags pit, [oi arx; oi ry])
      | MoveToConditionRegister (pit, cr, rs) -> (itags pit, [oi cr; oi rs])
      | MoveToConditionRegisterFields (pit, crm, rs, crfs) ->
         (itags pit, [oi crm; oi rs] @ (List.map oi crfs))
      | MoveToCountRegister (pit, ctr, rs) -> (itags pit, [oi ctr; oi rs])
      | MoveToExceptionRegister (pit, xer, rs) -> (itags pit, [oi xer; oi rs])
      | MoveToLinkRegister (pit, lr, rs) -> (itags pit, [oi lr; oi rs])
      | MoveToMachineStateRegister (pit, msr, rs) -> (itags pit, [oi msr; oi rs])
      | MoveToSpecialPurposeRegister (pit, spr, rs) ->
         (itags pit, [oi spr; oi rs])
      | MultiplyHighWord (pit, rc, rd, ra, rb, cr) ->
         (itags pit, [setb rc; oi rd; oi ra; oi rb; oi cr])
      | MultiplyHighWordUnsigned (pit, rc, rd, ra, rb, cr) ->
         (itags pit, [setb rc; oi rd; oi ra; oi rb; oi cr])
      | MultiplyLowImmediate (pit, op2, rd, ra, simm) ->
         (itags pit, [setb op2; oi rd; oi ra; oi simm])
      | MultiplyLowWord (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
         (itags pit, [setb rc; setb oe; oi rd; oi ra; oi rb; oi cr; oi so; oi ov])
      | Negate (pit, rc, oe, rd, ra, cr, so, ov) ->
         (itags pit, [setb rc; setb oe; oi rd; oi ra; oi cr; oi so; oi ov])
      | Or (pit, rc, ra, rs, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr])
      | OrComplement (pit, rc, ra, rs, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr])
      | OrImmediate (pit, rc, s, op2, ra, rs, uimm, cr) ->
         (itags pit, [setb rc; setb s; setb op2; oi ra; oi rs; oi uimm; oi cr])
      | ReturnFromDebugInterrupt (pit, msr, dsr0, dsr1) ->
         (itags pit, [oi msr; oi dsr0; oi dsr1])
      | ReturnFromInterrupt (pit, msr, sr0, sr1) ->
         (itags pit, [oi msr; oi sr0; oi sr1])
      | ReturnFromMachineCheckInterrupt (pit, msr, mcsr0, mcsr1) ->
         (itags pit, [oi msr; oi mcsr0; oi mcsr1])
      | RotateLeftWord (pit, rc, ra, rs, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr])
      | RotateLeftWordImmediateAndMask (pit, rc, ra, rs, sh, mb, me, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi sh; oi mb; oi me; oi cr])
      | RotateLeftWordImmediateMaskInsert (pit, rc, ra, rs, sh, mb, me, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi sh; oi mb; oi me; oi cr])
      | ShiftLeftWord (pit, rc, ra, rs, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr])
      | ShiftLeftWordImmediate (pit, rc, ra, rs, sh, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi sh; oi cr])
      | ShiftRightAlgebraicWord (pit, rc, ra, rs, rb, cr, ca) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr; oi ca])
      | ShiftRightAlgebraicWordImmediate (pit, rc, ra, rs, sh, cr, ca) ->
         (itags pit, [setb rc; oi ra; oi rs; oi sh; oi cr; oi ca])
      | ShiftRightWord (pit, rc, ra, rs, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr])
      | ShiftRightWordImmediate (pit, rc, ra, rs, sh, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi sh; oi cr])
      | StoreByte (pit, u, rs, ra, mem) ->
         (itags pit, [setb u; oi rs; oi ra; oi mem])
      | StoreByteIndexed (pit, u, rs, ra, rb, mem) ->
         (itags pit, [setb u; oi rs; oi ra; oi rb; oi mem])
      | StoreHalfword (pit, u, rs, ra, mem) ->
         (itags pit, [setb u; oi rs; oi ra; oi mem])
      | StoreHalfwordIndexed (pit, u, rs, ra, rb, mem) ->
         (itags pit, [setb u; oi rs; oi ra; oi rb; oi mem])
      | StoreMultipleWord (pit, rs, ra, mem) ->
         (itags pit, [oi rs; oi ra; oi mem])
      | StoreMultipleVolatileGPRWord (pit, ra, mem) ->
         (itags pit, [oi ra; oi mem])
      | StoreMultipleVolatileSPRWord (pit, ra, mem, cr, lr, ctr, xer) ->
         (itags pit, [oi ra; oi mem; oi cr; oi lr; oi ctr; oi xer])
      | StoreMultipleVolatileSRRWord (pit, ra, mem, srr0, srr1) ->
         (itags pit, [oi ra; oi mem; oi srr0; oi srr1])
      | StoreWord (pit, u, rs, ra, mem) ->
         (itags pit, [setb u; oi rs; oi ra; oi mem])
      | StoreWordIndexed (pit, u, rs, ra, rb, mem) ->
         (itags pit, [setb u; oi rs; oi ra; oi rb; oi mem])
      | Subtract (pit, rx, ry) -> (itags pit, [oi rx; oi ry])
      | SubtractFrom (pit, rc, oe, rd, ra, rb, cr, so, ov) ->
         (itags pit, [setb rc; setb oe; oi rd; oi ra; oi rb; oi cr; oi so; oi ov])
      | SubtractFromCarrying (pit, rc, oe, rd, ra, rb, cr, ca, so, ov) ->
         (itags pit,
          [setb rc; setb oe; oi rd; oi ra; oi rb; oi cr; oi ca; oi so; oi ov])
      | SubtractFromExtended (pit, rc, oe, rd, ra, rb, cr, ca, so, ov) ->
         (itags pit,
          [setb rc; setb oe; oi rd; oi ra; oi rb; oi cr; oi ca; oi so; oi ov])
      | SubtractFromImmediateCarrying (pit, rc, rd, ra, simm, cr, ca) ->
         (itags pit, [setb rc; oi rd; oi ra; oi simm; oi cr; oi ca])
      | SubtractFromZeroExtended (pit, rc, oe, rd, ra, cr, so, ov, ca) ->
         (itags pit,
          [setb rc; setb oe; oi rd; oi ra; oi cr; oi so; oi ov; oi ca])
      | SubtractImmediate (pit, rc, rd, ra, imm, cr) ->
         (itags pit, [setb rc; oi rd; oi ra; oi imm; oi cr])
      | TLBWriteEntry (pit) -> (itags pit, [])
      | VectorLoadDoubleDouble (pit, rd, ra, mem) ->
         (itags pit, [oi rd; oi ra; oi mem])
      | VectorStoreDoubleDouble (pit, rs, ra, mem) ->
         (itags pit, [oi rs; oi ra; oi mem])
      | VectorXor (pit, rd, ra, rb) -> (itags pit, [oi rd; oi ra; oi rb])
      | WriteMSRExternalEnableImmediate (pit, enable, msr) ->
         (itags pit, [setb enable; oi msr])
      | Xor (pit, rc, ra, rs, rb, cr) ->
         (itags pit, [setb rc; oi ra; oi rs; oi rb; oi cr])
      | XorImmediate (pit, rc, s, ra, rs, uimm, cr) ->
         (itags pit, [setb rc; setb s; oi ra; oi rs; oi uimm; oi cr])
      | OpInvalid -> (tags, [])
      | NotCode _ -> (tags, [])
      | NoOperation -> (tags, [])
      | OpcodeIllegal i -> (tags, [i])
      | OpcodeUnpredictable s -> (tags, [bd#index_string s])
      | OpcodeUndefined s -> (tags, [bd#index_string s])
      | NotRecognized (s, dw) -> (tags @ [s; dw#to_hex_string], [])
    in
    pwr_opcode_table#add key

  method index_pwr_bytestring (s: string): int = pwr_bytestring_table#add s

  method write_xml_pwr_bytestring
           ?(tag="ibt") (node: xml_element_int) (s: string) =
    node#setIntAttribute tag (self#index_pwr_bytestring s)

  method write_xml_pwr_opcode
           ?(tag="iopc") (node: xml_element_int) (opc: pwr_opcode_t) =
    node#setIntAttribute tag (self#index_pwr_opcode opc)

  method write_xml (node: xml_element_int) =
    let bnode = xmlElement pwr_bytestring_table#get_name in
    begin
      pwr_bytestring_table#write_xml bnode;
      node#appendChildren [bnode];
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end) tables)
    end

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      pwr_bytestring_table#read_xml (getc pwr_bytestring_table#get_name);
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

end


let pwr_dictionary: pwr_dictionary_int = new pwr_dictionary_t

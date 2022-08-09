(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs, LLC

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

(* bchlibarm32 *)
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMSumTypeSerializer
open BCHARMTypes

let bd = BCHDictionary.bdictionary

let raise_tag_error (name:string) (tag:string) (accepted:string list) =
  let msg =
    LBLOCK [ STR "Type " ; STR name ; STR " tag: " ; STR tag ;
             STR " not recognized. Accepted tags: " ;
             pretty_print_list accepted (fun s -> STR s) "" ", " "" ] in
  begin
    ch_error_log#add "serialization tag" msg ;
    raise (BCH_failure msg)
  end

class arm_dictionary_t:arm_dictionary_int =
object (self)

  val vfp_datatype_table = mk_index_table "vfp-datatype-table"
  val register_shift_rotate_table = mk_index_table "register-shift-table"
  val arm_memory_offset_table = mk_index_table "arm-memory-offset-table"
  val arm_simd_writeback_table = mk_index_table "arm-simd-writeback-table"
  val arm_simd_list_element_table = mk_index_table "arm-simd-list-element-table"
  val arm_opkind_table = mk_index_table "arm-opkind-table"
  val arm_operand_table = mk_index_table "arm-operand-table"
  val arm_opcode_table = mk_index_table "arm-opcode-table"
  val arm_bytestring_table = mk_string_index_table "arm-bytestring-table"

  val mutable tables = []

  initializer
    tables <- [
      vfp_datatype_table;
      register_shift_rotate_table;
      arm_memory_offset_table;
      arm_simd_writeback_table;
      arm_simd_list_element_table;
      arm_opkind_table;
      arm_operand_table;
      arm_opcode_table;
    ]

  method index_vfp_datatype (t: vfp_datatype_t) =
    let tags = [vfp_datatype_mcts#ts t] in
    let key = match t with
      | VfpNone -> (tags, [])
      | VfpSize s
        | VfpFloat s
        | VfpInt s
        | VfpPolynomial s
        | VfpSignedInt s
        | VfpUnsignedInt s -> (tags, [s]) in
    vfp_datatype_table#add key

  method index_register_shift_rotate (rs:register_shift_rotate_t) =
    let tags = [ register_shift_rotate_mcts#ts rs ] in
    let key = match rs with
      | ARMImmSRT (srt,imm) ->
         (tags @ [ shift_rotate_type_mfts#ts srt ],[ imm ])
      | ARMRegSRT (srt,reg) ->
         (tags @ [ shift_rotate_type_mfts#ts srt ; arm_reg_mfts#ts reg ],[]) in
    register_shift_rotate_table#add key

  method index_arm_memory_offset (f:arm_memory_offset_t) =
    let tags = [arm_memory_offset_mcts#ts f] in
    let key = match f with
      | ARMImmOffset imm -> (tags, [imm])
      | ARMIndexOffset (r, off) -> (tags @ [arm_reg_mfts#ts r], [off])
      | ARMShiftedIndexOffset (r, rs, off) ->
         (tags @ [arm_reg_mfts#ts r],
          [self#index_register_shift_rotate rs; off]) in
    arm_memory_offset_table#add key

  method index_arm_simd_writeback (f: arm_simd_writeback_t) =
    let tags = [arm_simd_writeback_mcts#ts f] in
    let key = match f with
      | SIMDNoWriteback -> (tags, [])
      | SIMDBytesTransferred t -> (tags, [t])
      | SIMDAddressOffsetRegister r -> (tags @ [arm_reg_mfts#ts r], []) in
    arm_simd_writeback_table#add key

  method index_arm_simd_list_element (f: arm_simd_list_element_t) =
    let tags = [arm_simd_list_element_mcts#ts f] in
    let key = match f with
      | SIMDReg r -> (tags, [bd#index_arm_extension_register r])
      | SIMDRegElement e -> (tags, [bd#index_arm_extension_register_element e])
      | SIMDRegRepElement e ->
         (tags, [bd#index_arm_extension_register_replicated_element e]) in
    arm_simd_list_element_table#add key

  method index_arm_opkind (k:arm_operand_kind_t) =
    let setb x = if x then 1 else 0 in
    let setoptint x = match x with Some i -> i | _ -> (-1) in
    let tags = [arm_opkind_mcts#ts k] in
    let key = match k with
      | ARMDMBOption o -> (tags @ [dmb_option_mfts#ts o], [])
      | ARMReg r -> (tags @ [arm_reg_mfts#ts r], [])
      | ARMWritebackReg (issingle, r, offset) ->
         (tags @ [arm_reg_mfts#ts r], [setb issingle; setoptint offset])
      | ARMSpecialReg r -> (tags @ [arm_special_reg_mfts#ts r], [])
      | ARMExtensionReg r -> (tags, [bd#index_arm_extension_register r])
      | ARMExtensionRegElement e ->
         (tags, [bd#index_arm_extension_register_element e])
      | ARMRegList rl -> (tags @ (List.map arm_reg_mfts#ts rl),[])
      | ARMExtensionRegList rl ->
         (tags, List.map bd#index_arm_extension_register rl)
      | ARMSIMDList el -> (tags, List.map self#index_arm_simd_list_element el)
      | ARMShiftedReg (r,rs) ->
         (tags @ [arm_reg_mfts#ts r], [self#index_register_shift_rotate rs])
      | ARMRegBitSequence (r, lsb, widthm1) ->
         (tags @ [ arm_reg_mfts#ts r ],[ lsb; widthm1 ])
      | ARMAbsolute addr -> (tags, [bd#index_address addr])
      | ARMLiteralAddress addr -> (tags, [bd#index_address addr])
      | ARMMemMultiple (r, align, n, size) ->
         (tags @ [ arm_reg_mfts#ts r ],[align; n; size])
      | ARMOffsetAddress (r, align, offset, isadd, iswback, isindex) ->
         let ioffset = self#index_arm_memory_offset offset in
         (tags @ [arm_reg_mfts#ts r],
          [align; ioffset; setb isadd; setb iswback; setb isindex])
      | ARMSIMDAddress (r, align, wb) ->
         (tags @ [arm_reg_mfts#ts r], [align; self#index_arm_simd_writeback wb])
      | ARMFPConstant x -> (tags @ [string_of_float x], [])
      | ARMImmediate imm -> (tags @ [imm#to_numerical#toString], []) in
    arm_opkind_table#add key

  method index_arm_operand (op:arm_operand_int) =
    let key =
      ([arm_operand_mode_to_string op#get_mode],
       [self#index_arm_opkind op#get_kind]) in
    arm_operand_table#add key

  method index_arm_opcode (opc:arm_opcode_t) =
    let setb x = if x then 1 else 0 in
    let setopt x = match x with Some k -> k | _ -> (-1) in
    let oi = self#index_arm_operand in
    let di = self#index_vfp_datatype in
    let ci = arm_opcode_cc_mfts#ts in
    let tags = [ get_arm_opcode_name opc ] in
    let ctags c = tags @ [ ci c ] in
    let key = match opc with
      | Add (s, c, rd, rn, imm, tw)
        | AddCarry (s, c, rd, rn, imm, tw) ->
         (ctags c, [setb s ; oi rd; oi rn; oi imm; setb tw])
      | Adr (cond,rd,addr) ->
         (tags @ [ ci cond ], [ oi rd ; oi addr ])
      | ArithmeticShiftRight (s, c, rd, rn, rm, tw) ->
         (ctags c, [setb s; oi rd; oi rn; oi rm; setb tw ])
      | BitFieldClear (c, rd, lsb, width, msb) ->
         (ctags c, [oi rd; lsb; width; msb])
      | BitFieldInsert (c, rd, rn, lsb, width, msb) ->
         (ctags c, [oi rd; oi rn; lsb; width; msb])
      | BitwiseAnd (s, c, rd, rn, imm, tw) ->
         (ctags c, [setb s; oi rd; oi rn; oi imm; setb tw])
      | BitwiseNot (s ,c,rd, imm, tw) ->
         (ctags c, [setb s; oi rd; oi imm; setb tw])
      | BitwiseOrNot (setflags,cond,rd,rn,imm) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd; oi rn; oi imm])
      | BitwiseBitClear (s,c,rd,rn,imm,tw) ->
         (ctags c, [setb s; oi rd; oi rn; oi imm; setb tw])
      | BitwiseExclusiveOr (s,c,rd,rn,imm,tw) ->
         (ctags c, [setb s; oi rd; oi rn; oi imm; setb tw])
      | BitwiseOr (s,c,rd,rn,imm,tw) ->
         (ctags c, [setb s; oi rd; oi rn; oi imm; setb tw])
      | Branch (c, addr, tw) -> (ctags c, [oi addr; setb tw])
      | BranchExchange (cond,addr)
        | BranchLink (cond,addr)
        | BranchLinkExchange (cond,addr) ->
         (tags @ [ ci cond ], [ oi addr ])
      | ByteReverseWord (c, rd, rm, tw) -> (ctags c,[ oi rd; oi rm; setb tw])
      | ByteReversePackedHalfword (c, rd, rm, tw) ->
         (ctags c, [oi rd; oi rm; setb tw])
      | Compare (c,op1,op2,tw) ->
         (ctags c, [oi op1; oi op2; setb tw])
      | CompareNegative (cond,op1,op2)
        | CountLeadingZeros (cond,op1,op2) ->
         (tags @ [ ci cond ], [ oi op1; oi op2 ])
      | CompareBranchNonzero (op1, op2)
        | CompareBranchZero (op1, op2) -> (tags, [oi op1; oi op2])
      | DataMemoryBarrier (c,op) -> (ctags c,[oi op])
      | IfThen (c, xyz) -> ((ctags c) @ [xyz], [])
      | FLoadMultipleIncrementAfter (wb, c, rn, rl, mem) ->
         (ctags c, [setb wb; oi rn; oi rl; oi mem])
      | FStoreMultipleIncrementAfter (wb, c, rn, rl, mem) ->
         (ctags c, [setb wb; oi rn; oi rl; oi mem])
      | LoadCoprocessor (islong, c, coproc, crd, mem, opt) ->
         (ctags c, [setb islong; coproc; crd; oi mem; setopt opt])
      | LoadMultipleDecrementBefore (wb,c,rn,rl,mem)
        | LoadMultipleDecrementAfter (wb,c,rn,rl,mem)
        | LoadMultipleIncrementAfter (wb,c,rn,rl,mem)
        | LoadMultipleIncrementBefore (wb,c,rn,rl,mem) ->
         (ctags c, [ setb wb; oi rn; oi rl; oi mem ])
      | LoadRegister (c, rt, rn, rm, mem, tw) ->
         (ctags c, [oi rt; oi rn; oi rm; oi mem; setb tw])
      | LoadRegisterByte (c, rt, rn, rm, mem, tw) ->
         (ctags c, [oi rt; oi rn; oi rm; oi mem; setb tw ])
      | LoadRegisterDual (c, rt, rt2, rn, rm, mem, mem2) ->
         (ctags c, [oi rt; oi rt2; oi rn; oi rm; oi mem; oi mem2])
      | LoadRegisterExclusive (c, rt, rn, rm, mem) ->
         (ctags c, [oi rt; oi rn; oi rm; oi mem])
      | LoadRegisterHalfword (c, rt, rn, rm, mem, tw)->
         (ctags c, [oi rt; oi rn; oi rm; oi mem; setb tw])
      | LoadRegisterSignedByte (c,rt,rn,rm,mem,tw) ->
         (ctags c,[ oi rt; oi rn; oi rm; oi mem; setb tw])
      | LoadRegisterSignedHalfword (c, rt, rn, rm, mem, tw) ->
         (ctags c,[ oi rt; oi rn; oi rm; oi mem; setb tw])
      | LogicalShiftLeft (s, c, rd, rn, rm, tw) ->
         (ctags c, [setb s; oi rd; oi rn; oi rm; setb tw])
      | LogicalShiftRight (s,c,rd,rn,rm,tw) ->
         (ctags c, [setb s; oi rd; oi rn; oi rm; setb tw])
      | Move (s, c, rd, rm, tw, aw) ->
         (ctags c, [setb s; oi rd; oi rm; setb tw; setb aw])
      | MoveRegisterCoprocessor (c, coproc, opc1, rt, crn, crm, opc2) ->
         (ctags c, [coproc; opc1; oi rt; crn; crm; opc2])
      | MoveToCoprocessor (c, coproc, opc1, rt, crn, crm, opc2) ->
         (ctags c, [coproc; opc1; oi rt; crn; crm; opc2])
      | MoveTop (c,rd,imm) -> (ctags c,[ oi rd; oi imm ])
      | MoveTwoRegisterCoprocessor (c, coproc, opc, rt, rt2, crm) ->
         (ctags c, [coproc; opc; oi rt; oi rt2; crm])
      | Multiply (setflags,cond,rd,rn,rm) ->
         (tags @ [ ci cond ], [setb setflags; oi rd; oi rn; oi rm])
      | MultiplyAccumulate (setflags,cond,rd,rn,rm,ra) ->
         (tags @ [ ci cond ], [setb setflags; oi rd; oi rn; oi rm; oi ra ])
      | MultiplySubtract (c, rd, rn, rm, ra) ->
         (ctags c, [oi rd; oi rn; oi rm; oi ra])
      | Pop (c, sp, rl, tw) -> (ctags c, [oi sp; oi rl; setb tw])
      | PreloadData (w, c, base, mem) -> (ctags c, [setb w; oi base; oi mem])
      | Push (c, sp, rl, tw) ->  (ctags c, [oi sp; oi rl; setb tw])
      | ReverseBits (c, dst, src) -> (ctags c, [oi dst; oi src])
      | ReverseSubtract (s, c, dst, src, imm, tw) ->
         (ctags c, [setb s; oi dst; oi src; oi imm; setb tw])
      | RotateRight (s, c, rd, rn, rm) ->
         (ctags c, [setb s; oi rd; oi rn; oi rm])
      | RotateRightExtend (s,c,rd,rm) -> (ctags c, [setb s; oi rd; oi rm])
      | SelectBytes(c, rd, rn, rm) -> (ctags c, [oi rd; oi rn; oi rm])
      | SignedBitFieldExtract (c, rd, rn) -> (ctags c, [oi rd; oi rn])
      | SignedDivide (c, rd, rn, rm) -> (ctags c, [oi rd; oi rn; oi rm])
      | SignedExtendByte (c, rd, rm, tw) -> (ctags c, [oi rd; oi rm; setb tw ])
      | SignedExtendHalfword (c, rd, rm, tw) ->
         (ctags c, [oi rd; oi rm; setb tw])
      | SignedMostSignificantWordMultiply (c, rd, rm, rn, roundf) ->
         (ctags c, [oi rd; oi rm; oi rn; roundf])
      | SignedMostSignificantWordMultiplyAccumulate (c, rd, rm, rn, ra, roundf) ->
         (ctags c, [oi rd; oi rm; oi rn; oi ra; roundf])
      | SignedMultiplyLong (s,c,rdlo,rdhi,rn,rm)
        | SignedMultiplyAccumulateLong (s,c,rdlo,rdhi,rn,rm) ->
         (ctags c, [setb s; oi rdlo; oi rdhi; oi rn; oi rm])
      | SingleBitFieldExtract (c,rd,rn) -> (ctags c, [ oi rd; oi rn ])
      | StoreMultipleDecrementBefore (wb,c,rn,rl,mem,tw)
        | StoreMultipleIncrementAfter (wb,c,rn,rl,mem,tw)
        | StoreMultipleIncrementBefore (wb,c,rn,rl,mem,tw) ->
         (ctags c, [ setb wb; oi rn; oi rl; oi mem; setb tw ])
      | StoreRegister (c, rt, rn, rm, mem, tw) ->
         (ctags c, [oi rt; oi rn; oi rm; oi mem; setb tw])
      | StoreRegisterByte (c, rt, rn, mem, tw) ->
         (ctags c, [oi rt; oi rn; oi mem; setb tw])
      | StoreRegisterHalfword (c, rt, rn, rm, mem, tw) ->
         (ctags c, [oi rt; oi rn; oi rm; oi mem; setb tw ])
      | StoreRegisterDual (c, rt, rt2, rn, rm, mem, mem2) ->
         (ctags c, [oi rt; oi rt2; oi rn; oi rm; oi mem; oi mem2])
      | StoreRegisterExclusive (c, rd, rt, rn, mem) ->
         (ctags c, [oi rd; oi rt; oi rn; oi mem])
      | Subtract (s, c, dst, src, imm, tw, w) ->
         (ctags c, [setb s; oi dst; oi src; oi imm; setb tw; setb w])
      | SubtractCarry (s, c, rd, rn, rm, tw) ->
         (ctags c, [setb s; oi rd; oi rn; oi rm; setb tw])
      | ReverseSubtractCarry (setflags,cond,dst,src,imm) ->
         (tags @ [ ci cond ], [ setb setflags; oi dst; oi src; oi imm ])
      | Swap (c, rt, rt2, mem) -> (ctags c, [oi rt; oi rt2; oi mem])
      | SwapByte (c, rt, rt2, mem) -> (ctags c, [oi rt; oi rt2; oi mem])
      | TableBranchByte (c, rn, rm, mem) -> (ctags c, [oi rn; oi rm; oi mem])
      | TableBranchHalfword (c, rn, rm, mem) -> (ctags c, [oi rn; oi rm; oi mem])
      | Test (cond,src1,src2)
        | TestEquivalence (cond,src1,src2) ->
         (tags @ [ ci cond ], [oi src1; oi src2 ])
      | UnsignedAdd8 (c, rd, rn, rm) -> (ctags c, [oi rd; oi rn; oi rm])
      | UnsignedBitFieldExtract (c,rd,rn) -> (ctags c, [oi rd; oi rn ])
      | UnsignedDivide (c, rd, rn, rm) -> (ctags c, [oi rd; oi rn; oi rm])
      | UnsignedExtendAddByte (c, rd, rn, rm) ->
         (ctags c, [oi rd; oi rn; oi rm])
      | UnsignedExtendAddHalfword (c, rd, rn, rm) ->
         (ctags c, [oi rd; oi rn; oi rm])
      | UnsignedExtendByte (c, rd, rm, tw) -> (ctags c, [oi rd; oi rm; setb tw])
      | UnsignedExtendHalfword (c,rd,rm) -> (ctags c, [oi rd; oi rm])
      | UnsignedMultiplyAccumulateLong (s, c, rdlo, rdhi, rn, rm) ->
         (ctags c, [setb s; oi rdlo; oi rdhi; oi rn; oi rm])
      | UnsignedMultiplyLong (s, c, rdlo, rdhi, rn, rm) ->
         (ctags c, [setb s; oi rdlo; oi rdhi; oi rn; oi rm])
      | UnsignedSaturatingSubtract8 (c, rd, rn, rm) ->
         (ctags c, [oi rd; oi rn; oi rm])
      | VectorAdd (c, dt, dst, src1, src2) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2])
      | VectorAddLong (c, dt, dst, src1, src2) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2])
      | VectorAddWide (c, dt, dst, src1, src2) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2])
      | VectorBitwiseAnd (c, dst, src1, src2) ->
         (ctags c, [oi dst; oi src1; oi src2])
      | VectorBitwiseBitClear (c, dt, dst, imm) ->
         (ctags c, [di dt; oi dst; oi imm])
      | VectorBitwiseExclusiveOr (c, dst, src1, src2) ->
         (ctags c, [oi dst; oi src1; oi src2])
      | VectorBitwiseNot (c, dt, dst, src) ->
         (ctags c, [di dt; oi dst; oi src])
      | VectorBitwiseOr (c, dst, src1, src2) ->
         (ctags c, [oi dst; oi src1; oi src2])
      | VCompare (nan, c, dt, op1, op2) ->
         (ctags c, [if nan then 1 else 0; di dt; oi op1; oi op2])
      | VectorConvert (round, c, dstdt, srcdt, dst, src) ->
         ((ctags c),
          [if round then 1 else 0; di dstdt; di srcdt; oi dst; oi src])
      | VDivide (c, dt, dst, src1, src2) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2])
      | VectorDuplicate (c, dt, regs, elements, dst, src) ->
         (ctags c, [di dt; regs; elements; oi dst; oi src])
      | VectorExtract (c, dt, dst, src1, src2, imm) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2; oi imm])
      | VectorLoadMultipleIncrementAfter (wb, c, rn, rl, mem) ->
         (ctags c, [setb wb; oi rn; oi rl; oi mem])
      | VectorLoadOne (wb, c, sz, rl, rn, mem, rm) ->
         (ctags c, [setb wb; di sz; oi rl; oi rn; oi mem; oi rm])
      | VLoadRegister (c, dst, base, mem) ->
         (ctags c, [oi dst; oi base; oi mem])
      | VectorMove (c, dt, ops) -> (ctags c, (di dt)::(List.map oi ops))
      | VectorMoveLong (c, dt, dst, src) -> (ctags c, [di dt; oi dst; oi src])
      | VectorMoveNarrow (c, dt, dst, src) -> (ctags c, [di dt; oi dst; oi src])
      | VMoveRegisterStatus (c, dst, src) -> (ctags c, [oi dst; oi src])
      | VMoveToSystemRegister (c, dst, src) -> (ctags c, [oi dst; oi src])
      | VectorMultiply (c, dt, dst, src1, src2) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2])
      | VectorMultiplyAccumulateLong (c, dt, dst, src1, src2) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2])
      | VectorMultiplyLong (c, dt, dst, src1, src2) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2])
      | VectorNegate (c, dt, dst, src) -> (ctags c, [di dt; oi dst; oi src])
      | VectorPop (c, sp, rl, mem) -> (ctags c, [oi sp; oi rl; oi mem])
      | VectorPush (c, sp, rl, mem) -> (ctags c, [oi sp; oi rl; oi mem])
      | VectorReverseDoublewords (c, dt, dst, src) ->
         (ctags c, [di dt; oi dst; oi src])
      | VectorReverseHalfwords (c, dt, dst, src) ->
         (ctags c, [di dt; oi dst; oi src])
      | VectorReverseWords (c, dt, dst, src) ->
         (ctags c, [di dt; oi dst; oi src])
      | VectorRoundingShiftRightAccumulate (c, dt, dst, src, imm) ->
         (ctags c, [di dt; oi dst; oi src; oi imm])
      | VectorShiftLeft (c, dt, dst, src, src2) ->
         (ctags c, [di dt; oi dst; oi src; oi src2])
      | VectorShiftRight (c, dt, dst, src, imm) ->
         (ctags c, [di dt; oi dst; oi src; oi imm])
      | VectorShiftRightInsert (c, dt, dst, src, imm) ->
         (ctags c, [di dt; oi dst; oi src; oi imm])
      | VectorShiftRightAccumulate (c, dt, dst, src, imm) ->
         (ctags c, [di dt; oi dst; oi src; oi imm])
      | VStoreRegister (c, src, base, mem) ->
         (ctags c, [oi src; oi base; oi mem])
      | VectorStoreMultipleIncrementAfter (wb, c, rn, rl, mem) ->
         (ctags c, [setb wb; oi rn; oi rl; oi mem])
      | VectorStoreOne (wb, c, sz, rl, rn, mem, rm) ->
         (ctags c, [setb wb; di sz; oi rl; oi rn; oi mem; oi rm])
      | VectorStoreTwo (wb, c, sz, rl, rn, mem, rm) ->
         (ctags c, [setb wb; di sz; oi rl; oi rn; oi mem; oi rm])
      | VectorSubtract (c, dt, dst, src1, src2) ->
         (ctags c, [di dt; oi dst; oi src1; oi src2])
      | VectorTranspose (c, dt, dst, src) -> (ctags c, [di dt; oi dst; oi src])

      | OpInvalid | NotCode _ -> (tags,[])
      | NoOperation c -> (ctags c, [])
      | PermanentlyUndefined (c,op) -> (ctags c, [oi op])
      | NotRecognized (name, dw) -> (tags @ [name; dw#to_hex_string], [])
      | OpcodeUndefined s -> (tags, [bd#index_string s])
      | OpcodeUnpredictable s -> (tags, [bd#index_string s])
      | SupervisorCall (cond,op) -> (tags @ [ ci cond ], [ oi  op ]) in
    arm_opcode_table#add key

  method index_arm_bytestring (s:string):int = arm_bytestring_table#add s

  method write_xml_arm_bytestring ?(tag="ibt") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_arm_bytestring s)

  method write_xml_arm_opcode
           ?(tag="iopc") (node:xml_element_int) (opc:arm_opcode_t) =
    node#setIntAttribute tag (self#index_arm_opcode opc)

  method write_xml (node:xml_element_int) =
    let bnode = xmlElement arm_bytestring_table#get_name in
    begin
      arm_bytestring_table#write_xml bnode;
      node#appendChildren [ bnode ];
      node#appendChildren
        (List.map
           (fun t->
             let tnode = xmlElement t#get_name in
             begin t#write_xml tnode ; tnode end) tables)
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      arm_bytestring_table#read_xml (getc arm_bytestring_table#get_name);
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

end

let arm_dictionary = new arm_dictionary_t

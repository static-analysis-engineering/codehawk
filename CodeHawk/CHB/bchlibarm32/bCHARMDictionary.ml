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
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHStringIndexTable
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
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

  val register_shift_rotate_table = mk_index_table "register-shift-table"
  val arm_memory_offset_table = mk_index_table "arm-memory-offset-table"
  val arm_opkind_table = mk_index_table "arm-opkind-table"
  val arm_operand_table = mk_index_table "arm-operand-table"
  val arm_opcode_table = mk_index_table "arm-opcode-table"
  val arm_bytestring_table = mk_string_index_table "arm-bytestring-table"
  val arm_instr_class_table = mk_index_table "arm-instr-class-table"

  val mutable tables = []

  initializer
    tables <- [
      register_shift_rotate_table;
      arm_memory_offset_table;
      arm_opkind_table;
      arm_operand_table;
      arm_opcode_table;
      arm_instr_class_table
    ]

  method index_arm_instr_class (c:arm_instr_class_t) =
    let tags = [ arm_instr_class_mcts#ts c ] in
    let key = match c with
      | DataProcRegType (cond,op,opx,rn,rd,rs,opy,shift,reg,rm) ->
         (tags, [ cond; op; opx; rn; rd; rs; opy; shift; reg; rm ])
      | DataProcImmType (cond, op, opx, rn, rd, rot, imm) ->
         (tags, [ cond; op; opx; rn; rd; rot; imm ])
      | LoadStoreImmType (cond, p, u, opx, w, opy, rn, rd, imm) ->
         (tags, [ cond; p; u; opx; w; opy; rn; rd; imm ])
      | LoadStoreRegType (cond,p,u,opx,w,opy,rn,rd,shiftimm,shift,opz,rm) ->
         (tags, [ cond; p; u; opx; w; opy; rn; rd; shiftimm; shift; opz; rm ])
      | MediaType (cond,op1,data1,rd,data2,op2,rn) ->
         (tags, [ cond; op1; data1; rd; data2; op2; rn ])
      | BlockDataType (cond,p,u,opx,w,opy,rn,opz,reglist) ->
         (tags, [ cond; p; u; opx; w; opy; rn; opz; reglist ])
      | BranchLinkType (cond,opx,offset) ->
         (tags, [ cond; opx; offset ])
      | SupervisorType (cond,index) ->
         (tags, [ cond; index ])
      | LoadStoreCoprocType (cond,p,u,n,w,op,rn,crd,cpnum,imm) ->
         (tags, [ cond; p; u; n; w; op; rn; crd; cpnum; imm ])
      | CoprocessorType (cond,op,op1,opx,crn,crd,cpnum,op2,opy,crm) ->
         (tags, [ cond; op; op1; opx; crn; crd; cpnum; op2; opy; crm ])
      | UnconditionalType (op1,rn,data,op,datax) ->
         (tags, [ op1; rn; data; op; datax ]) in
    arm_instr_class_table#add key

  method index_register_shift_rotate (rs:register_shift_rotate_t) =
    let tags = [ register_shift_rotate_mcts#ts rs ] in
    let key = match rs with
      | ARMImmSRT (srt,imm) ->
         (tags @ [ shift_rotate_type_mfts#ts srt ],[ imm ])
      | ARMRegSRT (srt,reg) ->
         (tags @ [ shift_rotate_type_mfts#ts srt ; arm_reg_mfts#ts reg ],[]) in
    register_shift_rotate_table#add key

  method index_arm_memory_offset (f:arm_memory_offset_t) =
    let tags = [ arm_memory_offset_mcts#ts f ] in
    let key = match f with
      | ARMImmOffset imm -> (tags,[ imm ])
      | ARMIndexOffset r -> (tags @ [ arm_reg_mfts#ts r ],[])
      | ARMShiftedIndexOffset (r,rs) ->
         (tags @ [ arm_reg_mfts#ts r ],[ self#index_register_shift_rotate rs ]) in
    arm_memory_offset_table#add key

  method index_arm_opkind (k:arm_operand_kind_t) =
    let setb x = if x then 1 else 0 in
    let tags = [ arm_opkind_mcts#ts k ] in
    let key = match k with
      | ARMDMBOption o -> (tags @ [ dmb_option_mfts#ts o], [])
      | ARMReg r -> (tags @ [ arm_reg_mfts#ts r ],[])
      | ARMRegList rl -> (tags @ (List.map arm_reg_mfts#ts rl),[])
      | ARMShiftedReg (r,rs) ->
         (tags @ [ arm_reg_mfts#ts r ], [ self#index_register_shift_rotate rs ])
      | ARMRegBitSequence (r,lsb,widthm1) ->
         (tags @ [ arm_reg_mfts#ts r ],[ lsb; widthm1 ])
      | ARMAbsolute addr -> (tags, [ bd#index_address addr ])
      | ARMMemMultiple (r,n) -> (tags @ [ arm_reg_mfts#ts r ],[n])
      | ARMOffsetAddress (r,offset,isadd,iswback,isindex) ->
         let ioffset = self#index_arm_memory_offset offset in
         (tags @ [ arm_reg_mfts#ts r],
          [ ioffset; setb isadd; setb iswback; setb isindex ])
      | ARMImmediate imm -> (tags @ [ imm#to_numerical#toString ],[]) in
    arm_opkind_table#add key

  method index_arm_operand (op:arm_operand_int) =
    let key = ([ arm_operand_mode_to_string op#get_mode ],
               [ self#index_arm_opkind op#get_kind ]) in
    arm_operand_table#add key

  method index_arm_opcode (opc:arm_opcode_t) =
    let setb x = if x then 1 else 0 in
    let oi = self#index_arm_operand in
    let ci = arm_opcode_cc_mfts#ts in
    let tags = [ get_arm_opcode_name opc ] in
    let ctags c = tags @ [ ci c ] in
    let key = match opc with
      | Add (setflags,cond, rd, rn, imm, tw)
        | AddCarry (setflags, cond, rd, rn, imm, tw) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd; oi rn; oi imm; setb tw ])
      | Adr (cond,rd,addr) ->
         (tags @ [ ci cond ], [ oi rd ; oi addr ])
      | ArithmeticShiftRight (s,c,rd,rn,rm) ->
         (ctags c,[ setb s; oi rd; oi rn; oi rm ])
      | BitwiseNot (setflags,cond,rd,imm) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd ; oi imm ])
      | BitwiseAnd (setflags,cond,rd,rn,imm)
        | BitwiseExclusiveOr (setflags,cond,rd,rn,imm)
        | BitwiseBitClear (setflags,cond,rd,rn,imm)
        | BitwiseOr (setflags,cond,rd,rn,imm) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd; oi rn; oi imm])
      | Branch (c,addr,tw) -> (ctags c, [oi addr; setb tw])
      | BranchExchange (cond,addr)
        | BranchLink (cond,addr)
        | BranchLinkExchange (cond,addr) ->
         (tags @ [ ci cond ], [ oi addr ])
      | ByteReverseWord (c,rd,rm) -> (ctags c,[ oi rd; oi rm ])
      | Compare (c,op1,op2,tw) ->
         (ctags c, [oi op1; oi op2; setb tw])
      | CompareNegative (cond,op1,op2)
        | CountLeadingZeros (cond,op1,op2) ->
         (tags @ [ ci cond ], [ oi op1; oi op2 ])
      | CompareBranchNonzero (op1, op2)
        | CompareBranchZero (op1, op2) -> (tags, [oi op1; oi op2])
      | DataMemoryBarrier (c,op) -> (ctags c,[oi op])
      | IfThen (c, xyz) -> ((ctags c) @ [xyz], [])
      | LoadMultipleDecrementBefore (wb,c,rn,rl,mem)
        | LoadMultipleDecrementAfter (wb,c,rn,rl,mem)
        | LoadMultipleIncrementAfter (wb,c,rn,rl,mem)
        | LoadMultipleIncrementBefore (wb,c,rn,rl,mem) ->
         (ctags c, [ setb wb; oi rn; oi rl; oi mem ])
      | LoadRegister (c,rt,rn,mem,tw) ->
         (ctags c, [ oi rt; oi rn; oi mem; setb tw])
      | LoadRegisterByte (c,rt,rn,mem,tw) ->
         (ctags c, [ oi rt; oi rn; oi mem; setb tw ])
      | LoadRegisterDual (c,rt,rt2,rn,rm,mem) ->
         (ctags c,[ oi rt; oi rt2; oi rn; oi rm; oi mem])
      | LoadRegisterExclusive (c, rt, rn, mem) ->
         (ctags c, [oi rt; oi rn; oi mem])
      | LoadRegisterHalfword (c,rt,rn,rm,mem)
        | LoadRegisterSignedByte (c,rt,rn,rm,mem)
        | LoadRegisterSignedHalfword (c,rt,rn,rm,mem) ->
         (ctags c,[ oi rt; oi rn; oi rm; oi mem])
      | LogicalShiftLeft (s,c,rd,rn,rm,tw) ->
         (ctags c, [ setb s; oi rd; oi rn; oi rm; setb tw])
      | LogicalShiftRight (s,c,rd,rn,rm) ->
         (ctags c, [ setb s; oi rd; oi rn; oi rm])
      | Move (setflags,cond,rd,imm,tw) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd ; oi imm; setb tw ])
      | MoveTop (c,rd,imm) -> (ctags c,[ oi rd; oi imm ])
      | MoveWide (c,rd,imm) -> (ctags c,[ oi rd; oi imm ])
      | Multiply (setflags,cond,rd,rn,rm) ->
         (tags @ [ ci cond ], [ setb setflags; oi rd; oi rn; oi rm])
      | MultiplyAccumulate (setflags,cond,rd,rn,rm,ra) ->
         (tags @ [ ci cond ], [ setb setflags; oi rd; oi rn; oi rm; oi ra ])
      | Pop (c,sp,rl,tw) -> (ctags c, [oi sp; oi rl; setb tw])
      | Push (c,sp,rl,tw) ->  (ctags c, [ oi sp; oi rl; setb tw ])
      | RotateRight (s, c, rd, rn, rm) ->
         (ctags c, [setb s; oi rd; oi rn; oi rm])
      | RotateRightExtend (s,c,rd,rm) ->
         (ctags c,[setb s; oi rd; oi rm])
      | SignedExtendHalfword (c,rd,rm)
        | SignedExtendByte (c,rd,rm) -> (ctags c, [ oi rd; oi rm ])
      | SignedMultiplyLong (s,c,rdlo,rdhi,rn,rm)
        | SignedMultiplyAccumulateLong (s,c,rdlo,rdhi,rn,rm) ->
         (ctags c,[setb s; oi rdlo; oi rdhi; oi rn; oi rm])
      | SingleBitFieldExtract (c,rd,rn) -> (ctags c, [ oi rd; oi rn ])
      | StoreMultipleDecrementBefore (wb,c,rn,rl,mem)
        | StoreMultipleIncrementAfter (wb,c,rn,rl,mem)
        | StoreMultipleIncrementBefore (wb,c,rn,rl,mem) ->
         (ctags c, [ setb wb; oi rn; oi rl; oi mem ])
      | StoreRegister (c,rt,rn,mem,tw) ->
         (ctags c, [oi rt; oi rn; oi mem; setb tw])
        | StoreRegisterByte (c,rt,rn,mem,tw) ->
         (ctags c,[ oi rt; oi rn; oi mem; setb tw])
      | StoreRegisterHalfword (c,rt,rn,rm,mem) ->
         (tags @ [ ci c ], [ oi rt; oi rn; oi rm; oi mem ])
      | StoreRegisterDual (c,rt,rt2,rn,rm,mem) ->
         (ctags c, [ oi rt; oi rt2; oi rn; oi rm; oi mem])
      | StoreRegisterExclusive (c, rd, rt, rn, mem) ->
         (ctags c, [oi rd; oi rt; oi rn; oi mem])
      | Subtract (s,c,dst,src,imm,tw) ->
         (ctags c, [setb s; oi dst; oi src; oi imm; setb tw])
      | SubtractCarry (setflags,cond,dst,src,imm)
        | ReverseSubtract (setflags,cond,dst,src,imm)
        | ReverseSubtractCarry (setflags,cond,dst,src,imm) ->
         (tags @ [ ci cond ], [ setb setflags; oi dst; oi src; oi imm ])
      | Swap (c, rt, rt2, mem) -> (ctags c, [oi rt; oi rt2; oi mem])
      | SwapByte (c, rt, rt2, mem) -> (ctags c, [oi rt; oi rt2; oi mem])
      | Test (cond,src1,src2)
        | TestEquivalence (cond,src1,src2) ->
         (tags @ [ ci cond ], [oi src1; oi src2 ])
      | UnsignedBitFieldExtract (c,rd,rn) -> (ctags c, [ oi rd; oi rn ])
      | UnsignedExtendAddHalfword (c,rd,rn,rm) ->
         (ctags c,[ oi rd; oi rn; oi rm])
      | UnsignedExtendByte (c,rd,rm)
        | UnsignedExtendHalfword (c,rd,rm) -> (ctags c,[ oi rd; oi rm])
      | UnsignedMultiplyLong (s,c,rdlo,rdhi,rn,rm) ->
         (ctags c,[setb s; oi rdlo; oi rdhi; oi rn; oi rm])
      | OpInvalid | NotCode _ -> (tags,[])
      | NoOperation c -> (ctags c, [])
      | PermanentlyUndefined (c,op) -> (ctags c, [oi op])
      | NotRecognized (name, dw) -> (tags @ [name; dw#to_hex_string], [])
      | SupervisorCall (cond,op) -> (tags @ [ ci cond ], [ oi  op ]) in
    arm_opcode_table#add key

  method index_arm_bytestring (s:string):int = arm_bytestring_table#add s

  method write_xml_arm_bytestring ?(tag="ibt") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_arm_bytestring s)

  method write_xml_arm_opcode ?(tag="iopc") (node:xml_element_int) (opc:arm_opcode_t) =
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

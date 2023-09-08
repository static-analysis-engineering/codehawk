(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019  Kestrel Technology LLC
   Copyright (c) 2020-2022  Henny Sipma
   Copyright (c) 2023       Aarno Labs LLC

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
open CHTiming
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHSumTypeSerializer

(* bchlibx86 *)
open BCHLibx86Types
open BCHOperand
open BCHX86OpcodeRecords
open BCHX86Opcodes
open BCHX86SumTypeSerializer


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


class x86dictionary_t:x86dictionary_int =
object (self)

  val opkind_table = mk_index_table "opkind-table"
  val operand_table = mk_index_table "operand-table"
  val opcode_table = mk_index_table "opcode-table"
  val bytestring_table = mk_string_index_table "bytestring-table"
  val opcode_text_table = mk_string_index_table "opcode-text-table"

  val mutable tables = []

  initializer
    tables <- [
      opkind_table;
      operand_table;
      opcode_table
    ]

  method size: int =
    let tablesum = List.fold_left (fun total table -> total + table#size) 0 tables in
    tablesum + bytestring_table#size

  method index_opkind (k:asm_operand_kind_t) =
    let get_optc optc = match optc with Some c -> cpureg_mfts#ts c | _ -> "none" in
    let tags = [ opkind_mcts#ts k ] in
    let key = match k with
      | Flag f -> (tags @ [ eflag_to_string f ],[])
      | Reg r -> (tags @ [ cpureg_mfts#ts r ],[])
      | FpuReg i 
        | ControlReg i 
        | DebugReg i
        | MmReg i 
        | XmmReg i -> (tags, [ i ])
      | SegReg s -> (tags @ [ segment_mfts#ts s ],[])
      | IndReg (c,n) -> (tags @ [ cpureg_mfts#ts c ; n#toString ], [])
      | SegIndReg (s,c,n) ->
         (tags @ [ segment_mfts#ts s ; cpureg_mfts#ts c ; n#toString ],[])
      | ScaledIndReg (optc1,optc2,scale,n) ->
         (tags @ [ get_optc optc1 ; get_optc optc2 ; n#toString ],[scale])
      | DoubleReg (c1,c2) -> (tags @ [cpureg_mfts#ts c1; cpureg_mfts#ts c2], [])
      | Imm imm -> (tags @ [imm#to_numerical#toString], [])
      | Absolute dw -> (tags, [bd#index_address dw])
      | SegAbsolute (s,dw) -> (tags @ [segment_mfts#ts s], [bd#index_address dw])
      | FarAbsolute (s, dw) -> (tags, [s; bd#index_address dw])
      | DummyOp -> (tags,[]) in
    opkind_table#add key

  method index_operand (op:operand_int) =
    let key =
      ([operand_mode_to_string op#get_mode],
       [op#size; self#index_opkind op#get_kind]) in
    operand_table#add key

  method index_opcode (opc:opcode_t) =
    let bi b = if b then 1 else 0 in
    let oi o = self#index_operand o in
    let ooi oo = match oo with Some o -> oi o | _ -> (-1) in
    let si s = bd#index_string s in
    let tags = [ get_opcode_name opc ] in
    let key = match opc with
      | Jcc (cc,op)
        | Setcc (cc,op) -> (tags @ [ condition_code_to_suffix_string cc ],[ oi op ])
      | FlushCacheLine op
        | Ldmxcsr op
        | Stmxcsr op
        | XRestore op
        | XRestoreSupervisor op
        | XSave op
        | XSaveSupervisor op
        | StoreIDTR op
        | StoreGDTR op
        | StoreLDTR op
        | LoadGDTR op
        | LoadIDTR op
        | LoadLDTR op
        | LoadTaskRegister op
        | StoreTaskRegister op
        | InvalidateTLBEntries op
        | TimedPause op
        | Increment op
        | Decrement op
        | RdRandomize op
        | ReadSeed op
        | DirectCall op
        | IndirectCall op
        | DirectJmp op
        | IndirectJmp op
        | DirectLoop  op
        | Fbstp op
        | FRestoreState op
        | FXRestore op
        | Fxch op
        | Jecxz op
        | BSwap op
        | AAD op
        | AAM op
        | OnesComplementNegate op
        | TwosComplementNegate op
        | JumpTableEntry op -> (tags,[ oi op ])
      | Arpl (op1,op2) 
        | ConvertLongToDouble (op1,op2)
        | ConvertWordToDoubleword (op1,op2)
        | BitTestComplement (op1,op2)
        | BitTestReset (op1,op2)
        | BitTestAndSet (op1,op2)
        | BitTest (op1,op2)
        | BitScanForward (op1,op2)
        | BitScanReverse (op1,op2)
        | CountTrailingZeroBits (op1, op2)
        | InvalidatePCID (op1, op2)
        | UndefinedInstruction0 (op1, op2)
        | UndefinedInstruction1 (op1, op2)
        | Add (op1,op2)
        | XAdd (op1,op2)
        | AddCarry (op1,op2)
        | Sub (op1,op2)
        | SubBorrow (op1,op2)
        | Enter (op1,op2)
        | Lea (op1,op2) 
        | Xchg (op1,op2)
        | LogicalAnd (op1,op2)
        | LogicalOr (op1,op2)
        | Test (op1,op2)
        | Cmp (op1,op2)
        | Xor (op1,op2)
        | Sar (op1,op2)
        | Shr (op1,op2)
        | Shl (op1,op2)
        | Ror (op1,op2)
        | Rol (op1,op2)
        | Rcr (op1,op2)
        | Rcl (op1,op2)
        | AESDecrypt (op1,op2)
        | AESDecryptLast (op1,op2)
        | AESEncrypt (op1,op2)
        | AESEncryptLast (op1,op2)
        | AESInvMix (op1,op2) -> (tags, [ oi op1 ; oi op2 ])
      | Shrd (op1,op2,op3)
        | Shld (op1,op2,op3)
        | PackedRoundScalarDouble (op1,op2,op3)
        | PackedAlignRight (op1,op2,op3)
        | LoadFarPointer (op1, op2, op3)
        | AESKeyGenAssist  (op1,op2,op3) -> (tags, [ oi op1 ; oi op2 ; oi op3 ])
      | VPackedAlignRight (op1,op2,op3,op4) ->
         (tags,[ oi op1 ; oi op2 ; oi op3 ; oi op4 ])
      | InterruptReturn b
        | Finit b
        | Fclex b  ->  (tags, [ bi b ])
      | FStore (b1,b2,i,op) -> (tags, [ (bi b1) ; (bi b2) ; i ; oi op ])
      | Fadd (b1,b2,i,op1,op2)
        | Fsub (b1,b2,i,op1,op2)
        | Fsubr (b1,b2,i,op1,op2)
        | Fmul (b1,b2,i,op1,op2)
        | Fdiv (b1,b2,i,op1,op2)
        | Fdivr (b1,b2,i,op1,op2)
        | PackedAdd (b1,b2,i,op1,op2)
        | PackedSubtract (b1,b2,i,op1,op2) ->
         (tags, [ bi b1; bi b2 ; i ; oi op1 ; oi op2 ])
      | VPackedAdd (b1,b2,i,op1,op2,op3) ->
          (tags,[ bi b1 ; bi b2 ; i ; oi op1 ; oi op2 ; oi op3 ])
      | Fcomi (b1,b2,op) -> (tags, [ bi b1 ; bi b2 ])
      | FXmmCompare (b1,b2,op1,op2,op3)
        | PackedCompareString (b1,b2,op1,op2,op3) ->
         (tags, [ bi b1 ; bi b2 ; oi op1 ; oi op2 ; oi op3 ])
      | FLoad (b,i,op) -> (tags, [ (bi b) ; i ; oi op ])
      | Movnt (b,i,op1,op2) -> (tags, [ bi b ; i ; oi op1 ; oi op2 ])
      | FSaveState (b,op) -> (tags, [ bi b ; oi op ])
      | Movdq (b,op1,op2)
        | VMovdq (b,op1,op2) -> (tags, [ bi b ; oi op1 ; oi op2 ])
      | FConvert (b,s1,s2,op1,op2) ->
         (tags, [ bi b; si s1 ; si s2 ; oi op1 ; oi op2 ])
      | MultiByteNop i -> (tags, [ i ])
      | Ret opti
        | BndRet opti -> (tags, match opti with Some i -> [ i ] | _ -> [])
      | Fcom (i1,b,i2,op) -> (tags,[ i1 ; bi b ; i2 ; oi op ]) 
      | Pop (i,op)
        | Push (i,op)
        | Fucom (i,op)
        | Scas (i,op)
        | Lods (i,op)
        | RepIns (i,op)
        | RepOuts (i,op)
        | RepLods (i,op)
        | RepStos (i,op)
        | RepNeStos (i,op)
        | RepEScas (i,op)
        | RepNeScas (i,op)
        | InputStringFromPort (i,op)
        | OutputStringToPort (i,op) -> (tags,[ i ; oi op ])
      | Mov (i,op1,op2)
        | Movdw (i,op1,op2)
        | Movzx (i,op1,op2)
        | Movsx (i,op1,op2)
        | Cmps (i,op1,op2)
        | RepMovs (i,op1,op2)
        | RepNeMovs (i,op1,op2)
        | RepECmps (i,op1,op2)
        | RepNeCmps (i,op1,op2)
        | InputFromPort (i,op1,op2)
        | OutputToPort (i,op1,op2) -> (tags, [ i ; oi op1 ; oi op2 ])
      | IMul (i,op1,op2,op3)
        | Mul (i,op1,op2,op3)
        | PackedExtract (i,op1,op2,op3)
        | PackedInsert (i,op1,op2,op3) ->
         (tags, [ i ; oi op1 ; oi op2 ; oi op3 ])
      | Div (i,op1,op2,op3,op4)
        | IDiv (i,op1,op2,op3,op4)
        | Movs (i,op1,op2,op3,op4)      
        | Stos(i,op1,op2,op3,op4) ->
         (tags, [ i; oi op1 ; oi op2 ; oi op3 ; oi op4 ])      
      | CfNop (i,s) -> (tags, [ i ; si s ])
      | CfJmp (op,i,s) -> (tags, [ oi op ; i ; si s ])
      | MiscOp s
        | XCrypt s
        | InconsistentInstr s -> (tags, [ si s ])
      | FXmmMove (s,b1,b2,op1,op2)
        | FXmmOp (s,b1,b2,op1,op2) ->
         (tags, [ si s ; bi b1 ; bi b2 ; oi op1 ; oi op2 ])
      | FXmmOpEx  (s,b1,b2,op1,op2,op3) ->
         (tags, [ si s ; bi b1 ; bi b2 ; oi op1 ; oi op2 ; oi op3 ])
      | FStoreState (s,b,i,op) -> (tags, [ si s ; bi b ; i ; oi op ])
      | FLoadState (s,i,op) -> (tags, [ si s ; i ; oi op ])
      | PackedOp (s,i,op1,op2)
        | PackedCompare (s,i,op1,op2)
        | PackedShift (s,i,op1,op2)
        | Unpack (s,i,op1,op2) -> (tags, [ si s ; i ; oi op1 ; oi op2 ])
      | VPackedOp (s,i,op1,op2,op3)
        | VPackedShift (s,i,op1,op2,op3) ->
         (tags,[ si s ; i ; oi op1 ; oi op2 ; oi op3 ])
      | Prefetch (s,op) -> (tags, [ si s ; oi op ])
      | PackedMultiply (s,op1,op2)
        | PackedConvert (s,op1,op2) -> (tags, [ si s ; oi op1 ; oi op2 ])
      | PackedShuffle (s,op1,op2,oop3)
        | VPackedShuffle (s,op1,op2,oop3) ->
         (tags, [ si s; oi op1 ; oi op2 ; ooi oop3 ])
      | FLoadConstant (s1,s2)
        | FStackOp (s1,s2) -> (tags, [ si s1 ; si s2 ])
      | _ -> (tags, []) in
    opcode_table#add key

  method index_bytestring (s:string):int = bytestring_table#add s

  method index_opcode_text (s:string):int = opcode_text_table#add s

  method write_xml_opcode ?(tag="iopc") (node:xml_element_int) (opc:opcode_t) =
    node#setIntAttribute tag (self#index_opcode opc)

  method write_xml_bytestring ?(tag="ibt") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_bytestring s)

  method write_xml_opcode_text ?(tag="itxt") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_opcode_text s)

  method write_xml (node:xml_element_int) =
    let _ = pr_timing [STR "saving bytestring table ..."] in
    let s1node = xmlElement bytestring_table#get_name in
    let s2node = xmlElement opcode_text_table#get_name in
    begin
      bytestring_table#write_xml s1node;
      opcode_text_table#write_xml s2node;
      node#appendChildren [s1node; s2node];
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin
               t#write_xml tnode;
               tnode
             end) tables)
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      bytestring_table#read_xml (getc bytestring_table#get_name);
      opcode_text_table#read_xml (getc opcode_text_table#get_name);
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

end

let x86dictionary = new  x86dictionary_t
                  

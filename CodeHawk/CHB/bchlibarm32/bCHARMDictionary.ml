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

  val arm_opkind_table = mk_index_table "arm-opkind-table"
  val arm_operand_table = mk_index_table "arm-operand-table"
  val arm_opcode_table = mk_index_table "arm-opcode-table"
  val arm_bytestring_table = mk_string_index_table "arm-bytestring-table"
  val arm_instr_class_table = mk_index_table "arm-instr-class-table"

  val mutable tables = []

  initializer
    tables <- [
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

  method index_arm_opkind (k:arm_operand_kind_t) =
    let setb x = if x then 1 else 0 in
    let tags = [ arm_opkind_mcts#ts k ] in
    let key = match k with
      | ARMReg r -> (tags @ [ arm_reg_mfts#ts r ],[])
      | ARMRegList rl -> (tags @ (List.map arm_reg_mfts#ts rl),[])
      | ARMShiftedReg (r,shift) ->
         let alist =
           match shift with
           | None -> [ -1 ]
           | Some (SRType_LSL,n) -> [ 0; n ]
           | Some (SRType_LSR,n) -> [ 1; n ]
           | Some (SRType_ASR,n) -> [ 2; n ]
           | Some (SRType_ROR,n) -> [ 3; n ]
           | Some (SRType_RRX,n) -> [ 4; n ] in
         (tags @ [ arm_reg_mfts#ts r ], alist)
      | ARMAbsolute addr -> (tags, [ bd#index_address addr ])
      | ARMOffsetAddress (r,offset,isadd,iswback,isindex) ->
         (tags,[ offset; setb isadd; setb iswback; setb isindex ])
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
    let key = match opc with
      | Add (setflags,cond,rd,rn,imm) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd; oi rn; oi imm ])
      | Adr (cond,rd,addr) ->
         (tags @ [ ci cond ], [ oi rd ; oi addr ])
      | BitwiseNot (setflags,cond,rd,imm) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd ; oi imm ])
      | BitwiseOr (setflags,cond,rd,rn,imm) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd; oi rn; oi imm])
      | Branch (cond,addr)
        | BranchExchange (cond,addr)
        | BranchLink (cond,addr)
        | BranchLinkExchange (cond,addr) ->
         (tags @ [ ci cond ], [ oi addr ])
      | Compare (cond,op1,op2) ->
         (tags @ [ ci cond ], [ oi op1; oi op2 ])
      | LoadRegister (cond,dst,src)
        | LoadRegisterByte (cond,dst,src) ->
         (tags @ [ ci cond ], [ oi dst; oi src ])
      | Mov (setflags,cond,rd,imm)
        | MoveTop (setflags,cond,rd,imm)
        | MoveWide (setflags,cond,rd,imm) ->
         (tags @ [ ci cond ], [ setb setflags ; oi rd ; oi imm ])
      | Pop (cond,rl)
        | Push (cond,rl) ->
         (tags @ [ ci cond ], [ oi rl ])
      | StoreRegister (cond,src,dst) ->
         (tags @ [ ci cond ], [ oi src; oi dst ])
      | StoreRegisterByte (cond,src,dst) ->
         (tags @ [ ci cond ], [ oi src; oi dst ])
      | Subtract (setflags,cond,dst,src,imm)
        | ReverseSubtract (setflags,cond,dst,src,imm) ->
         (tags @ [ ci cond ], [ setb setflags; oi dst; oi src; oi imm ])
      | OpInvalid -> (tags,[])
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

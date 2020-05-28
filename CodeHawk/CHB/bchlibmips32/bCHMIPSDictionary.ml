(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* bchlibmips32 *)
open BCHMIPSTypes
open BCHMIPSOperand
open BCHMIPSOpcodeRecords
open BCHMIPSSumTypeSerializer

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

class mips_dictionary_t:mips_dictionary_int =
object (self)

  val mips_opkind_table = mk_index_table "mips-opkind-table"
  val mips_operand_table = mk_index_table "mips-operand-table"
  val mips_opcode_table = mk_index_table "mips-opcode-table"
  val mips_bytestring_table = mk_string_index_table "mips-bytestring-table"
  val mips_opcode_text_table = mk_string_index_table "mips-opcode-text-table"
  val mips_instr_format_table = mk_index_table "mips-instr-format-table"

  val mutable tables = []

  initializer
    tables <- [
      mips_opkind_table ;
      mips_operand_table ;
      mips_opcode_table ;
      mips_instr_format_table 
    ]

  method index_mips_instr_format (f:mips_instr_format_t) =
    let tags = [ mips_instr_format_mcts#ts f ] in
    let key = match f with
      | RType (opc,rs,rt,rd,shamt,funct) ->
         (tags, [ opc; rs; rt; rd; shamt; funct ])
      | R2Type (opc,rs,rt,rd,shamt,funct) ->
         (tags, [ opc; rs; rt; rd; shamt; funct ])        
      | IType (opc,rs,rt,imm) -> (tags, [ opc; rs; rt; imm ])
      | JType (opc,addr) -> (tags, [ opc; addr ])
      | FPMCType (opc,rs,cc,tf,rd,funct) ->
         (tags, [ opc; rs; cc; tf; rd; funct ])
      | FPRMCType (opc,fmt,cc,tf,fs,fd,funct) ->
         (tags, [ opc; fmt; cc; tf; fs; fd; funct ])
      | FPRType (opc,fmt,ft,fs,fd,funct) ->
         (tags, [ opc; fmt; ft; fs; fd; funct ])
      | FPRIType (opc,sub,rt,fs) ->
         (tags, [ opc; sub; rt; fs ])
      | FPCompareType (opc, fmt, ft, fs, cc, funct) ->
         (tags, [ opc; fmt; ft; fs; cc ; funct ])
      | FPICCType (opc,sub,cc,nd,tf,offset) ->
         (tags, [ opc; sub; cc; nd; tf; offset ])   in
    mips_instr_format_table#add key

  method index_mips_opkind (k:mips_operand_kind_t) =
    let tags =[ mips_opkind_mcts#ts k ] in
    let key =  match k with
      | MIPSReg r -> (tags @ [ mips_reg_mfts#ts r ],[])
      | MIPSSpecialReg r -> (tags @ [ mips_special_reg_mfts#ts r ],[])
      | MIPSFPReg r -> (tags,[ r ])
      | MIPSIndReg (r,offset) -> (tags @ [ mips_reg_mfts#ts r ; offset#toString ],[])
      | MIPSAbsolute a -> (tags,[ bd#index_address a ])
      | MIPSImmediate i -> (tags @ [ i#to_numerical#toString ],[]) in
    mips_opkind_table#add key

  method index_mips_operand (op:mips_operand_int) =
    let key = ([ mips_operand_mode_to_string op#get_mode ],
               [ self#index_mips_opkind op#get_kind ]) in
    mips_operand_table#add key

  method index_mips_opcode (opc:mips_opcode_t) =
    let oi = self#index_mips_operand in
    let tags = [ get_mips_opcode_name opc ] in
    let key = match opc with
      (* no operands *)
      | NoOperation
        | Return
        | Halt
        | NotCode _
        | OpInvalid -> (tags,[])
      (* 1 operand *)
      | Jump op
        | BranchLink op
        | JumpLink op
        | JumpRegister op
        | Branch op
        -> (tags,[ oi op ])
      (* 2 operands *)
      | BranchLTZero (op1,op2)
        | BranchLTZeroLikely (op1,op2)
        | BranchLEZero (op1,op2)
        | BranchLEZeroLikely (op1,op2)
        | BranchGEZero (op1,op2)
        | BranchGEZeroLikely (op1,op2)
        | BranchGTZero (op1,op2)
        | BranchGTZeroLikely (op1,op2)
        | BranchLTZeroLink (op1,op2)
        | BranchGEZeroLink (op1,op2)
        | CountLeadingZeros (op1,op2)
        | LoadImmediate (op1,op2)
        | LoadUpperImmediate (op1,op2)
        | LoadByte (op1,op2)
        | LoadHalfWord (op1,op2)
        | LoadWordLeft (op1,op2)
        | LoadByteUnsigned (op1,op2)
        | LoadHalfWordUnsigned (op1,op2)
        | LoadWord (op1,op2)
        | LoadLinkedWord (op1,op2)
        | LoadWordRight (op1,op2)
        | StoreByte (op1,op2)
        | StoreHalfWord (op1,op2)
        | StoreWordLeft (op1,op2)
        | StoreWord (op1,op2)
        | StoreConditionalWord (op1,op2)
        | StoreWordRight (op1,op2)
        | LoadWordFP (op1,op2)
        | LoadDoublewordToFP (op1,op2)
        | StoreWordFromFP (op1,op2)
        | StoreDoublewordFromFP (op1,op2)
        | JumpLinkRegister (op1,op2)
        | Move (op1,op2)
        | MoveFromHi (op1,op2)
        | MoveToHi (op1,op2)
        | MoveFromLo (op1,op2)
        | MoveToLo (op1,op2)
        | MoveWordFromFP (op1,op2)
        | MoveWordToFP (op1,op2)
        | ControlWordFromFP (op1,op2)
        | ControlWordToFP (op1,op2)
      -> (tags,[ oi op1 ; oi op2 ])
      (* 3 operands *)
      | BranchEqual (op1,op2,op3)
        | BranchEqualLikely (op1,op2,op3)
        | BranchNotEqual (op1,op2,op3)
        | BranchNotEqualLikely (op1,op2,op3)
        | AddImmediate  (op1,op2,op3)
        | AddUpperImmediate (op1,op2,op3)
        | AddImmediateUnsigned (op1,op2,op3)
        | SetLTImmediate (op1,op2,op3)
        | SetLTImmediateUnsigned (op1,op2,op3)
        | AndImmediate (op1,op2,op3)
        | OrImmediate (op1,op2,op3)
        | XorImmediate (op1,op2,op3)
        | ShiftLeftLogical (op1,op2,op3)
        | ShiftRightLogical (op1,op2,op3)
        | ShiftRightArithmetic (op1,op2,op3)
        | ShiftLeftLogicalVariable (op1,op2,op3)
        | ShiftRightLogicalVariable (op1,op2,op3)
        | ShiftRightArithmeticVariable (op1,op2,op3)
        | Add (op1,op2,op3)
        | AddUnsigned (op1,op2,op3)
        | Subtract (op1,op2,op3)
        | SubtractUnsigned (op1,op2,op3)
        | And (op1,op2,op3)
        | Or (op1,op2,op3)
        | Xor (op1,op2,op3)
        | Nor (op1,op2,op3)
        | SetLT (op1,op2,op3)
        | SetLTUnsigned (op1,op2,op3)
        | MovN (op1,op2,op3)
        | MovZ (op1,op2,op3)
        | MultiplyWordToGPR (op1,op2,op3)
        -> (tags,[ oi op1 ; oi op2 ; oi op3 ])
      (* 4 operands *)
      | MultiplyWord (op1,op2,op3,op4)
        | MultiplyAddWord (op1,op2,op3,op4)
        | MultiplyUnsignedWord  (op1,op2,op3,op4)
        | DivideWord (op1,op2,op3,op4)
        | DivideUnsignedWord (op1,op2,op3,op4)
        -> (tags,[ oi op1 ; oi op2 ; oi op3 ; oi op4 ])
      (* cc, 1 operand *)
      | BranchFPFalse (cc,op)
        | BranchFPTrue (cc,op)
        | BranchFPFalseLikely (cc,op)
        | BranchFPTrueLikely (cc,op)
      ->  (tags, [ cc ; oi op ])
      (* cc, 2 operands *)
      | MovF (cc,op1,op2)
        | MovT (cc,op1,op2)
        | TrapIfEqual (cc,op1,op2)
        -> (tags, [ cc; oi op1 ; oi op2 ])
      (* fmt, 2 operands  *)
      | FPSqrtfmt (fmt,op1,op2)
        | FPAbsfmt (fmt,op1,op2)
        | FPMovfmt (fmt,op1,op2)
        | FPNegfmt (fmt,op1,op2)
        | FPRoundLfmt (fmt,op1,op2)
        | FPTruncLfmt (fmt,op1,op2)
        | FPCeilLfmt (fmt,op1,op2)
        | FPFloorLfmt (fmt,op1,op2)
        | FPRoundWfmt (fmt,op1,op2)
        | FPTruncWfmt (fmt,op1,op2)
        | FPCeilWfmt (fmt,op1,op2)
        | FPFloorWfmt (fmt,op1,op2)
        | FPRSqrtfmt (fmt,op1,op2)
        | FPCVTSfmt (fmt,op1,op2)
        | FPCVTDfmt (fmt,op1,op2)
        | FPCVTWfmt (fmt,op1,op2)
        | FPCVTLfmt (fmt,op1,op2)
        | FPCVTSPfmt (fmt,op1,op2)
      -> (tags @ [ mips_fp_format_mfts#ts fmt ],[ oi op1 ; oi op2 ])
      (* fmt,  3 operands *)
      | FPAddfmt (fmt,op1,op2,op3)
        | FPSubfmt (fmt,op1,op2,op3)
        | FPMulfmt (fmt,op1,op2,op3)
        | FPDivfmt (fmt,op1,op2,op3)
        -> (tags @ [ mips_fp_format_mfts#ts fmt ],[ oi op1 ; oi op2 ])
      (* fmt, cc,cond,exc, 2 operands *)
      | FPCompare (fmt,cc,cond,exc,op1,op2)
        -> (tags @ [ mips_fp_format_mfts#ts fmt ], [ cc; cond; exc; oi op1 ; oi op2 ])
    in
    mips_opcode_table#add key

  method index_mips_bytestring (s:string):int = mips_bytestring_table#add s

  method index_mips_opcode_text  (s:string):int = mips_opcode_text_table#add s

  method write_xml_mips_bytestring ?(tag="ibt") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_mips_bytestring s)

  method write_xml_mips_opcode ?(tag="iopc") (node:xml_element_int) (opc:mips_opcode_t) =
    node#setIntAttribute tag (self#index_mips_opcode opc)
      
  method write_xml_mips_opcode_text ?(tag="itxt") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_mips_opcode_text s)

  method write_xml (node:xml_element_int) =
    let bnode = xmlElement mips_bytestring_table#get_name in
    let snode = xmlElement mips_opcode_text_table#get_name in
    begin
      mips_bytestring_table#write_xml bnode ;
      mips_opcode_text_table#write_xml snode ;
      node#appendChildren [ bnode ; snode ] ;
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin t#write_xml tnode ; tnode end) tables)
    end

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    begin
      mips_bytestring_table#read_xml (getc mips_bytestring_table#get_name) ;
      mips_opcode_text_table#read_xml (getc mips_opcode_text_table#get_name) ;
      List.iter (fun t -> t#read_xml (getc t#get_name)) tables
    end

end

let mips_dictionary = new mips_dictionary_t

(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs, LLC

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


class power_dictionary_t: power_dictionary_int =
object (self)

  val pwr_opkind_table = mk_index_table "pwr-opkind-table"
  val pwr_operand_table = mk_index_table "pwr-operand-table"
  val pwr_branch_prediction_table = mk_index_table "pwr_branch_prediction_table"
  val pwr_opcode_table = mk_index_table "pwr-opcode-table"

  val mutable tables = []

  initializer
    tables <- [
      pwr_opkind_table;
      pwr_operand_table;
      pwr_branch_prediction_table;
      pwr_opcode_table
    ]

  method index_pwr_opkind (k: power_operand_kind_t) =
    let tags = [pwr_opkind_mcts#ts k] in
    let key = match k with
      | PowerGPReg i -> (tags, [i])
      | PowerSpecialReg r -> (tags @ [power_spr_mfts#ts r], [])
      | PowerRegisterField r -> (tags @ [power_crf_mfts#ts r], [])
      | PowerConditionRegisterBit i -> (tags, [i])
      | PowerImmediate imm -> (tags @ [imm#to_numerical#toString], [])
      | PowerAbsolute a -> (tags, [bd#index_address a])
      | PowerIndReg (i, off) -> (tags @ [off#toString], [i])
      | PowerIndexedIndReg (i, ix) -> (tags, [i; ix]) in
    pwr_opkind_table#add key

  method index_pwr_operand (op: power_operand_int) =
    let key =
      ([power_operand_mode_to_string op#get_mode],
       [self#index_pwr_opkind op#get_kind]) in
    pwr_operand_table#add key

  method index_pwr_branch_prediction (p: power_branch_prediction_t) =
    let tags = [pwr_branch_prediction_mcts#ts p] in
    let key = match p with
      | BPNone -> (tags, [])
      | BPPlus i -> (tags, [i])
      | BPMinus i -> (tags, [i]) in
    pwr_branch_prediction_table#add key

  method index_pwr_opcode (opc: power_opcode_t) =
    let setb x = if x then 1 else 0 in
    let oi = self#index_pwr_operand in
    let tags = [power_opcode_name opc] in
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
          [setb s; setb op2; setb op16; setb rc; oi rd; oi ra; oi simm; oi cr]) in
    pwr_opcode_table#add key

  method write_xml_pwr_opcode
           ?(tag="iopc") (node: xml_element_int) (opc: power_opcode_t) =
    node#setIntAttribute tag (self#index_pwr_opcode opc)

  method write_xml (node: xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method read_xml (node: xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

end


let power_dictionary: power_dictionary_int = new power_dictionary_t

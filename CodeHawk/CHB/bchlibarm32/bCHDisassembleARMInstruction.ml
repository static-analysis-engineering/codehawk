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

(* bchlib *)
open CHPretty
open CHNumerical

(* chutil *)
open CHLogger
open CHPrettyUtil

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHDoubleword
open BCHImmediate
open BCHLibTypes
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings

(* bchlibarm32 *)
open BCHARMDisassemblyUtils
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMTypes

module B = Big_int_Z

(* commonly used constant values *)
let e7   = 128
let e8   = 256
let e15  = e7 * e8
let e16  = e8 * e8
let e31 = e16 * e15
let e32 = e16 * e16
         

let parse_data_proc_reg_type
      (cond:int)
      (op:int)
      (opx:int)
      (rn:int)
      (rd:int)
      (rs:int)
      (opy:int)
      (shifttype:int)
      (reg:int)
      (rm:int) =
  match op with
  | 3 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     let rnop = arm_register_op (get_arm_reg rn) RD in
     let rdop = arm_register_op (get_arm_reg rd) WR in
     let shiftamount = (rs lsl 1) + opy in
     let rmop = mk_arm_shifted_register_op (get_arm_reg rm) shifttype shiftamount RD in
     ReverseSubtract(setflags,cond,rdop,rnop,rmop)
  | 4 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     if not (rd = 15) then
       let rnop = arm_register_op (get_arm_reg rn) RD in
       let rdop = arm_register_op (get_arm_reg rd) WR in
       let shiftamount = (rs lsl 1) + opy in
       let rmop = mk_arm_shifted_register_op (get_arm_reg rm) shifttype shiftamount RD in
       Add (setflags,cond,rdop,rnop,rmop)
     else
       OpInvalid
  | 9 when (rn = 15) && (rd = 15) && (rs = 15) && (opy = 0) && (reg = 1) ->
     let cond = get_opcode_cc cond in
     let rmop = arm_register_op (get_arm_reg rm) RD in
     if shifttype = 1 then
       BranchLinkExchange (cond,rmop)
     else if shifttype = 0 then
       BranchExchange (cond,rmop)
     else
       OpInvalid
  | 10 when rd = 0 ->
     let cond = get_opcode_cc cond in
     let rnop = arm_register_op (get_arm_reg rn) RD in
     let shiftamount = (rs lsl 1) + opy in
     let rmop = mk_arm_shifted_register_op (get_arm_reg rm) shifttype shiftamount RD in
     Compare (cond,rnop,rmop)
  | 13 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     let rd = arm_register_op (get_arm_reg rd) WR in
     let rm = arm_register_op (get_arm_reg rm) RD in
     Mov (setflags, cond, rd, rm)
  | _ -> OpInvalid

let parse_data_proc_imm_type
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (cond:int)
      (op:int)
      (opx:int)
      (rn:int)
      (rd:int)
      (rotate:int)
      (imm:int) =
  match op with
  | 2 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     let rdop = arm_register_op (get_arm_reg rd) WR in
     (match rn with
      | 15 ->
         OpInvalid
      | _ ->
         let rnop = arm_register_op (get_arm_reg rn) RD in
         let imm32 = make_immediate false 4 (B.big_int_of_int (arm_expand_imm rotate imm)) in
         let immop = arm_immediate_op imm32 in
         Subtract (setflags, cond, rdop, rnop, immop))
  | 3 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     let rdop = arm_register_op (get_arm_reg rd) WR in
     (match rn with
      | 15 ->
         OpInvalid
      | _ ->
         let rnop = arm_register_op (get_arm_reg rn) RD in
         let imm32 = make_immediate false 4 (B.big_int_of_int (arm_expand_imm rotate imm)) in
         let immop = arm_immediate_op imm32 in
         ReverseSubtract (setflags, cond, rdop, rnop, immop))
  | 4 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     let rdop = arm_register_op (get_arm_reg rd) WR in
     (match rn with
      | 15 ->
         let imm32 = arm_expand_imm rotate imm in         
         let tgt = mk_arm_absolute_target_op ch base imm32 WR in
         Adr (cond,rdop,tgt)
      | _ ->
         let rnop = arm_register_op (get_arm_reg rn) RD in
         let imm32 = make_immediate false 4 (B.big_int_of_int (arm_expand_imm rotate imm)) in
         let immop = arm_immediate_op imm32 in         
         Add (setflags, cond, rdop, rnop, immop))
  | 8 ->
     let cond = get_opcode_cc cond in
     if opx = 0 then
       let rdop = arm_register_op (get_arm_reg rd) WR in
       let immval = (rn lsl 12) + (rotate lsl 8) + imm in
       let imm32 = make_immediate false 4 (B.big_int_of_int immval) in
       let immop = arm_immediate_op imm32 in
       MoveWide (false,cond,rdop,immop)
     else
       OpInvalid
  | 10 when rd = 0 && opx = 1 ->
     let cond = get_opcode_cc cond in
     let rn = arm_register_op (get_arm_reg rn) RD in
     let imm32 = make_immediate false 4 (B.big_int_of_int (arm_expand_imm rotate imm)) in
     let immop = arm_immediate_op imm32 in
     Compare (cond,rn,immop)
  | 10 ->
     let cond = get_opcode_cc cond in
     let rdop = arm_register_op (get_arm_reg rd) WR in
     let imm32 = (rn lsl 12) + (rotate lsl 8) + imm in
     let imm32 = make_immediate false 4 (B.big_int_of_int imm32) in
     let immop = arm_immediate_op imm32 in
     MoveTop (false,cond,rdop,immop)
                                         
  | 12 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     let rdop = arm_register_op (get_arm_reg rd) WR in
     (match rn with
      | 15 ->
         OpInvalid
      | _ ->
         let rnop = arm_register_op (get_arm_reg rn) RD in
         let imm32 = make_immediate false 4 (B.big_int_of_int (arm_expand_imm rotate imm)) in
         let immop = arm_immediate_op imm32 in
         BitwiseOr (setflags, cond, rdop, rnop, immop))
  | 13 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     let rd = arm_register_op (get_arm_reg rd) WR in
     let imm32 = make_immediate false 4 (B.big_int_of_int (arm_expand_imm rotate imm)) in
     let immop = arm_immediate_op imm32 in
     Mov (setflags, cond, rd, immop)
  | 15 when rn = 0 ->
     let cond = get_opcode_cc cond in
     let setflags = (opx = 1) in
     let rdop = arm_register_op (get_arm_reg rd) WR in
     let imm32 = make_immediate false 4 (B.big_int_of_int (arm_expand_imm rotate imm)) in
     let immop = arm_immediate_op imm32 in
     BitwiseNot (setflags, cond, rdop, immop)
  | _ -> OpInvalid

let parse_load_store_imm_type
      (cond:int)
      (p:int)
      (u:int)
      (opx:int)
      (w:int)
      (isload:int)
      (rn:int)
      (rd:int)
      (imm:int) =
  let cond = get_opcode_cc cond in
  match rn with
  | 13 ->
     if isload = 1 then
       if p = 0 && u = 1 && opx = 0 && w = 0 && imm = 4 then
         let rl = arm_register_list_op [ (get_arm_reg rd) ] WR in
         Pop (cond, rl)
       else
         OpInvalid
     else
       if p = 1 && u = 0 && opx = 0 && w = 1 && imm = 4 then
         let rl = arm_register_list_op [ (get_arm_reg rd) ] RD in
         Push (cond, rl)
       else
         let srcop = arm_register_op (get_arm_reg rd) RD in
         let isadd = (u = 1) in
         let iswback = (p = 0) || (w = 1) in
         let isindex = (p = 1) in
         let dstop = mk_arm_offset_address_op (get_arm_reg rn) imm isadd iswback isindex WR in
         if opx = 0 then
           StoreRegister (cond,srcop,dstop)
         else
           StoreRegisterByte (cond,srcop,dstop)
  | _ ->
     if isload = 1 then
       if not (p = 0 && w = 1) then
         let rtop = arm_register_op (get_arm_reg rd) WR in
         let isadd = (u = 1) in
         let iswback = (p = 0) || (w = 1) in
         let isindex = (p = 1) in
         let srcop = mk_arm_offset_address_op (get_arm_reg rn) imm isadd iswback isindex RD in
         if opx = 0 then
           LoadRegister (cond,rtop,srcop)
         else
           LoadRegisterByte (cond,rtop,srcop)
       else         
         OpInvalid
     else
       let srcop = arm_register_op (get_arm_reg rd) RD in
       let isadd = (u = 1) in
       let iswback = (p = 0) || (w = 1) in
       let isindex = (p = 1) in
       let dstop = mk_arm_offset_address_op (get_arm_reg rn) imm isadd iswback isindex WR in
       if opx = 0 then
         StoreRegister (cond,srcop,dstop)
       else
         StoreRegisterByte (cond,srcop,dstop)
  
let parse_load_store_reg_type
      (cond:int)
      (p:int)
      (u:int)
      (opx:int)
      (w:int)
      (opy:int)
      (rn:int)
      (rd:int)
      (shiftimm:int)
      (shift:int)
      (opz:int)
      (rm:int) = OpInvalid

let parse_block_data_type
      (cond:int)
      (p:int)
      (u:int)
      (opx:int)
      (w:int)
      (isload:int)
      (rn:int)
      (opz:int)
      (reglist:int) =
  match rn with
  | 13 ->
     let cond = get_opcode_cc cond in
     if isload = 0 then
       if (p = 1) && (u = 0) && (opx = 0) && (w = 1) then
         let rl = get_reglist_from_int 16 reglist in
         let rlop = arm_register_list_op rl RD in
         Push (cond, rlop)
       else
         OpInvalid
     else
       if (p = 0) && (u = 1) && (opx = 0) && (w = 1) then
         let rl = get_reglist_from_int 16 reglist in
         let rl = if opz = 1 then rl @ [ ARPC ] else rl in
         let rlop = arm_register_list_op rl WR in
         Pop (cond, rlop)
       else
         OpInvalid
  | _ ->
     OpInvalid
     

let parse_branch_link_type
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (cond:int)
      (opx:int)
      (offset:int) =
  let cond = get_opcode_cc cond in
  let imm32 = sign_extend 32 26 (offset lsl 2) in
  let imm32 = if imm32 >= e31 then imm32 - e32 else imm32 in
  let tgt = (base#add_int (ch#pos + 4))#add_int imm32 in
  let tgtop = arm_absolute_op tgt RD in
  if opx = 0 then
    Branch (cond,tgtop)
  else
    BranchLink (cond,tgtop)

let parse_opcode
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (instrbytes:doubleword_int):arm_opcode_t =
  let p = numerical_to_doubleword (mkNumerical ch#pos) in
  let addr = (base#add p)#add_int (-4) in
  let instr = decompose_arm_instr instrbytes in
  let opcode =
    match instr with
    | DataProcRegType (cond,op,opx,rn,rd,rs,opy,shift,reg,rm) ->
       parse_data_proc_reg_type cond op opx rn rd rs opy shift reg rm
    | DataProcImmType (cond,op,opx,rn,rd,rotate,imm) ->
       parse_data_proc_imm_type ch base cond op opx rn rd rotate imm
    | LoadStoreImmType (cond,p,u,opx,w,opy,rn,rd,imm) ->
       parse_load_store_imm_type cond p u opx w opy rn rd imm
    | LoadStoreRegType (cond,p,u,opx,w,opy,rn,rd,shiftimm,shift,opz,rm) ->
       parse_load_store_reg_type cond p u opx w opy rn rd shiftimm shift opz rm
    | BlockDataType (cond,p,u,opx,w,opy,rn,opz,reglist) ->
       parse_block_data_type cond p u opx w opy rn opz reglist
    | BranchLinkType (cond,opx,offset) ->
       parse_branch_link_type ch base cond opx offset
    | _ -> OpInvalid in
  let pinstrclass =
    if system_settings#is_verbose
       && (match opcode with OpInvalid -> true | _ -> false) then
      LBLOCK [ STR " ("; STR (arm_instr_class_to_string instr); STR ")" ]
    else
      STR "" in
  begin
    pr_debug [ addr#toPretty ; STR "  " ; STR (arm_opcode_to_string opcode) ;
               pinstrclass ; NL ];
    opcode
  end

let disassemble_arm_instruction
      (ch:pushback_stream_int) (base:doubleword_int) (instrbytes:doubleword_int) =
  try
    parse_opcode ch base instrbytes
  with
  | IO.No_more_input ->
     let address = base#add_int ch#pos in
     begin
       ch_error_log#add
         "no more input"
         (LBLOCK [ STR "No more input at position " ; address#toPretty ; STR " (" ;
                   INT ch#pos ; STR ")" ]) ;
       raise IO.No_more_input
     end

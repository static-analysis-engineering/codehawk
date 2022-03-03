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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHDoubleword
open BCHImmediate
open BCHLibTypes

(* bchlibpower32 *)
open BCHPowerOperand
open BCHPowerPseudocode
open BCHPowerTypes


let stri = string_of_int


let parse_se_C_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let opc = b 12 15 in

  match opc with

  (* 0000000000000100    se_blr *)
  | 4 ->
     let tgt = power_special_register_op ~reg:PowerLR ~mode:RD in
     BranchLinkRegister (VLE16, tgt)

  (* 0000000000000101    se_blrl *)
  | 5 ->
     let tgt = power_special_register_op ~reg:PowerLR ~mode:RW in
     BranchLinkRegisterLink (VLE16, tgt)

  (* 0000000000000110    se_bctr *)
  | 6 ->
     let tgt = power_special_register_op ~reg:PowerCTR ~mode:RD in
     BranchCountRegister (VLE16, tgt)

  (* 0000000000000111    se_bctrl *)
  | 7 ->
     let tgt = power_special_register_op ~reg:PowerCTR ~mode:RD in
     BranchCountRegisterLink (VLE16, tgt)

  | _ ->     
     NotRecognized("000-C:" ^ (string_of_int opc), instr)


let parse_se_R_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let opc = b 8 11 in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  match opc with

  (* 000000000010<rx>   se_not *)
  | 2 ->
     (* se_not rX *)
     NotRegister (VLE16, rx ~mode:RW)

  (* 000000001000<rx>   se_mflr *)    
  | 8 ->
     let lr = power_special_register_op ~reg:PowerLR in     
     (* se_mflr rX *)
     MoveFromLinkRegister (VLE16, rx ~mode:WR, lr ~mode:RD)

  (* 000000001001<rx>   se_mtlr *)
  | 9 ->
     let lr = power_special_register_op ~reg:PowerLR in
     (* se_mtrl rX *)
     MoveToLinkRegister (VLE16, lr ~mode:WR, rx ~mode:WR)

  (* 000000001011<rx>   se_mtctr *)
  | 11 ->
     let ctr = power_special_register_op ~reg:PowerCTR in     
     (* se_mtctr rX *)
     MoveToCountRegister (VLE16, ctr ~mode:WR, rx ~mode:RD)

  (* 000000001110<rx>   se_extzh *)
  | 14 ->
     (* se_extzh rX *)
     ExtendZeroHalfword (VLE16, rx ~mode:RW)
  
  | _ ->
     NotRecognized("00-R:" ^ (string_of_int opc), instr)


let parse_se_RR_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  let ry = power_gp_register_op ~index:(rindex (b 8 11)) in
  let opc = b 4 7 in
  match opc with
    
  (* 0000001<ry><rx>    se_mr *)
  | 1 ->
     (* se_mr rX, rY *)
     MoveRegister (VLE16, rx ~mode:WR, ry ~mode:RD)

  (* 00000011<ay><rx>   se_mfar *)
  | 3 ->
     (* se_mfar rx, arY *)
     let ary = power_gp_register_op ~index:(arindex (b 8 11)) in
     MoveFromAlternateRegister (VLE16, rx ~mode:WR, ary ~mode:RD)

  (* 00000110<ry><rx>   se_sub *)
  | 6 ->
     (* se_sub rX, rY *)
     Subtract (VLE16, rx ~mode:WR, ry ~mode:RD)

  (* 00001101<ry><rx>   se_cmpl *)
  | 13 ->
     (* se_cmpl rX, rY *)
     CompareLogical (VLE16, rx ~mode:RD, ry ~mode:RD)

  | _ ->
     NotRecognized("0-RR:" ^ (string_of_int opc), instr)


let parse_se_IM_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let ui5 = b 7 11 in
  let oim5 = ui5 + 1 in
  let immop =
    power_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical oim5) in
  let ui5op =
    power_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical ui5) in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  let opc = b 4 6 in
  match opc with

  (* 0010000<oi5><rx>   se_addi *)
  | 0 ->
     (* se_addi rX, OIMM *)
     AddImmediate (VLE16, false, false, rx ~mode:WR, rx ~mode:RD, immop)

  (* 0010001<oi5><rx>   se_cmpli *)
  | 1 ->
     (* se_cmpli rX, OIMM *)
     CompareLogicalImmediate (VLE16, rx ~mode:RD, immop)

  (* 0010101<ui5><rx>   se_cmpi *)    
  | 5 ->
     (* se_cmpi rX, UI5 *)
     CompareImmediate (VLE16, rx ~mode:RD, ui5op)

  (* 0010110<ui5><rx>   se_bmaski *)
  | 6 ->
     (* se_bmaski rX, UI5 *)
     BitMaskGenerateImmediate (VLE16, rx~mode:WR, ui5op)

  | _ ->
     NotRecognized("2-IM:" ^ (string_of_int opc), instr)


let parse_se_RR_IM7_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let bv = instr#get_reverse_bitval 16 in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  let ry = power_gp_register_op ~index:(rindex (b 8 11)) in

  if (bv 4) = 1 then
     let imm7 = b 5 11 in
     let immop =
       power_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical imm7) in
     LoadImmediate (VLE16, false, rx ~mode:WR, immop)

  else
    let opc = b 5 7 in
    NotRecognized("4-RR:" ^ (string_of_int opc), instr)
    
     
let parse_se_IM5_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let imm5 = b 7 11 in
  let immop =
    power_immediate_op ~signed:false ~size: 4 ~imm:(mkNumerical imm5) in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  let opc = b 4 6 in
  match opc with
  (* 0110001<ui5><rx>    se_bgeni *)
  | 1 ->
     (* se_bgeni rX, UI5 *)
     BitGenerateImmediate (VLE16, rx ~mode:WR, immop)

  (* 0110010<ui5><rx>   se_bseti *)
  | 2 ->
     (* se_bseti rX, UI5 *)
     BitSetImmediate (VLE16, rx ~mode:WR, immop)

  (* 0110101<ui5><rx> *)
  | 5 ->
     (* se_srawi rx, UI5 *)
     ShiftRightAlgebraicWordImmediate (VLE16, rx ~mode:WR, rx ~mode:RD, immop)

  (* 0110110<ui5><rx> *)
  | 6 ->
     (* se_slwi rX, UI5 *)
     ShiftLeftWordImmediate (VLE16, rx ~mode:WR, rx ~mode:RD, immop)

  | _ ->
     NotRecognized("6-IM5:" ^ (string_of_int opc), instr)


let parse_se_branch
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let opc = b 4 7 in
  NotRecognized("14-BR:" ^ (string_of_int opc), instr)


let parse_se_SD4_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let sd4 w = mkNumerical (w * (b 4 7)) in
  let rz = power_gp_register_op ~index:(rindex (b 8 11)) in
  let rx w =
    power_indirect_register_op ~index:(rindex (b 12 15)) ~offset:(sd4 w) in
  let opc = b 0 3 in
  match opc with

  (* 1010<sd><rz><rx>   se_lhz *)
  | 10 ->
     (* se_lhz rZ, SD4(rX) *)
     LoadHalfwordZero (VLE16, rz ~mode:WR, rx 2 ~mode:RD)

  (* 1011<sd><rz><rx>   se_sth *)
  | 11 ->
     (* se_sth rZ, SD4(rX) *)
     StoreHalfword (VLE16, rz ~mode:RD, rx 2 ~mode:WR)

  (* 1100<sd><rz><rx>   se_lwz *)
  | 12 ->
     (* se_lwz rZ, SD4(rX) *)
     LoadWordZero (VLE16, rz ~mode:WR, rx 4 ~mode:RD)

  (* 1101<sd><rz><rx>   se_stw *)
  | 13 ->
     (* se_stw rZ, SD4(rX) *)
     StoreWord (VLE16, rz ~mode:RD, rx 4 ~mode:WR)

  | _ ->
     NotRecognized("SD4:" ^ (string_of_int opc), instr)

     
let parse_se_instruction
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in

  if (b 0 11) = 0 then
    parse_se_C_form ch base iaddr instr

  else if (b 0 7) = 0 then
    parse_se_R_form ch base iaddr instr

  else
    match (b 0 3) with
    | 0 -> parse_se_RR_form ch base iaddr instr
    | 2 -> parse_se_IM_form ch base iaddr instr
    | 4 -> parse_se_RR_IM7_form ch base iaddr instr
    | 6 -> parse_se_IM5_form ch base iaddr instr
    | 14 -> parse_se_branch ch base iaddr instr
    | _ -> parse_se_SD4_form ch base iaddr instr


let parse_vle_opcode
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instrbytes: int): power_opcode_t =
  let prefix = instrbytes lsr 12 in
  if prefix = 1 || prefix = 3 || prefix = 5 || prefix = 7 then
    let sndhalfword = ch#read_ui16 in
    let instr32 = (instrbytes lsl 16) + sndhalfword in
    let instr32 = int_to_doubleword instr32 in
    NotRecognized (instr32#to_hex_string, instr32)
  else
    let instr16 = int_to_doubleword instrbytes in
    parse_se_instruction ch base iaddr instr16
  

let disassemble_vle_instruction
      (ch: pushback_stream_int) (base: doubleword_int) (instrbytes: int) =
  let iaddr = base#add_int (ch#pos - 2) in
  try
    parse_vle_opcode ch base iaddr instrbytes
  with
  | BCH_failure p ->
     begin
       ch_error_log#add
         "disassembly - vle"
         (LBLOCK [
              STR "Error in disassembling vle: ";
              iaddr#toPretty;
              STR ": ";
              p]);
       raise (BCH_failure p)
     end

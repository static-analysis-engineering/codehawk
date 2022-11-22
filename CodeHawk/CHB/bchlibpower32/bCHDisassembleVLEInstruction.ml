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

  (* < 0>< 0>< 0>< 1>    se_isync *)
  | 1 ->
     InstructionSynchronize (VLE16)

  (* < 0>< 0>< 0>< 4>    se_blr *)
  | 4 ->
     let tgt = power_special_register_op ~reg:PowerLR ~mode:RD in
     BranchLinkRegister (VLE16, tgt)

  (* < 0>< 0>< 0>< 5>    se_blrl *)
  | 5 ->
     let tgt = power_special_register_op ~reg:PowerLR ~mode:RW in
     BranchLinkRegisterLink (VLE16, tgt)

  (* < 0>< 0>< 0>< 6>    se_bctr *)
  | 6 ->
     let tgt = power_special_register_op ~reg:PowerCTR ~mode:RD in
     BranchCountRegister (VLE16, tgt)

  (* < 0>< 0>< 0>< 7>    se_bctrl *)
  | 7 ->
     let tgt = power_special_register_op ~reg:PowerCTR ~mode:RD in
     BranchCountRegisterLink (VLE16, tgt)

  (* < 0>< 0>< 0>< 8>    se_rfi *)
  | 8 ->
     let reg = power_special_register_op ~reg:PowerMSR ~mode:WR in
     ReturnFromInterrupt (VLE16, reg)

  | _ ->     
     NotRecognized("000-C:" ^ (string_of_int opc), instr)


(** R-form: (16-bit Monadic Instructions)

    0..5: OPCD (primary opcode)
    6..11: XO (extended opcode)
    12..15: RX (GPR in the ranges GPR0-GPR7 or GPR24-GPR31, src or dst)
*)
let parse_se_R_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let opc = b 8 11 in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  match opc with

  (* < 0>< 0>< 2><rx>   se_not *)
  | 2 ->
     (* se_not rX *)
     NotRegister (VLE16, rx ~mode:RW)

  (* < 0>< 0>< 8><rx>   se_mflr *)
  | 8 ->
     let lr = power_special_register_op ~reg:PowerLR in     
     (* se_mflr rX *)
     MoveFromLinkRegister (VLE16, rx ~mode:WR, lr ~mode:RD)

  (* < 0>< 0>< 9><rx>   se_mtlr *)
  | 9 ->
     let lr = power_special_register_op ~reg:PowerLR in
     (* se_mtrl rX *)
     MoveToLinkRegister (VLE16, lr ~mode:WR, rx ~mode:WR)

  (* < 0>< 0><11><rx>   se_mtctr *)
  | 11 ->
     let ctr = power_special_register_op ~reg:PowerCTR in     
     (* se_mtctr rX *)
     MoveToCountRegister (VLE16, ctr ~mode:WR, rx ~mode:RD)

  (* < 0>< 0><14><rx>   se_extzh *)
  | 14 ->
     (* se_extzh rX *)
     ExtendZeroHalfword (VLE16, rx ~mode:RW)
  
  | _ ->
     NotRecognized("00-R:" ^ (string_of_int opc), instr)


(** RR Form (16-bit Dyadic Instructions)

    0..5: OPCD (Primary Opcode)
    6..7: XO/RC  (Extended Opcode field/Record Bit (Do (not) set CR))
    8..11: RY/ARY  (GPR in the ranges GPR0-GPR7 or GPR24-GPR31 (src)
                     /alternate GPR in the range GPR8-GPR23 as src)
    12..15: RX/ARX  (GPR in the ranges GPR0-GPR7 or GPR24-GPR31 (src or dst)
                     /alternate GPR in the range GPR8-GPR23 as dst)
 *)
let parse_se_0RR_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  let ry = power_gp_register_op ~index:(rindex (b 8 11)) in
  let opc = b 4 7 in
  match opc with
    
  (* < 0>< 1><ry><rx>    se_mr *)
  | 1 ->
     (* se_mr rX, rY *)
     MoveRegister (VLE16, rx ~mode:WR, ry ~mode:RD)

  (* < 0>< 3><ay><rx>   se_mfar *)
  | 3 ->
     (* se_mfar rx, arY *)
     let ary = power_gp_register_op ~index:(arindex (b 8 11)) in
     MoveFromAlternateRegister (VLE16, rx ~mode:WR, ary ~mode:RD)

  (* < 0>< 6><ry><rx>   se_sub *)
  | 6 ->
     (* se_sub rX, rY *)
     Subtract (VLE16, rx ~mode:WR, ry ~mode:RD)

  (* < 0><13><ry><rx>   se_cmpl *)
  | 13 ->
     (* se_cmpl rX, rY *)
     CompareLogical (VLE16, rx ~mode:RD, ry ~mode:RD)

  | _ ->
     NotRecognized("0-RR:" ^ (string_of_int opc), instr)


(** IM5 Form (16-bit register + immediate instructions), and
    OIM5 Form (16-bit register + offset immediate instructions)

    0..5: OPCD (primary opcode)
    6: XO  (extended opcode)
    7..11: (IM5): UI5 (immediate used to specify a 5-bit unsigned value)
           (OIM5): OIM5 (offset immediate in the range 1..32, encoded as 0..31)
    12..15: RX (GPR in the ranges GPR0-GPR7, or GPR24-GPR31, as src or dst)
 *)
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

  (* < 2><0><oi5><rx>   se_addi *)
  | 0 ->
     (* se_addi rX, OIMM *)
     AddImmediate (VLE16, false, false, rx ~mode:WR, rx ~mode:RD, immop)

  (* < 2><1><oi5><rx>   se_cmpli *)
  | 1 ->
     (* se_cmpli rX, OIMM *)
     CompareLogicalImmediate (VLE16, rx ~mode:RD, immop)

  (* < 2><5><ui5><rx>   se_cmpi *)
  | 5 ->
     (* se_cmpi rX, UI5 *)
     CompareImmediate (VLE16, rx ~mode:RD, ui5op)

  (* < 2><6><ui5><rx>   se_bmaski *)
  | 6 ->
     (* se_bmaski rX, UI5 *)
     BitMaskGenerateImmediate (VLE16, rx~mode:WR, ui5op)

  | _ ->
     NotRecognized("2-IM:" ^ (string_of_int opc), instr)


let parse_se_IM7_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  let imm7 = b 5 11 in
  let immop =
    power_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical imm7) in
  LoadImmediate (VLE16, false, rx ~mode:WR, immop)


let parse_se_4RR_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let rx = power_gp_register_op ~index:(rindex (b 12 15)) in
  let ry = power_gp_register_op ~index:(rindex (b 8 11)) in
  let opc = b 5 7 in

  match opc with

  (* < 4>0<4><ry><rx>    se_or rX, rY *)
  | 4 ->
     Or (VLE16, rx ~mode:WR, ry ~mode:RD)

  (* < 4>0<6><ry><rx>    se_and rX, rY *)
  | 6 ->
     And (VLE16, rx ~mode:WR, ry ~mode:RD)
     
  | _ ->
     NotRecognized("4-RR:" ^ (string_of_int opc), instr)


(** IM5 Form (16-bit register + immediate instructions)

    0..5: OPCD (primary opcode)
    6: XO  (extended opcode)
    7..11: (IM5): UI5 (immediate used to specify a 5-bit unsigned value)
    12..15: RX (GPR in the ranges GPR0-GPR7, or GPR24-GPR31, as src or dst)
 *)
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
  (* < 6><1><ui5><rx>    se_bgeni *)
  | 1 ->
     (* se_bgeni rX, UI5 *)
     BitGenerateImmediate (VLE16, rx ~mode:WR, immop)

  (* < 6><2><ui5><rx>   se_bseti *)
  | 2 ->
     (* se_bseti rX, UI5 *)
     BitSetImmediate (VLE16, rx ~mode:WR, immop)

  (* < 6><5><ui5><rx> *)
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


(** SD4 Form (16-bit Load/Store Instructions)
    1..3: OPCD (primary opcode)
    4..7: SD4 (4-bit unsigned immediate value zero-extended to 64 bits, shifted
          left according to the size of the operation, and added to the base
          register to form a 64-bit effective address. For byte operations no
          shift is performed. For halfword operations, the immediate is shifted
          left one bit. For word operations, the immediate is shifted left two
          bits.
    8..11: RZ (specifies a GPR in the range GPR0-GPR7 or GPR24-GPR31, as src
           or dst for load/store data).
    12..15: RX (specifies a GPR in the range GPR0-GPR7 or GPR24-GPR31, as src
            or dst).
 *)
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

  (* <10><sd><rz><rx>   se_lhz *)
  | 10 ->
     (* se_lhz rZ, SD4(rX) *)
     LoadHalfwordZero (VLE16, rz ~mode:WR, rx 2 ~mode:RD)

  (* <11><sd><rz><rx>   se_sth *)
  | 11 ->
     (* se_sth rZ, SD4(rX) *)
     StoreHalfword (VLE16, rz ~mode:RD, rx 2 ~mode:WR)

  (* <12><sd><rz><rx>   se_lwz *)
  | 12 ->
     (* se_lwz rZ, SD4(rX) *)
     LoadWordZero (VLE16, rz ~mode:WR, rx 4 ~mode:RD)

  (* <13><sd><rz><rx>   se_stw *)
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
    | 0 -> parse_se_0RR_form ch base iaddr instr
    | 2 -> parse_se_IM_form ch base iaddr instr
    | 4 when (b 4 4) = 1 -> parse_se_IM7_form ch base iaddr instr
    | 4 -> parse_se_4RR_form ch base iaddr instr
    | 6 -> parse_se_IM5_form ch base iaddr instr
    | 14 -> parse_se_branch ch base iaddr instr
    | _ -> parse_se_SD4_form ch base iaddr instr


let parse_e_D8_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  let opc1 = b 16 19 in
  let opc2 = b 20 23 in
  let ra_index = b 11 15 in
  let d8 = d8_sign_extend (b 24 31) in
  let mk_ea mnem mode =
    if ra_index = 0 then
      if d8 <= 0 then
        raise
          (BCH_failure
             (LBLOCK [
                  STR "Negative effective address in ";
                  STR mnem;
                  STR ": ";
                  INT d8]))
      else
        power_absolute_op (int_to_doubleword d8) mode
    else
      power_indirect_register_op
        ~index:ra_index
        ~offset:(mkNumerical d8)
        ~mode:mode in

  match (opc1, opc2) with

  (* < 1>10< rd>< ra>< 0>< 0><--d8-->    e_lbzu *)
  | (0, 0) ->
     let rd = power_gp_register_op ~index:(b 6 10) in
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_lbzu" RD in
     LoadByteZeroUpdate (VLE32, rd WR, ra RW, ea)

  (* < 1>10< rd>< ra>< 0>< 2><--d8-->    e_lwzu *)
  | (0, 2) ->
     let rd = power_gp_register_op ~index:(b 6 10) in
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_lwzu" RD in
     LoadWordZeroUpdate (VLE32, rd WR, ra RW, ea)

  (* < 1>10< rs>< ra>< 0>< 4><--d8-->    e_stbu *)
  | (0, 4) ->
     let rs = power_gp_register_op ~index:(b 6 10) in
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_stbu" WR in
     StoreByteUpdate (VLE32, rs RD, ra RW, ea)

  (* < 1>10< rs>< ra>< 0>< 6><--d8-->    e_stwu *)
  | (0, 6) ->
     let rs = power_gp_register_op ~index:(b 6 10) in
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_stwu" WR in
     StoreWordUpdate (VLE32, rs RD, ra RW, ea)

  (* < 1>10< rd>< ra>< 0>< 8><--d8-->    e_lmw *)
  | (0, 8) ->
     let rd = power_gp_register_op ~index:(b 6 10) in
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_lmw" RD in
     LoadMultipleWord (VLE32, rd WR, ra RD, ea)

  (* < 1>10< rs>< ra>< 0>< 9><--d8-->    e_stmw *)
  | (0, 9) ->
     let rs = power_gp_register_op ~index:(b 6 10) in
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_stmw" WR in
     StoreMultipleWord (VLE32, rs RD, ra RD, ea)

  (* < 1>10<  0>< ra>< 1>< 0><--d8-->    e_lmvgprw *)
  | (1, 0) when (b 6 10) = 0 ->
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_lmvgprw" WR in
     LoadMultipleVolatileGPRWord (VLE32, ra RD, ea)

  (* < 1>10<  1>< ra>< 1>< 0><--d8-->    e_lmvsprw *)
  | (1, 0) when (b 6 10) = 1 ->
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_lmvsprw" WR in
     let cr = power_special_register_op ~reg:PowerCR in
     let lr = power_special_register_op ~reg:PowerLR in
     let ctr = power_special_register_op ~reg:PowerCTR in
     let xer = power_special_register_op ~reg:PowerXER in
     LoadMultipleVolatileSPRWord (
         VLE32, ra RD, cr WR, lr WR, ctr WR, xer WR, ea)

  (* < 1>10<  4>< ra>< 1>< 0><--d8-->    e_lmvsrrw *)
  | (1, 0) when (b 6 10) = 4 ->
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_lmvsrrw" WR in
     let srr0 = power_special_register_op ~reg:PowerSRR0 in
     let srr1 = power_special_register_op ~reg:PowerSRR1 in
     LoadMultipleVolatileSRRWord (VLE32, ra RD, srr0 RD, srr1 RD, ea)

  (* < 1>10<  0>< ra>< 1>< 1><--d8-->    e_stmvgprw *)
  | (1, 1) when (b 6 10) = 0 ->
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_stmvgprw" WR in
     StoreMultipleVolatileGPRWord (VLE32, ra RD, ea)

  (* < 1>10<  1>< ra>< 1>< 1><--d8-->    e_stmvsprw *)
  | (1, 1) when (b 6 10) = 1 ->
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_stmvsprw" WR in
     let cr = power_special_register_op ~reg:PowerCR in
     let lr = power_special_register_op ~reg:PowerLR in
     let ctr = power_special_register_op ~reg:PowerCTR in
     let xer = power_special_register_op ~reg:PowerXER in
     StoreMultipleVolatileSPRWord (
         VLE32, ra RD, cr RD, lr RD, ctr RD, xer RD, ea)

  (* < 1>10<  4>< ra>< 1>< 1><--d8-->    e_stmvsrrw *)
  | (1, 1) when (b 6 10) = 4 ->
     let ra = power_gp_register_op ~index:ra_index in
     let ea = mk_ea "e_stmvsrrw" WR in
     let srr0 = power_special_register_op ~reg:PowerSRR0 in
     let srr1 = power_special_register_op ~reg:PowerSRR1 in
     StoreMultipleVolatileSRRWord (VLE32, ra RD, srr0 RD, srr1 RD, ea)

  | _ ->
     NotRecognized (
         "18-D8:" ^ (string_of_int opc1) ^ "_" ^ (string_of_int opc2), instr)


let parse_e_SCI8_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  let opc = b 16 20 in

  match opc with
  | _ ->
     NotRecognized ("18-SCI8:" ^ (string_of_int opc), instr)


let parse_e_D_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int)
      (prefix: int) =

  NotRecognized ("D:" ^ (string_of_int prefix), instr)


let parse_e_misc_form
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  let sndbyte = b 4 7 in
  let byten1 = b 28 31 in
  let byten2 = b 24 27 in

  NotRecognized (
      "7-misc:"
      ^ (string_of_int sndbyte)
      ^ "_"
      ^ (string_of_int byten2)
      ^ "_"
      ^ (string_of_int byten1),
      instr)


let parse_e_instruction
      (ch: pushback_stream_int)
      (base: doubleword_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int)
      (prefix: int) =
  let b = instr#get_reverse_segval 32 in

  (* D8 / SCI8 / D form *)
  match prefix with
  | 1 ->
     (match b 4 5 with
      | 2 ->
         (match b 16 16 with
          | 0 -> parse_e_D8_form ch base iaddr instr
          | 1 -> parse_e_SCI8_form ch base iaddr instr
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [STR "Internal error in parse_e_instruction"])))
      | 3 -> parse_e_D_form ch base iaddr instr 1
      | t ->
         NotRecognized ("non-VLE-1:" ^ (string_of_int t), instr))

  (* D form *)
  | 3 -> parse_e_D_form ch base iaddr instr 3

  (* D form *)
  | 5 -> parse_e_D_form ch base iaddr instr 5

  (* LI20 / I16A / IA16 / I16L / M / BD24 / BD15 / X / XO / XL / XFX *)
  | 7 -> parse_e_misc_form ch base iaddr instr

  | _ ->
     NotRecognized ("non-VLE-" ^ (string_of_int prefix), instr)


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
    parse_e_instruction ch base iaddr instr32 prefix
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

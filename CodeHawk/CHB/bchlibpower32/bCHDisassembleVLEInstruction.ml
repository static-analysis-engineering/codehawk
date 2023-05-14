(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2023  Aarno Labs, LLC

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

module TR = CHTraceResult


let stri = string_of_int


let parse_se_C_form
      (ch: pushback_stream_int)
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
     let tgt = pwr_special_register_op ~reg:PowerLR ~mode:RD in
     BranchLinkRegister (VLE16, tgt)

  (* < 0>< 0>< 0>< 5>    se_blrl *)
  | 5 ->
     let tgt = pwr_special_register_op ~reg:PowerLR ~mode:RW in
     BranchLinkRegisterLink (VLE16, tgt)

  (* < 0>< 0>< 0>< 6>    se_bctr *)
  | 6 ->
     let tgt = pwr_special_register_op ~reg:PowerCTR ~mode:RD in
     BranchCountRegister (VLE16, tgt)

  (* < 0>< 0>< 0>< 7>    se_bctrl *)
  | 7 ->
     let tgt = pwr_special_register_op ~reg:PowerCTR ~mode:RD in
     BranchCountRegisterLink (VLE16, tgt)

  (* < 0>< 0>< 0>< 8>    se_rfi *)
  | 8 ->
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:WR in
     let sr0 = pwr_special_register_op ~reg:PowerSRR0 ~mode:RD in
     let sr1 = pwr_special_register_op ~reg:PowerSRR1 ~mode:RD in
     ReturnFromInterrupt (VLE16, msr, sr0, sr1)

  (* < 0>< 0>< 0><10>   se_rfdi *)
  | 10 ->
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:WR in
     let dsr0 = pwr_special_register_op ~reg:PowerDSRR0 ~mode:RD in
     let dsr1 = pwr_special_register_op ~reg:PowerDSRR1 ~mode:RD in
     (* se_rfdi *)
     ReturnFromDebugInterrupt (VLE16, msr, dsr0, dsr1)

  (* < 0>< 0>< 0><11>   se_rfmci *)
  | 11 ->
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:WR in
     let mcsr0 = pwr_special_register_op ~reg:PowerMCSRR0 ~mode:RD in
     let mcsr1 = pwr_special_register_op ~reg:PowerMCSRR1 ~mode:RD in
     (* se_rfmci *)
     ReturnFromMachineCheckInterrupt (VLE16, msr, mcsr0, mcsr1)
  | _ ->     
     NotRecognized("000-C:" ^ (string_of_int opc), instr)


(** R-form: (16-bit Monadic Instructions)

    0..5: OPCD (primary opcode)
    6..11: XO (extended opcode)
    12..15: RX (GPR in the ranges GPR0-GPR7 or GPR24-GPR31, src or dst)
*)
let parse_se_R_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let opc = b 8 11 in
  let rx = pwr_gp_register_op ~index:(rindex (b 12 15)) in
  match opc with

  (* < 0>< 0>< 2><rx>   se_not *)
  | 2 ->
     let cr = cr0_op ~mode:NT in
     (* se_not rX *)
     ComplementRegister (VLE16, false, rx ~mode:WR, rx ~mode:RD, cr)

  (* < 0>< 0>< 3><rx>   se_neg *)
  | 3 ->
     let cr = cr0_op ~mode:NT in
     let so = xer_so_op ~mode:NT in
     let ov = xer_ov_op ~mode:NT in
     (* se_neg rX *)
     Negate (VLE16, false, false, rx ~mode: WR, rx ~mode:RD, cr, so, ov)

  (* < 0>< 0>< 8><rx>   se_mflr *)
  | 8 ->
     let lr = pwr_special_register_op ~reg:PowerLR in
     (* se_mflr rX *)
     MoveFromLinkRegister (VLE16, rx ~mode:WR, lr ~mode:RD)

  (* < 0>< 0>< 9><rx>   se_mtlr *)
  | 9 ->
     let lr = pwr_special_register_op ~reg:PowerLR in
     (* se_mtrl rX *)
     MoveToLinkRegister (VLE16, lr ~mode:WR, rx ~mode:WR)

  (* < 0>< 0><10><rx>   se_mfctr *)
  | 10 ->
     let ctr = pwr_special_register_op ~reg:PowerCTR in
     (* se_mfctr rX *)
     MoveFromCountRegister (VLE16, rx ~mode:WR, ctr ~mode:RD)

  (* < 0>< 0><11><rx>   se_mtctr *)
  | 11 ->
     let ctr = pwr_special_register_op ~reg:PowerCTR in
     (* se_mtctr rX *)
     MoveToCountRegister (VLE16, ctr ~mode:WR, rx ~mode:RD)

  (* < 0>< 0><12><rx>   se_extzb *)
  | 12 ->
     (* se_extzb rX *)
     ExtendZeroByte (VLE16, rx ~mode:RW)

  (* < 0>< 0><13><rx>   se_extsb *)
  | 13 ->
     let cr0 = cr0_op ~mode:NT in
     (* se_extsb rX *)
     ExtendSignByte (VLE16, false, rx ~mode:WR, rx ~mode:RD, cr0)

  (* < 0>< 0><14><rx>   se_extzh *)
  | 14 ->
     (* se_extzh rX *)
     ExtendZeroHalfword (VLE16, rx ~mode:RW)

  (* < 0>< 0><15><rx>   se_extsh *)
  | 15 ->
     let cr = cr0_op ~mode:NT in
     (* se_extsh rX *)
     ExtendSignHalfword (VLE16, false, rx ~mode:WR, rx ~mode:RD, cr)
  
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
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let rx = pwr_gp_register_op ~index:(rindex (b 12 15)) in
  let ry = pwr_gp_register_op ~index:(rindex (b 8 11)) in
  let cr_nt = cr_op ~mode:NT in
  let ov_nt = xer_ov_op ~mode:NT in
  let so_nt = xer_so_op ~mode:NT in
  let opc = b 4 7 in
  match opc with
    
  (* < 0>< 1><ry><rx>    se_mr *)
  | 1 ->
     (* se_mr rX, rY *)
     MoveRegister (VLE16, false, rx ~mode:WR, ry ~mode:RD)

  (* < 0>< 2><ry><ax>   se_mtar *)
  | 2 ->
     let arx = pwr_gp_register_op ~index:(arindex (b 12 15)) in
     MoveToAlternateRegister (VLE16, arx ~mode:WR, ry ~mode:RD)

  (* < 0>< 3><ay><rx>   se_mfar *)
  | 3 ->
     (* se_mfar rx, arY *)
     let ary = pwr_gp_register_op ~index:(arindex (b 8 11)) in
     MoveFromAlternateRegister (VLE16, rx ~mode:WR, ary ~mode:RD)

  (* < 0>< 4><ry><rx>   se_add *)
  | 4 ->
     (* se_add rX, rY *)
     Add (VLE16, false, false, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD,
          cr_nt, so_nt, ov_nt)

  (* < 0>< 5><ry><rx>   se_mullw *)
  | 5 ->
     (* se_mullw rX, rY *)
     MultiplyLowWord
       (VLE16, false, false, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD,
        cr_nt, so_nt, ov_nt)

  (* < 0>< 6><ry><rx>   se_sub *)
  | 6 ->
     (* se_sub rX, rY *)
     Subtract (VLE16, rx ~mode:WR, ry ~mode:RD)

  (* < 0>< 7><ry><rx>   se_subf (documentation missing) *)
  | 7 ->
     (* se_subf rX, rY *)
     SubtractFrom
       (VLE16, false, false, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD, cr_nt, so_nt, ov_nt)

  (* < 0><12><ry><rx>   se_cmp (assume word size) *)
  | 12 ->
     let cr = cr0_op ~mode:WR in
     (* se_cmp rX,rY *)
     CompareWord (VLE16, cr, rx ~mode:RD, ry ~mode:RD)

  (* < 0><13><ry><rx>   se_cmpl *)
  | 13 ->
     let cr = cr0_op ~mode:WR in
     (* se_cmpl rX, rY *)
     CompareLogical (VLE16, cr, rx ~mode:RD, ry ~mode:RD)

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
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let ui5 = b 7 11 in
  let oim5 = ui5 + 1 in
  let immop =
    pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical oim5) in
  let ui5op =
    pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical ui5) in
  let rx = pwr_gp_register_op ~index:(rindex (b 12 15)) in
  let opc = b 4 6 in
  match opc with

  (* < 2><0><oi5><rx>   se_addi *)
  | 0 ->
     let cr = cr0_op ~mode:NT in
     (* se_addi rX, OIMM *)
     AddImmediate
       (VLE16, false, false, false, false, rx ~mode:WR, rx ~mode:RD, immop, cr)

  (* < 2><2><oi5><rx>   se_subi *)
  (* < 2><3><oi5><rx>   se_subi. *)
  | 2 | 3 ->
     let cr = cr0_op ~mode:WR in
     (* se_subi rX,OIMM *)
     (* se_subi. rX,OIMM *)
     SubtractImmediate (VLE16, opc = 3, rx ~mode:WR, rx ~mode:RD, immop, cr)

  (* < 2><1><oi5><rx>   se_cmpli *)
  | 1 ->
     let cr = cr0_op ~mode:WR in
     (* se_cmpli rX, OIMM *)
     CompareLogicalImmediate (VLE16, false, cr, rx ~mode:RD, immop)

  (* < 2><5><ui5><rx>   se_cmpi *)
  | 5 ->
     let cr = cr0_op ~mode:WR in
     (* se_cmpi rX, UI5 *)
     CompareImmediate (VLE16, false, cr, rx ~mode:RD, ui5op)

  (* < 2><6><ui5><rx>   se_bmaski *)
  | 6 ->
     (* se_bmaski rX, UI5 *)
     BitMaskGenerateImmediate (VLE16, rx ~mode:WR, ui5op)

  (* < 2><7><ui5><rx>   se_andi *)
  | 7 ->
     let cr = cr0_op ~mode:NT in
  (* se_andi rX,UI5 *)
     AndImmediate
       (VLE16, false, false, false, rx ~mode:WR, rx ~mode:RD, ui5op, cr)

  | _ ->
     NotRecognized("2-IM:" ^ (string_of_int opc), instr)


let parse_se_IM7_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let rx = pwr_gp_register_op ~index:(rindex (b 12 15)) in
  let imm7 = b 5 11 in
  let immop =
    pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical imm7) in
  LoadImmediate (VLE16, false, false, rx ~mode:WR, immop)


let parse_se_4RR_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let rx = pwr_gp_register_op ~index:(rindex (b 12 15)) in
  let ry = pwr_gp_register_op ~index:(rindex (b 8 11)) in
  let opc = b 5 7 in

  match opc with

  (* < 4>0<0><ry><rx>   se_srw *)
  | 0 ->
     let cr0 = cr0_op ~mode:NT in
     (* se_srw rX,rY *)
     ShiftRightWord (VLE16, false, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD, cr0)

  (* < 4>0<1><ry><rx>   se_sraw rX, rY *)
  | 1 ->
     let cr0 = cr0_op ~mode:NT in
     let ca = xer_ca_op ~mode:WR in
     ShiftRightAlgebraicWord
       (VLE16, false, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD, cr0, ca)

  (* < 4>0<2><ry><rx>   se_slw rX, rY *)
  | 2 ->
     let cr0 = cr0_op ~mode:NT in
     ShiftLeftWord (VLE16, false, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD, cr0)

  (* < 4>0<4><ry><rx>    se_or *)
  | 4 ->
     let cr = cr0_op ~mode:NT in
     (* se_or rX, rY *)
     Or (VLE16, false, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD, cr)

  (* < 4>0<5><ry><rx>   se_andc rX,rY *)
  | 5 ->
     let cr = cr0_op ~mode:NT in
     (*se_andc rX,rY *)
     AndComplement (VLE16, false, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD, cr)

  (* < 4>0<6><ry><rx>    se_and rX, rY *)
  (* < 4>0<7><ry><rx>    se_and rX, rY *)
  | 6 | 7 ->
     let rc = (b 7 7) = 1 in
     let cr = cr_op ~mode:WR in
     And (VLE16, rc, rx ~mode:WR, rx ~mode:RD, ry ~mode:RD, cr)
     
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
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let imm5 = b 7 11 in
  let immop =
    pwr_immediate_op ~signed:false ~size: 4 ~imm:(mkNumerical imm5) in
  let rx = pwr_gp_register_op ~index:(rindex (b 12 15)) in
  let opc = b 4 6 in
  match opc with
  (* < 6><0><ui5><rx>    se_bclri *)
  | 0 ->
     (* se_bclri rX, *UI5 *)
     BitClearImmediate (VLE16, rx ~mode:RW, immop)

  (* < 6><1><ui5><rx>    se_bgeni *)
  | 1 ->
     (* se_bgeni rX, UI5 *)
     BitGenerateImmediate (VLE16, rx ~mode:WR, immop)

  (* < 6><2><ui5><rx>   se_bseti *)
  | 2 ->
     (* se_bseti rX, UI5 *)
     BitSetImmediate (VLE16, rx ~mode:WR, immop)

  (* < 6><3><ui5><rx>   se_btsti *)
  | 3 ->
     let cr = cr0_op ~mode:WR in
     (* se_btsti rX,UI5 *)
     BitTestImmediate (VLE16, rx ~mode:WR, immop, cr)

  (* < 6><4><ui5><rx>   se_srwi *)
  | 4 ->
     let cr = cr0_op ~mode:NT in
     (* se_srwi rX,rY *)
     ShiftRightWordImmediate (VLE16, false, rx ~mode:WR, rx ~mode:RD, immop, cr)

  (* < 6><5><ui5><rx>   se_srawi *)
  | 5 ->
     let cr = cr0_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     (* se_srawi rx, UI5 *)
     ShiftRightAlgebraicWordImmediate
       (VLE16, false, rx ~mode:WR, rx ~mode:RD, immop, cr, ca)

  (* 0110110<ui5><rx>   se_slwi *)
  | 6 ->
     let cr0 = cr0_op ~mode:NT in
     (* se_slwi rX, UI5 *)
     ShiftLeftWordImmediate (VLE16, false, rx ~mode:WR, rx ~mode:RD, immop, cr0)

  | _ ->
     NotRecognized("6-IM5:" ^ (string_of_int opc), instr)


let parse_se_branch
      (ch: pushback_stream_int)
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
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in
  let sd4 w = mkNumerical (w * (b 4 7)) in
  let rz = pwr_gp_register_op ~index:(rindex (b 8 11)) in
  let rx = pwr_gp_register_op ~index:(rindex (b 12 15)) in
  let mem w =
    pwr_indirect_register_op ~basegpr:(rindex (b 12 15)) ~offset:(sd4 w) in
  let opc = b 0 3 in
  match opc with

  (* < 8><sd><rz><rx>   se_lbz *)
  | 8 ->
     (* se_lbz rZ, SD4(rX) *)
     LoadByteZero (VLE16, false, rz ~mode:WR, rx ~mode:RD, mem 1 ~mode:RD)

  (* < 9><sd><rz><rx>   se_stb *)
  | 9 ->
     (* se_stb rZ, SD4(rX) *)
     StoreByte (VLE16, false, rz ~mode:RD, rx ~mode:RD, mem 1 ~mode:WR)

  (* <10><sd><rz><rx>   se_lhz *)
  | 10 ->
     (* se_lhz rZ, SD4(rX) *)
     LoadHalfwordZero (VLE16, false, rz ~mode:WR, rx ~mode:RD, mem 2 ~mode:RD)

  (* <11><sd><rz><rx>   se_sth *)
  | 11 ->
     (* se_sth rZ, SD4(rX) *)
     StoreHalfword (VLE16, false, rz ~mode:RD, rx ~mode:RD, mem 2 ~mode:WR)

  (* <12><sd><rz><rx>   se_lwz *)
  | 12 ->
     (* se_lwz rZ, SD4(rX) *)
     LoadWordZero (VLE16, false, rz ~mode:WR, rx ~mode:RD, mem 4 ~mode:RD)

  (* <13><sd><rz><rx>   se_stw *)
  | 13 ->
     (* se_stw rZ, SD4(rX) *)
     StoreWord (VLE16, false, rz ~mode:RD, rx ~mode:RD, mem 4 ~mode:WR)

  | _ ->
     NotRecognized("SD4:" ^ (string_of_int opc), instr)

     
let parse_se_instruction
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 16 in

  if (b 0 11) = 0 then
    parse_se_C_form ch iaddr instr

  else if (b 0 7) = 0 then
    parse_se_R_form ch iaddr instr

  else
    match (b 0 3) with
    | 0 -> parse_se_0RR_form ch iaddr instr
    | 2 -> parse_se_IM_form ch iaddr instr
    | 4 when (b 4 4) = 1 -> parse_se_IM7_form ch iaddr instr
    | 4 -> parse_se_4RR_form ch iaddr instr
    | 6 -> parse_se_IM5_form ch iaddr instr
    | 14 -> parse_se_branch ch iaddr instr
    | _ -> parse_se_SD4_form ch iaddr instr


let parse_e_D8_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  let opc1 = b 16 19 in
  let opc2 = b 20 23 in
  let ra_index = b 11 15 in
  let d8 = d8_sign_extend (b 24 31) in
  let mk_mem mnem mode =
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
        pwr_absolute_op (TR.tget_ok (int_to_doubleword d8)) mode
    else
      pwr_indirect_register_op
        ~basegpr:ra_index
        ~offset:(mkNumerical d8)
        ~mode:mode in

  match (opc1, opc2) with

  (* < 1>10< rd>< ra>< 0>< 0><--d8-->    e_lbzu *)
  | (0, 0) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_lbzu" RD in
     LoadByteZero (VLE32, true, rd ~mode:WR, ra ~mode:RW, mem)

  (* < 1>10< rd>< ra>< 0>< 2><--d8-->    e_lwzu *)
  | (0, 2) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_lwzu" RD in
     LoadWordZero (VLE32, true, rd ~mode:WR, ra ~mode:RW, mem)

  (* < 1>10< rs>< ra>< 0>< 4><--d8-->    e_stbu *)
  | (0, 4) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_stbu" WR in
     StoreByte (VLE32, true, rs ~mode:RD, ra ~mode:RW, mem)

  (* < 1>10< rs>< ra>< 0>< 6><--d8-->    e_stwu *)
  | (0, 6) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_stwu" WR in
     StoreWord (VLE32, true, rs ~mode:RD, ra ~mode:RW, mem)

  (* < 1>10< rd>< ra>< 0>< 8><--d8-->    e_lmw *)
  | (0, 8) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_lmw" RD in
     LoadMultipleWord (VLE32, rd ~mode:RW, ra ~mode:RD, mem)

  (* < 1>10< rs>< ra>< 0>< 9><--d8-->    e_stmw *)
  | (0, 9) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_stmw" WR in
     StoreMultipleWord (VLE32, rs ~mode:RD, ra ~mode:RD, mem)

  (* < 1>10<  0>< ra>< 1>< 0><--d8-->    e_lmvgprw *)
  | (1, 0) when (b 6 10) = 0 ->
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_lmvgprw" WR in
     LoadMultipleVolatileGPRWord (VLE32, ra ~mode:RD, mem)

  (* < 1>10<  1>< ra>< 1>< 0><--d8-->    e_lmvsprw *)
  | (1, 0) when (b 6 10) = 1 ->
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_lmvsprw" WR in
     let cr = pwr_special_register_op ~reg:PowerCR in
     let lr = pwr_special_register_op ~reg:PowerLR in
     let ctr = pwr_special_register_op ~reg:PowerCTR in
     let xer = pwr_special_register_op ~reg:PowerXER in
     LoadMultipleVolatileSPRWord (
         VLE32,
         ra ~mode:RD,
         mem,
         cr ~mode:WR,
         lr ~mode:WR,
         ctr ~mode:WR,
         xer ~mode:WR)

  (* < 1>10<  4>< ra>< 1>< 0><--d8-->    e_lmvsrrw *)
  | (1, 0) when (b 6 10) = 4 ->
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_lmvsrrw" WR in
     let srr0 = pwr_special_register_op ~reg:PowerSRR0 in
     let srr1 = pwr_special_register_op ~reg:PowerSRR1 in
     LoadMultipleVolatileSRRWord
       (VLE32, ra ~mode:RD, mem, srr0 ~mode:RD, srr1 ~mode:RD)

  (* < 1>10<  0>< ra>< 1>< 1><--d8-->    e_stmvgprw *)
  | (1, 1) when (b 6 10) = 0 ->
     let ra = pwr_gp_register_op ~index:ra_index in
     let ea = mk_mem "e_stmvgprw" WR in
     StoreMultipleVolatileGPRWord (VLE32, ra ~mode:RD, ea)

  (* < 1>10<  1>< ra>< 1>< 1><--d8-->    e_stmvsprw *)
  | (1, 1) when (b 6 10) = 1 ->
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_stmvsprw" WR in
     let cr = pwr_special_register_op ~reg:PowerCR in
     let lr = pwr_special_register_op ~reg:PowerLR in
     let ctr = pwr_special_register_op ~reg:PowerCTR in
     let xer = pwr_special_register_op ~reg:PowerXER in
     StoreMultipleVolatileSPRWord (
         VLE32, ra ~mode:RD, mem, cr ~mode:RD, lr ~mode:RD, ctr ~mode:RD, xer ~mode:RD)

  (* < 1>10<  4>< ra>< 1>< 1><--d8-->    e_stmvsrrw *)
  | (1, 1) when (b 6 10) = 4 ->
     let ra = pwr_gp_register_op ~index:ra_index in
     let mem = mk_mem "e_stmvsrrw" WR in
     let srr0 = pwr_special_register_op ~reg:PowerSRR0 in
     let srr1 = pwr_special_register_op ~reg:PowerSRR1 in
     StoreMultipleVolatileSRRWord
       (VLE32, ra ~mode:RD, mem, srr0 ~mode:RD, srr1 ~mode:RD)

  | _ ->
     NotRecognized (
         "18-D8:" ^ (string_of_int opc1) ^ "_" ^ (string_of_int opc2), instr)


let parse_e_SCI8_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  let opc = b 16 19 in
  let rc = (b 20 20 ) = 1 in

  match opc with
  (* < 1>10< rd>< ra>< 8>cFsc<-ui8-->   e_addi *)
  | 8 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let f = b 21 21 in
     let scl = b 22 23 in
     let ui8 = b 24 31 in
     let imm = sci8 f scl ui8 in
     let immop =
       pwr_immediate_op ~signed:true ~size:4 ~imm:(mkNumerical imm) in
     let cr = cr_op ~mode:WR in
     (* e_addi rD,rA,SCI8 *)
     (* e_addi. rD,rA,SCI8 *)
     AddImmediate
       (VLE32, false, false, false, rc, rd ~mode:WR, ra ~mode:RD, immop, cr)

  (* < 1>10< rd>< ra>< 9>cFsc<--ui8->   e_addic *)
  | 9 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let f = b 21 21 in
     let ui8 = b 24 31 in
     let scl = b 22 23 in
     let imm = sci8 f scl ui8 in
     let immop =
       pwr_immediate_op ~signed:true ~size:4 ~imm:(mkNumerical imm) in
     let rc = (b 20 20) = 1 in
     let cr = cr0_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     (* e_addic rD,rA,SCI8 *)
     AddImmediateCarrying (VLE32, rc, rd ~mode:WR, ra ~mode:RD, immop, cr, ca)

  (* < 1>10< rd>< ra><10>0Fsc<--ui8->   e_mulli *)
  | 10 when (b 20 20) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let f = b 21 21 in
     let ui8 = b 24 31 in
     let scl = b 22 23 in
     let imm = sci8 f scl ui8 in
     let immop =
       pwr_immediate_op ~signed:true ~size:4 ~imm:(mkNumerical imm) in
     (* e_mulli rD,rA,SCI8 *)
     MultiplyLowImmediate (VLE32, false, rd ~mode:WR, ra ~mode:RD, immop)

  (* < 1>10<1>cr< ra><10>1Fsc<--ui8->   e_cmpli *)
  | 10 when (b 20 20) = 1 ->
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let f = b 21 21 in
     let ui8 = b 24 31 in
     let scl = b 22 23 in
     let imm = sci8 f scl ui8 in
     let immop =
       pwr_immediate_op ~signed:true ~size:4 ~imm:(mkNumerical imm) in
     let cr = crf_op (b 9 10) in
     (* e_cmpli crD32,rA,SCI8 *)
     CompareLogicalImmediate (VLE32, false, cr ~mode:WR, ra ~mode:RD, immop)

  (* < 1>10< rd>< ra><11>cFsc<--ui8->   e_subfic *)
  | 11 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let f = b 21 21 in
     let ui8 = b 24 31 in
     let scl = b 22 23 in
     let imm = sci8 f scl ui8 in
     let immop =
       pwr_immediate_op ~signed:true ~size:4 ~imm:(mkNumerical imm) in
     let cr0 = cr0_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     (* e_subfic rD,rA,SCI8 *)
     (* e_subfic. rD,rA,SCI8 *)
     SubtractFromImmediateCarrying
       (VLE32, rc, rd ~mode:WR, ra ~mode:RD, immop, cr0, ca)

  (* < 1>10< rs>< ra><12>cFsc<--ui8->   e_andi *)
  | 12 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let f = b 21 21 in
     let ui8 = b 24 31 in
     let scl = b 22 23 in
     let imm = sci8 f scl ui8 in
     let immop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical imm) in
     let cr0 = cr0_op ~mode:WR in
     (* e_andi rA,rS,SCI8 *)
     AndImmediate (VLE32, false, false, rc, ra ~mode:WR, rs ~mode:RD, immop, cr0)

(* < 1>10< rs>< ra><13>cFsc<--ui18->   e_ori *)
  | 13 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let f = b 21 21 in
     let ui8 = b 24 31 in
     let scl = b 22 23 in
     let imm = sci8 f scl ui8 in
     let immop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical imm) in
     let cr0 = cr0_op ~mode:WR in
     (* e_ori rA,rS,SCI8 *)
     OrImmediate (VLE32, rc, false, false, ra ~mode:WR, rs ~mode:RD, immop, cr0)

  (* < 1>10< rs>< ra><14>cFsc<--ui8->   e_xori *)
  | 14 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let f = b 21 21 in
     let ui8 = b 24 31 in
     let scl = b 22 23 in
     let imm = sci8 f scl ui8 in
     let immop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical imm) in
     let cr0 = cr0_op ~mode:WR in
     (* e_xori rA,rS,SCI8 *)
     XorImmediate (VLE32, rc, false, ra ~mode:WR, rs ~mode:RD, immop, cr0)

  | _ ->
     NotRecognized ("18-SCI8:" ^ (string_of_int opc), instr)


(** D Form (not documented)
    0..5: OPCD  (primary opcode)
    6..10: RS (source register)
    11..15: RA (address register)
    16..31: D (offset, signed)
 *)
let parse_e_D_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int)
      (prefix: int) =
  let b = instr#get_reverse_segval 32 in
  match (prefix, b 4 5) with

  (* < 1>11<rd><ra><------si------>   e_add16i *)
  | (1, 3) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let imm = b 16 31 in
     let immop =
       pwr_immediate_op ~signed:true ~size:2 ~imm:(mkNumerical imm) in
     let cr = cr_op ~mode:NT in
     (* e_add16i rD,rA,SI *)
     AddImmediate
       (VLE32, false, false, true, false, rd ~mode:WR, ra ~mode:RD, immop, cr)

  (* < 3>00< rd>< ra><------D------->    e_lbz *)
  | (3, 0) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let offset = mkNumerical (b 16 31) in
     let mem = pwr_indirect_register_op ~basegpr:(b 11 15) ~offset in
     (* e_lbz rD,D(rA) *)
     LoadByteZero (VLE32, false, rd ~mode:WR, ra ~mode:RD, mem ~mode:RD)

  (* < 3>01< rs>< ra><------D------->    e_stb *)
  | (3, 1) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let offset = mkNumerical (b 16 31) in
     let mem = pwr_indirect_register_op ~basegpr:(b 11 15) ~offset in
     (* e_stb rS,D(rA) *)
     StoreByte (VLE32, false, rs ~mode:RD, ra ~mode:RD, mem ~mode:WR)

  (* < 5>00< rd>< ra><-------D------>   e_lwz *)
  | (5, 0) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let offset = (b 16 31) in
     let offset = if (b 16 16) = 1 then offset - e16 else offset in
     let offset = mkNumerical offset in
     let mem = pwr_indirect_register_op ~basegpr:(b 11 15) ~offset in
     (* e_lwz rD,D(rA) *)
     LoadWordZero (VLE32, false, rd ~mode:WR, ra ~mode:RD, mem ~mode:RD)

  (* < 5>01< rs>< ra><------D------->   e_stw *)
  | (5, 1) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let offset = (b 16 31) in
     let offset = if (b 16 16) = 1 then offset - e16 else offset in
     let offset = mkNumerical offset in
     let mem = pwr_indirect_register_op ~basegpr:(b 11 15) ~offset in
     StoreWord (VLE32, false, rs ~mode:RD, ra ~mode:RD, mem ~mode:WR)

  (* < 5>10< rd>< ra><-------D------>   e_lhz *)
  | (5, 2) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let offset = (b 16 31) in
     let offset = if (b 16 16) = 1 then offset - e16 else offset in
     let offset = mkNumerical offset in
     let mem = pwr_indirect_register_op ~basegpr:(b 11 15) ~offset in
     (* e_lhz rD,D(rA) *)
     LoadHalfwordZero (VLE32, false, rd ~mode:WR, ra ~mode:RD, mem ~mode:RD)

  (* < 5>11< rs>< ra><-------D------>   e_sth *)
  | (5, 3) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let offset = (b 16 31) in
     let offset = if (b 16 16) = 1 then offset - e16 else offset in
     let offset = mkNumerical offset in
     let mem = pwr_indirect_register_op ~basegpr:(b 11 15) ~offset in
     (* e_sth rS,D(rA) *)
     StoreHalfword (VLE32, false, rs ~mode:RD, ra ~mode:RD, mem ~mode:WR)

  | (p, x) ->
     NotRecognized ("D:" ^ (string_of_int prefix) ^ "_" ^ (string_of_int x), instr)


let parse_e_misc_0_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  match (b 16 16, b 17 20) with

  (* < 7>00<rd><li2>0<li><---li---->   e_li (LI20) *)
  | (0, _) ->
     let imm = ((b 17 20) lsl 16) + ((b 11 15) lsl 11) + (b 21 31) in
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let immop =
       pwr_immediate_op ~signed:true ~size:4 ~imm:(mkNumerical imm) in
     LoadImmediate (VLE32, true, false, rx ~mode:WR, immop)

  (* < 7>00<si4>< ra>1< 2><---si---->   e_add2is *)
  | (1, 2) ->
     let imm = ((b 6 10) lsl 11) + (b 21 31) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr = cr0_op ~mode:NT in
     let immop =
       pwr_immediate_op ~signed:true ~size:2 ~imm:(mkNumerical imm) in
     (* e_add2is rA,SI *)
     AddImmediate
       (VLE32, true, true, false, false, ra ~mode:WR, ra ~mode:RD, immop, cr)

  (* < 7>00<si4>< ra>1< 3><---si---->   e_cmp16i *)
  | (1, 3) ->
     let imm = ((b 6 10) lsl 11) + (b 21 31) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr = cr0_op ~mode:WR in
     let immop =
       pwr_immediate_op ~signed:true ~size:4 ~imm:(mkNumerical imm) in
     (* e_cmp16i rA,SI *)
     CompareImmediate (VLE32, true, cr, ra ~mode:RD, immop)

  (* < 7>00<si4>< ra>1< 4><---si---->   e_mull2i *)
  | (1, 4) ->
     let imm = ((b 6 10) lsl 11) + (b 21 31) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let immop =
       pwr_immediate_op ~signed:true ~size:4 ~imm:(mkNumerical imm) in
     (* e_mull2i rA,SI *)
     MultiplyLowImmediate (VLE32, true, ra ~mode:WR, ra ~mode:RD, immop)

  (* < 7>00<ui5>< ra>1< 5><---ui---->   e_cmpl16i *)
  | (1, 5) ->
     let imm = ((b 6 10) lsl 11) + (b 21 31) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr = cr0_op ~mode:WR in
     let immop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical imm) in
     (* e_cmpl16i rA,UI *)
     CompareLogicalImmediate (VLE32, true, cr, ra ~mode:RD, immop)

  (* < 7>00< rd><ui1>1< 8><---ui---->   e_or2i *)
  (* < 7>00< rd><ui1>1<10><---ui---->   e_or2i *)
  | (1, 8) | (1, 10) ->
     let imm = ((b 11 15) lsl 11) + (b 21 31) in
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let immop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical imm) in
     let cr = cr0_op ~mode:WR in
     let shifted = (b 17 20) = 10 in
     (* e_or2i rD,UI *)
     OrImmediate
       (VLE32, false, shifted, true, rx ~mode:WR, rx ~mode:RD, immop, cr)

  (* < 7>00<rd><ui1>1<12><---ui---->   e_lis (LI20) *)
  | (1, 12) ->
     let imm = ((b 11 15) lsl 11) + (b 21 31) in
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let immop =
       pwr_immediate_op ~signed:true ~size:2 ~imm:(mkNumerical imm) in
     LoadImmediate (VLE32, true, true, rx ~mode:WR, immop)

  (* < 7>00<rd><ui1>1<13><---ui---->   e_and2is. *)
  | (1, 13) ->
     let imm = ((b 11 15) lsl 11) + (b 21 31) in
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let immop =
       pwr_immediate_op ~signed:false ~size:2 ~imm:(mkNumerical imm) in
     let cr = cr0_op ~mode:WR in
     (* e_and2is. rD,UI *)
     AndImmediate (VLE32, true, true, true, rd ~mode:WR, rd ~mode:RD, immop, cr)

  | (_, p) ->
     NotRecognized ("e_misc_0:" ^ (string_of_int p), instr)


let parse_e_misc_1_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  match (b 31 31) with

  (* < 7>01< rs>< ra>< sh>< mb>< me>0   e_rlwimi/e_insrwi *)
  | 0 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let sh = b 16 20 in
     let mb = b 21 25 in
     let me = b 26 30 in
     let n = (32 - sh) - mb in
     if me = (mb + n) -1 then
       let cr = cr0_op ~mode:NT in
       let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical n) in
       let mb = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical mb) in
       InsertRightWordImmediate (VLE32, false, ra ~mode:WR, rs ~mode:RD, n, mb, cr)
     else
       NotRecognized ("InsertRightWordImmediate-0", instr)

  (* < 7>01< rs>< ra><  0>< mb>< 31>1   e_clrlwi (VLEPIM) *)
  | 1 when (b 16 20) = 0 && (b 26 30) = 31 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let mb = b 21 25 in
     let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical mb) in
     (* e_clrlwi rA, rS, n *)
     ClearLeftWordImmediate (VLE32, false, ra ~mode:WR, rs ~mode:RD, n)

  (* < 7>01< rs>< ra><  0><  0>< me>1   e_clrrwi (VLEPIM) *)
  | 1 when (b 16 20) = 0 && (b 21 25) = 0 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let me = b 26 30 in
     let n = 31 - me in
     let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical n) in
     let cr = cr0_op ~mode:NT in
     (* e_clrrwi rA, rS, n *)
     ClearRightWordImmediate (VLE32, false, ra ~mode:WR, rs ~mode:RD, n, cr)

  (* < 7>01< rs>< ra>< sh>< mb>< 31>1   e_extrwi (VLEPIM) *)
  | 1 when (b 26 30) = 31 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let sh = b 16 20 in
     let mb = b 21 25 in
     let n = 32 - mb in
     let b = (sh + mb) - 32 in
     let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical n) in
     let b = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical b) in
     let cr = cr0_op ~mode:NT in
     (* e_extrwi rA,rS,n,b *)
     ExtractRightJustifyWordImmediate
       (VLE32, false, ra ~mode:WR, rs ~mode:RD, n, b, cr)

  (* < 7>01< rs>< ra>< sh>< mb>< me>1   e_rlwinm *)
  | 1 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let sh =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical (b 16 20)) in
     let mb =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical (b 21 25)) in
     let me =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical (b 26 30)) in
     let cr = cr0_op ~mode:WR in
     (* e_rlwinm rA,rS,SH,MB,ME *)
     RotateLeftWordImmediateAndMask
       (VLE32, false, ra ~mode:WR, rs ~mode:RD, sh, mb, me, cr)

  | _ ->
     NotRecognized ("e_misc_1", instr)


let parse_e_misc_2_branchlink
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  if (b 6 6) = 0 then

    (* < 7>100<---------BD24-------->1   e_bl BD24 *)
    let offset = 2 * (b 7 30) in
    let offset = if (b 7 7) = 1 then offset - e25 else offset in
    let btea = iaddr#add_int offset in
    let tgt = pwr_absolute_op btea RD in
    let lr = pwr_special_register_op ~reg:PowerLR ~mode:WR in
    (* e_bl BD24 *)
    BranchLink (VLE32, tgt, lr)

  else
    NotRecognized ("e_misc_2_bl_conditional", instr)


let parse_e_misc_2_branchconditional
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =

  (* (b 6 9) = 8, (b 31 31) = 0 *)
  let b = instr#get_reverse_segval 32 in
  let bo32 = b 10 11 in
  let bi32 = b 12 15 in
  let offset = b 16 31 in
  let offset = if offset >= e15 then offset - e16 else offset in
  let btea = iaddr#add_int offset in
  let bd = pwr_absolute_op btea RD in
  match (bo32, bi32) with

  (* < 7>10< 8>00<b>00<----BD15---->0   e_bge *)
  | (0, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28)) ->
     let cr = crbi_op bi32 ~mode:RD in
     (* e_bge bd *)
     CBranchGreaterEqual (VLE32, false, bo32, bi32, BPNone, cr, bd)

  (* < 7>10< 8>00<b>01<----BD15---->0   e_ble *)
  | (0, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29)) ->
     let cr = crbi_op bi32 ~mode:RD in
     (* e_ble bd *)
     CBranchLessEqual (VLE32, false, bo32, bi32, BPNone, cr, bd)

  (* < 7>10< 8>00<b>10<----BD15---->0   e_bne *)
  | (0, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30)) ->
     let cr = crbi_op bi32 ~mode:WR in
     (* e_bne bd *)
     CBranchNotEqual (VLE32, false, bo32, bi32, BPNone, cr, bd)

  (* < 7>10< 8>01<b>00<----BD15---->0   e_blt *)
  | (1, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28)) ->
     let cr = crbi_op bi32 ~mode:RD in
     (* e_blt bd *)
     CBranchLessThan (VLE32, false, bo32, bi32, BPNone, cr, bd)

  (* < 7>10< 8>01<b>01<----BD15---->0   e_bgt *)
  | (1, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29)) ->
     let cr = crbi_op bi32 ~mode:RD in
     (* b_bgt bd *)
     CBranchGreaterThan (VLE32, false, bo32, bi32, BPNone, cr, bd)

  (* < 7>10< 8>01<b>10<----BD15---->0   e_beq *)
  | (1, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30)) ->
     let cr = crbi_op bi32 ~mode:WR in
     (* e_beq bd *)
     CBranchEqual (VLE32, false, bo32, bi32, BPNone, cr, bd)

  (* < 7>10< 8>bo<bi><----BD15---->L  e_bc BO32,BI32,BD15 (VLEPEM) *)
  | ((0 | 1), _) ->
     let offset = b 16 31 in
     let offset = if offset >= e15 then offset - e16 else offset in
     let btea = iaddr#add_int offset in
     let bd = pwr_absolute_op btea RD in
     let bo32 = b 10 11 in
     let bi32 = b 12 15 in
     (* e_bc BO32,BI32,BD15 *)
     BranchConditional (VLE32, false, bo32, bi32, bd)

  (* < 7>10< 8>bo<bi><----BD15---->L  e_bc BO32,BI32,BD15 (VLEPEM) *)
  | ((2 | 3), _) ->
     let offset = b 16 31 in
     let offset = if offset >= e15 then offset - e16 else offset in
     let btea = iaddr#add_int offset in
     let bo32 = b 10 11 in
     let dst = pwr_absolute_op btea RD in
     let ctr = pwr_special_register_op ~reg:PowerCTR ~mode:WR in
     if (b 11 11 ) = 0 then
       (* e_bdnz dst *)
       CBranchDecrementNotZero (VLE32, false, bo32, bi32, BPNone, dst, ctr)
     else
       (* e_bdz dst *)
       CBranchDecrementZero (VLE32, false, bo32, bi32, BPNone, dst, ctr)

  | (p, q) ->
     NotRecognized
       ("e_misc_2:("
        ^ (string_of_int p)
        ^ ", "
        ^ (string_of_int q)
        ^ ")", instr)


let parse_e_misc_2_branch
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in

  if (b 6 6) = 0 then

    (* < 7>100<----------BD24-------->0   e_b BD24 *)
    let offset = 2 * (b 7 30) in
    let offset = if (b 7 7) = 1 then offset - e25 else offset in
    let btea = iaddr#add_int offset in
    let bd = pwr_absolute_op btea RD in
    (* e_b BD24 *)
    Branch (VLE32, bd)

  else if (b 6 9) = 8 then
    parse_e_misc_2_branchconditional ch iaddr instr

  else
    NotRecognized ("e_misc_2_branch:" ^ (string_of_int (b 6 9)), instr)


let parse_e_misc_2_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  if (b 31 31) = 1 then
    parse_e_misc_2_branchlink ch iaddr instr
  else
    parse_e_misc_2_branch ch iaddr instr


let parse_e_misc_3_form
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int) =
  let b = instr#get_reverse_segval 32 in
  match (b 21 21, b 22 30) with

  (* < 7>11<<c>/0< ra>< rb><----0-->/   cmpw (BookE) *)
  | (0, 0) when (b 10 10) = 0 ->
     let crd = crf_op (b 6 8) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     (* cmpw cfrD,rA,rB *)
     CompareWord (PWR, crd ~mode:WR, ra ~mode:RD, rb ~mode:RD)

  (* < 7>11< rd>< ra>< rb>E<----8-->c   subfc (BookE) *)
  | (_, 8) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     let cr = cr0_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     (* subfc rD,rA,rB *)
     SubtractFromCarrying
       (PWR, rc, oe, rd ~mode:WR, ra ~mode:WR, rb ~mode:RD, cr, ca, so, ov)

  (* < 7>11< rd>< ra>< rb>E<---10-->c   addc (BookE) *)
  | (_, 10) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     let cr = cr0_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     (* addc rD,rA,rB *)
     AddCarrying
       (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr, so, ov, ca)

  (* < 7>11< rd>< ra>< rb>/<---11-->c   mulhwu (BookE) *)
  | (0, 11) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let rc = (b 31 31) = 1 in
     let cr = cr0_op ~mode:WR in
     (* mulhwu rD,rA,rB *)
     MultiplyHighWordUnsigned
       (PWR, rc, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11< rd>< ra>< rb>0<---15-->/   isellt (BookE, simplified) *)
  | (0, 15) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:RD in
     (* isellt rD,rA,rB *)
     IntegerSelectLessThan (PWR, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11<d>//<s>///////0<---16-->/   e_mcrf *)
  | (0, 16) ->
     let crd = crf_op (b 6 8) in
     let crs = crf_op (b 11 13) in
     (* e_mcrf crD,crS *)
     MoveConditionRegisterField (VLE32, crd ~mode:WR, crs ~mode:RD)

  (* < 7>11< rd>0/////////0<---19-->/   mfcr (BookE) *)
  | (0, 19) when (b 11 11) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let cr = pwr_special_register_op ~reg:PowerCR ~mode:RD in
     (* mfcr rD *)
     MoveFromConditionRegister (PWR, rd ~mode:WR, cr)

  (* < 7>11< rd>< ra>< rb>0<---23-->/   lwzx (BookE) *)
  | (0, 23) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let mem =
       pwr_indexed_indirect_register_op
         ~basegpr:(b 11 15) ~offsetgpr:(b 16 20) in
     (* lwzx *)
     LoadWordZeroIndexed
       (PWR, false, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, mem ~mode:RD)

  (* < 7>11< rs>< ra>< rb>0<---24-->c   slw (BookE) *)
  | (0, 24) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let rc = (b 31 31) = 1 in
     let cr0 = cr0_op ~mode:WR in
     (* slw rA,rS,rB *)
     ShiftLeftWord (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr0)

  (* < 7>11< rs>< ra>/////0<---26-->c   cntlzw (BookE) *)
  | (0, 26) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr0 = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* cntlzw ra,rs) *)
     CountLeadingZerosWord (PWR, rc, ra ~mode:WR, rs ~mode:RD, cr0)

  (* < 7>11< rs>< ra>< rb>0<---28-->c   and (BookE) *)
  | (0, 28) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* and rA,rS,rB *)
     And (PWR, rc, ra ~mode:WR, rs ~mode:WR, rb ~mode:WR, cr)

  (* < 7>11<c>/0< ra>< rb>0<---32-->/   cmplw (BookE, simplified mnemonic) *)
  | (0, 32) ->
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let crfd = crf_op (b 6 8) ~mode:WR in
     (* cmplw crfd, rA, rB *)
     CompareLogical (VLE32, crfd, ra ~mode:RD, rb ~mode:RD)

  (* < 7>11<crd><cra><cra>0<---33-->/   crnot (BookE) *)
  | (0, 33) when (b 11 15) = (b 16 20) ->
     let crd = crbit_op (b 6 10) ~mode:WR in
     let cra = crbit_op (b 11 15) ~mode:RD in
     (* crnot *)
     ConditionRegisterNot (PWR, crd, cra)

  (* < 7>11< rd>< ra>< rb>E<---40-->c   subf (BookE) *)
  | (_, 40) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     (* subf rD,rA,rB *)
     SubtractFrom
       (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr, so, ov)

  (* < 7>11< rd>< ra>< rb>0<---47-->/   iselgt (BookE, simplified) *)
  | (0, 47) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:RD in
     (* iselgt rD,rA,rB *)
     IntegerSelectGreaterThan (PWR, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11< rs>< ra>< sh>0<---56-->c   e_slwi *)
  | (0, 56) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let sh = b 16 20 in
     let sh = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical sh) in
     let cr0 = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* e_slwi rA,rS,SH *)
     ShiftLeftWordImmediate (VLE32, rc, ra ~mode:WR, rs ~mode:RD, sh, cr0)

  (* < 7>11< rs>< ra>< rb>0<---60-->c   andc (BookE) *)
  | (0, 60) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* andc rA,rS,rB *)
     AndComplement (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11< rd>< ra>< rb>0<---79-->/   iseleq (BookE, simplified *)
  | (0, 79) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra =
       if (b 11 15) = 0 then
         pwr_immediate_op ~signed:false ~size:4 ~imm:numerical_zero
       else
         pwr_gp_register_op ~index:(b 11 15) ~mode:RD in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:RD in
     (* iseleq rD,rA,rB *)
     IntegerSelectEqual (PWR, rd ~mode:WR, ra, rb ~mode:RD, cr)

  (* < 7>11< rd>//////////0<---83-->/   mfmsr (BookE) *)
  | (0, 83) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:RD in
     (* mfmsr rD *)
     MoveFromMachineStateRegister (PWR, rd ~mode:WR, msr)

  (* < 7>11< rd>< ra>< rb>0<---87-->/   lbzx (BookE) *)
  | (0, 87) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let mem =
       pwr_indexed_indirect_register_op
         ~basegpr:(b 11 15) ~offsetgpr:(b 16 20) in
     (* lbzx rD,rA,rB *)
     LoadByteZeroIndexed
       (PWR, false, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, mem ~mode:RD)

  (* < 7>11< rd>< ra>/////E<--104-->c   neg (BookE) *)
  | (_, 104) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     let cr = cr0_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     (* neg rD,rA *)
     Negate (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, cr, so, ov)

  (* < 7>11< rs>< ra>< rb>0<--124-->c   not (BookE) *)
  | (0, 124) when (b 6 10) = (b 16 20) ->
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* not rA,rB *)
     ComplementRegister (PWR, rc, ra ~mode:WR, rb ~mode:RD, cr)

  (* < 7>11< rd>< ra>< rb>E<--136-->c   subfe (BookE) *)
  | (_, 136) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let oe = (b 21 21) = 1 in
     let rc = (b 31 31) = 1 in
     let cr = cr0_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     (* subfe rD,rA,rB *)
     SubtractFromExtended
       (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr, ca, so, ov)

  (* < 7>11< rd>< ra>< rb>E<--138-->c   adde (BookE) *)
  | (_, 138) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let oe = (b 21 21) = 1 in
     let rc = (b 31 31) = 1 in
     let cr = cr0_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     (* adde rA,rB,rC *)
     AddExtended
       (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr, so, ov, ca)

  (* < 7>11< rs>0<15><15>/0<--144-->/   mtcr (BookE, simplified) *)
  | (0, 144) when (b 11 11) = 0 && (b 12 19) = 255 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let cr = pwr_special_register_op ~reg:PowerCR ~mode:WR in
     (* mtcr rS *)
     MoveToConditionRegister (PWR, cr, rs ~mode:RD)

  (* < 7>11< rs>0<--crm->/0<--144-->/   mtcrf (BookE) *)
  | (0, 144) when (b 11 11) = 0 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let crm = b 12 19 in
     let crmop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical crm) in
     let crfs = pwr_cr_field_list crm in
     (* mtcrf CRM,rS *)
     MoveToConditionRegisterFields (PWR, crmop, rs ~mode:RD, crfs ~mode:WR)

  (* < 7>11<rs><.........>0<--146-->/  mtmsr (BookE) *)
  | (0, 146) ->
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let msr = pwr_special_register_op ~reg:PowerMSR in
     (* mtmsr RS *)
     MoveToMachineStateRegister (PWR, msr ~mode:WR, rx ~mode:RD)

  (* < 7>11< rs>< ra>< rb>0<--151-->/   stwx (BookE) *)
  | (0, 151) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let mem =
       pwr_indexed_indirect_register_op
         ~basegpr:(b 11 15) ~offsetgpr:(b 16 20) in
     (* stwx rS,rA,rB *)
     StoreWordIndexed
       (PWR, false, rs ~mode:RD, ra ~mode:RD, rb ~mode:RD, mem ~mode:WR)

  (* < 7>11//////////E////0<--163-->/   wrteei (BookE) *)
  | (0, 163) ->
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:WR in
     let enable = (b 16 16) = 1 in
     (* wrteei E *)
     WriteMSRExternalEnableImmediate (PWR, enable, msr)

  (* < 7>11< rs>< ra>< rb>0<--183-->/   stwux (BookE) *)
  | (0, 183) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let mem =
       pwr_indexed_indirect_register_op
         ~basegpr:(b 11 15) ~offsetgpr:(b 16 20) in
     (* stwx rS,rA,rB *)
     StoreWordIndexed
       (PWR, true, rs ~mode:RD, ra ~mode:RD, rb ~mode:RD, mem ~mode:WR)

  (* < 7>11< rd>< ra>/////E<--200-->c   subfze (BookE) *)
  | (_, 200) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr = cr0_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     (* `subfze rD,rA *)
     SubtractFromZeroExtended
       (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, cr, so, ov, ca)

  (* < 7>11< rd>< ra>/////E<--202-->c   addze (BookE) *)
  | (_, 202) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr = cr_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     (* addze rD,rA *)
     AddZeroExtended (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, cr, ca, so, ov)

  (* < 7>11< rs>< ra>< rb>0<--215-->/   stbx (BookE) *)
  | (0, 215) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let mem =
       pwr_indexed_indirect_register_op
         ~basegpr:(b 11 15) ~offsetgpr:(b 16 20) in
     (* stbx rS,rA,rB *)
     StoreByteIndexed
       (PWR, false, rs ~mode:RD, ra ~mode:RD, rb ~mode:RD, mem ~mode:WR)

  (* < 7>11< rd>< ra>/////E<--234-->c   addme (BookE) *)
  | (_, 234) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr = cr0_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     let oe = (b 21 21) = 1 in
     let rc = (b 31 31) = 1 in
     (* addme rD,rA *)
     AddMinusOneExtended (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, cr, ca, so, ov)

  (* < 7>11< rd>< ra>< rb>E<--235-->c   mullw (BookE) *)
  | (_, 235) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     (* mullw rD,rA,rB *)
     MultiplyLowWord
       (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr, so, ov)

  (* < 7>11< rd>< ra>< rb>E<--266-->c   add (BookE) *)
  | (_, 266) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     (* add rD,rA,rB *)
     Add (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr, so, ov)

  (* < 7>11< rs>< ra>< rb>0<--280-->c   e_rlw *)
  | (0, 280) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* e_rlw rA,rS,rB *)
     RotateLeftWord (VLE32, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11< rs>< ra>< rb>0<--316-->c   xor (BookE) *)
  | (0, 316) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* xor rA,rS,rB *)
     Xor (PWR, rc, ra ~mode:WR, rs ~mode:WR, rb ~mode:WR, cr)

  (* < 7>11< rd>< 0 >< 1 >0<--339-->/   mfxer (BookE, simplified) *)
  | (0, 339) when (b 11 15) = 1 && (b 16 20) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let xer = pwr_special_register_op ~reg:PowerXER ~mode:RD in
     (* mfxer rD *)
     MoveFromExceptionRegister (PWR, rd ~mode:WR, xer)

  (* < 7>11< rd><spr><spr>0<--339-->/   mfspr (BookE) *)
  | (0, 339) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let spr = ((b 16 20) lsl 5) + (b 11 15) in
     let spr =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical spr) in
     (* mfspr rD, sprn *)
     MoveFromSpecialPurposeRegister (PWR, rd ~mode:WR, spr)

  (* < 7>11< rs>< ra>< rb>0<--444-->c   or (BookE) *)
  | (0, 444) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode: WR in
     let rc = (b 31 31) = 1 in
     (* or rA,rS,rB *)
     Or (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11<crd><cra><crb>0<--449-->/   e_cror *)
  | (0, 449) ->
     let crd = crbit_op (b 6 10) ~mode:WR in
     let cra = crbit_op (b 11 15) ~mode:RD in
     let crb = crbit_op (b 16 20) ~mode:RD in
     (* e_cror crbD,crbA,crbB *)
     ConditionRegisterOr (VLE32, crd, cra, crb)

  (* < 7>11< rd>< ra>< rb>E<--459-->c   divwu (BookE) *)
  | (_, 459) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     (* divwu rD,rA,rB *)
     DivideWordUnsigned
       (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr, so, ov)

  (* < 7>11< rs><  8><  0>0<--467-->/   mtlr (BookE) *)
  | (0, 467) when (b 11 15) = 8 && (b 16 20) = 0 ->
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let lr = lr_op ~mode:WR in
     (* mtctr rS *)
     MoveToLinkRegister (PWR, lr, rx ~mode:RD)

  (* < 7>11< rs><  9><  0>0<--467-->/   mtctr (BookE) *)
  | (0, 467) when (b 11 15) = 9 && (b 16 20) = 0 ->
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let ctr = ctr_op ~mode:WR in
     (* mtctr rS *)
     MoveToCountRegister (PWR, ctr, rx ~mode:RD)

  (* < 7>11< rs><spr><spr>0<--467-->/   mtspr (BookE) *)
  | (0, 467) ->
     let sprn = ((b 16 20) lsl 5) + (b 11 15) in
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let immop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical sprn) in
     (* mtspr sprN, rS *)
     MoveToSpecialPurposeRegister(PWR, immop, rx ~mode:WR)

  (* < 7>11< rd>< ra>< rb>E<--491-->c   divw (BookE) *)
  | (_, 491) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let so = xer_so_op ~mode:WR in
     let ov = xer_ov_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     let oe = (b 21 21) = 1 in
     (* divw rD,rA,rB *)
     DivideWord (PWR, rc, oe, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr, so, ov)

  (* < 7>11< rs>< ra>< rb>1<---24-->c   srw (BookE) *)
  | (1, 24) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* srw rA,rS,rB *)
     ShiftRightWord (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11< rs>< ra>< sh>1<---56-->c   e_srwi *)
  | (1, 56) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let sh = b 16 20 in
     let sh = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical sh) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* srwi rA,rS,SH *)
     ShiftRightWordImmediate (VLE32, rc, ra ~mode:WR, rs ~mode:RD, sh, cr)

  (* < 7>11< rs>< ra>< rb>1<--280-->c   sraw (BookE) *)
  | (1, 280) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let rc = (b 31 31) = 1 in
     let cr = cr0_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     (* sraw rA,rS,rB *)
     ShiftRightAlgebraicWord
       (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr, ca)

  (* < 7>11< rs>< ra>< sh>1<--312-->c   srawi (BookE) *)
  | (1, 312) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let sh = b 16 20 in
     let sh =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical sh) in
     let rc = (b 31 31) = 1 in
     let cr = cr0_op ~mode:WR in
     let ca = xer_ca_op ~mode:WR in
     (* srawi rA,rS,sh  documentation error? *)
     ShiftRightAlgebraicWordImmediate
       (PWR, rc, ra ~mode:WR, rs ~mode:RD, sh, cr, ca)

  (* < 7>11< rs>< ra>/////1<--410-->c   extsh (BookE) *)
  | (1, 410) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* extsh rA,rS *)
     ExtendSignHalfword (PWR, rc, ra ~mode:WR, rs ~mode:RD, cr)

  (* < 7>110//////////////1<--466-->/   tlbwe (BookE) *)
  | (1, 466) when (b 6 6) = 0 ->
     (* tlbwe *)
     TLBWriteEntry PWR

  (* < 7>11< mo>//////////1<--342-->/   mbar (BookE) *)
  | (1, 342) ->
     let mo = b 6 10 in
     let mo = pwr_immediate_op ~signed:false ~size:1 ~imm:(mkNumerical mo) in
     (* mbar *)
     MemoryBarrier (PWR, mo)

  | (p, q) ->
     NotRecognized
       ("e_misc_3:(" ^ (string_of_int p) ^ ", " ^ (string_of_int q) ^ ")", instr)


let parse_e_instruction
      (ch: pushback_stream_int)
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
          | 0 -> parse_e_D8_form ch iaddr instr
          | 1 -> parse_e_SCI8_form ch iaddr instr
          | _ ->
             raise
               (BCH_failure
                  (LBLOCK [STR "Internal error in parse_e_instruction"])))
      | 3 -> parse_e_D_form ch iaddr instr 1
      | t ->
         NotRecognized ("non-VLE-1:" ^ (string_of_int t), instr))

  (* D form *)
  | 3 -> parse_e_D_form ch iaddr instr 3

  (* D form *)
  | 5 -> parse_e_D_form ch iaddr instr 5

  (* LI20 / I16A / IA16 / I16L / M / BD24 / BD15 / X / XO / XL / XFX *)
  | 7 ->
     (match (b 4 5) with
      | 0 -> parse_e_misc_0_form ch iaddr instr
      | 1 -> parse_e_misc_1_form ch iaddr instr
      | 2 -> parse_e_misc_2_form ch iaddr instr
      | 3 -> parse_e_misc_3_form ch iaddr instr
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [STR "parse_e_misc:Not reachable"])))

  | _ ->
     NotRecognized ("non-VLE-" ^ (string_of_int prefix), instr)


let parse_vle_opcode
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instrbytes: int): pwr_opcode_t =
  if instrbytes = 0 then
    OpcodeIllegal 0
  else
    let prefix = instrbytes lsr 12 in
    if prefix = 1 || prefix = 3 || prefix = 5 || prefix = 7 then
      let sndhalfword = ch#read_ui16 in
      let instr32 = (instrbytes lsl 16) + sndhalfword in
      let instr32 = TR.tget_ok (int_to_doubleword instr32) in
      parse_e_instruction ch iaddr instr32 prefix
    else
      let instr16 = TR.tget_ok (int_to_doubleword instrbytes) in
      parse_se_instruction ch iaddr instr16
  

let disassemble_vle_instruction
      (ch: pushback_stream_int) (iaddr: doubleword_int) (instrbytes: int) =
  (* let iaddr = base#add_int (ch#pos - 2) in *)
  try
    parse_vle_opcode ch iaddr instrbytes
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

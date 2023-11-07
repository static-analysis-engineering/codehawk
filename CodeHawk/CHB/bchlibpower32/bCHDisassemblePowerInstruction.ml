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


let parse_opcode_4
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in

  (* floating-point general pattern:
     <   4>< rd>< ra>< rb><----i---->

  let rd = pwr_gp_register_op ~index:(b 6 10) in
  let ra = pwr_gp_register_op ~index:(b 11 15) in
  let rb = pwr_gp_register_op ~index:(b 16 20) in
   *)
  let opc = b 21 31 in
  match opc with
  | _ ->
     NotRecognized ("FP opcode:" ^ (string_of_int opc), instr)


let parse_opcode_7
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in

  (* <   7>< rd>< ra><-----simm----->   mulli *)
  let rd = pwr_gp_register_op ~index:(b 6 10) in
  let ra = pwr_gp_register_op ~index:(b 11 15) in
  let simm =
    pwr_immediate_op ~signed:true ~size:2 ~imm:(mkNumerical (b 16 31)) in
  (* mulli rD,rA,SIMM *)
  MultiplyLowImmediate (PWR, false, rd ~mode:WR, ra ~mode:RD, simm)


let parse_opcode_8
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in

  (* <   8>< rd>< ra><-----simm----->   subfic *)
  let rd = pwr_gp_register_op ~index:(b 6 10) in
  let ra = pwr_gp_register_op ~index:(b 11 15) in
  let simm =
    pwr_immediate_op ~signed:true ~size:2 ~imm:(mkNumerical (b 16 31)) in
  let cr = cr0_op ~mode:NT in
  let ca = xer_ca_op ~mode:WR in
  (* subfic rD,rA,SIMM *)
  SubtractFromImmediateCarrying
    (PWR, false, rd ~mode:WR, ra ~mode:RD, simm, cr, ca)


let parse_opcode_10
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in

  if (b 10 10) = 0 then
    (* <  10><c>/L< ra><-----uimm----->   cmpli *)
    let crfd = crf_op (b 6 8) ~mode:WR in
    let ra = pwr_gp_register_op ~index:(b 11 15) in
    let uimm =
      pwr_immediate_op ~signed:false ~size:2 ~imm:(mkNumerical (b 16 31)) in
    (* cmplwi crfd,rA,UIMM *)
    CompareLogicalImmediate (PWR, false, crfd, ra ~mode:RD, uimm)
  else
    NotRecognized ("CompareLogicalImmediate with L=1", instr)


let parse_opcode_11
      (ch:pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in

  if (b 10 10) = 0 then
    (* <  11><c>/L< ra><-----simm----->   cmpi *)
    let crfd = crf_op (b 6 8) ~mode:WR in
    let ra = pwr_gp_register_op ~index:(b 11 15) in
    let simm =
      pwr_immediate_op ~signed:true ~size:2 ~imm:(mkNumerical (b 16 31)) in
    (* cmpwi crfD,rA,SIMM *)
    CompareImmediate (PWR, false, crfd, ra ~mode:RD, simm)
  else
    NotRecognized ("CompareImmediate with L=1", instr)
  

let parse_opcode_12_13
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in

  (* <  12>< rd>< ra><-----simm----->   addic *)
  (* <  13>< rd>< ra><-----simm----->   addic. *)
  let rd = pwr_gp_register_op ~index:(b 6 10) in
  let ra = pwr_gp_register_op ~index:(b 11 15) in
  let simm =
    pwr_immediate_op ~signed:true ~size:2 ~imm:(mkNumerical (b 16 31)) in
  let rc = (b 5 5) = 1 in
  let cr = cr0_op ~mode:WR in
  let ca = xer_ca_op ~mode:WR in
  (* addic rD,rA,SIMM *)
  AddImmediateCarrying (PWR, rc, rd ~mode:WR, ra ~mode: RD, simm, cr, ca)


let parse_opcode_14_15
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in

  (* <  14>< rd>< ra><-----simm----->   addi *)
  (* <  15>< rd>< ra><-----simm----->   addis *)
  let rd = pwr_gp_register_op ~index:(b 6 10) in
  let simm =
    pwr_immediate_op ~signed:true ~size:2 ~imm:(mkNumerical (b 16 31)) in
  let shifted = (b 5 5) = 1 in
  if (b 11 15) = 0 then
    (* li rD,SIMM *)
    LoadImmediate (PWR, true, shifted, rd ~mode:WR, simm)
  else
    let ra = pwr_gp_register_op ~index:(b 11 15) in
    let cr = cr0_op ~mode:NT in    
    (* addi rD,rA,SIMM *)
    AddImmediate
      (PWR, shifted, false, false, false, rd ~mode:WR, ra ~mode:RD, simm, cr)

    
(* Branch Instruction Simplified Mnemonics
   ---------------------------------------
   BO Field (branch operations):
   0 : if set, ignore the CRT bit comparison
   1 : if set, the CR bit comparison is against ture, else against false
   2 : if set, the CTR is not decremented
   3 : if BO[2] is set, determines whether the CTR comparison is for equal to
       zero or not equal to zero
   4 : used for static branch prediction

   BI Field (bit in condition register)
   0 - 2 : CR0 - CR7
   3 - 4 : LT, GT, EQ, SO
 *)
let parse_opcode_16
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let bo = b 6 10 in
  let bi = b 11 15 in
  let bd = (b 16 29) * 4 in
  let bdval = if (b 16 16) = 1 then bd - e16 else bd in

  match (b 30 31) with
  | 0 ->
     (* <  16>< bo>< bi><------bd---->00   bc *)
     let btea = iaddr#add_int bdval in
     let bd = pwr_absolute_op btea RD in
     (match (bo, bi) with
      (* <  16><  4><c>00<------bd---->00    bge *)
      | (4, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28)) ->
         let crf = crbi_op bi ~mode:RD in
         (* bge cr, bd *)
         CBranchGreaterEqual (PWR, false, bo, bi, BPNone, crf, bd)

      (* <  16><  4><c>01<------bd---->00    ble *)
      | (4, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29)) ->
         let crf = crbi_op bi ~mode:RD in
         CBranchLessEqual (PWR, false, bo, bi, BPNone, crf, bd)

      (* <  16><  4><c>10<------bd---->00    bne *)
      | (4, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30)) ->
         let crf = crbi_op bi ~mode:RD in
         CBranchNotEqual (PWR, false, bo, bi, BPNone, crf, bd)

      (* <  16><  5><c>00<------bd---->00    bge+ *)
      | (5, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28)) ->
         let crf = crbi_op bi ~mode:RD in
         let bp = if bdval > 0 then BPPlus 1 else BPMinus 1 in
         CBranchGreaterEqual (PWR, false, bo, bi, bp, crf, bd)

      (* <  16><  5><c>01<------bd---->00    ble+ *)         
      | (5, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29)) ->
         let crf = crbi_op bi ~mode:RD in
         let bp = if bdval > 0 then BPPlus 1 else BPMinus 1 in         
         CBranchLessEqual (PWR, false, bo, bi, bp, crf, bd)

      (* <  16><  5><c>10<------bd---->00    bne+ *)         
      | (5, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30)) ->
         let crf = crbi_op bi ~mode:RD in
         let bp = if bdval > 0 then BPPlus 1 else BPMinus 1 in         
         CBranchNotEqual (PWR, false, bo, bi, bp, crf, bd)

      (* <  16><  12><c>00<------bd---->00   blt *)
      | (12, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28)) ->
         let crf = crbi_op bi ~mode:RD in
         CBranchLessThan (PWR, false, bo, bi, BPNone, crf, bd)

      | (12, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29)) ->
         let crf = crbi_op bi ~mode:RD in
         CBranchGreaterThan (PWR, false, bo, bi, BPNone, crf, bd)

      | (12, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30)) ->
         let crf = crbi_op bi ~mode:RD in
         CBranchEqual (PWR, false, bo, bi, BPNone, crf, bd)

      | (13, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28)) ->
         let crf = crbi_op bi ~mode:RD in
         let bp = if bdval > 0 then BPPlus 1 else BPMinus 1 in         
         CBranchLessThan (PWR, false, bo, bi, bp, crf, bd)

      | (13, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29)) ->
         let crf = crbi_op bi ~mode:RD in
         let bp = if bdval > 0 then BPPlus 1 else BPMinus 1 in         
         CBranchGreaterThan (PWR, false, bo, bi, bp, crf, bd)

      | (13, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30)) ->
         let crf = crbi_op bi ~mode:RD in
         let bp = if bdval > 0 then BPPlus 1 else BPMinus 1 in         
         CBranchEqual (PWR, false, bo, bi, bp, crf, bd)

      (* <  16>< 16><  0><------bd---->00   bdnz *)         
      | (16, 0) ->
         let ctr = ctr_op ~mode:RW in
         CBranchDecrementNotZero (PWR, false, bo, bi, BPNone, bd, ctr)

      (* <  16>< 18><  0><------bd---->00   bdz *)                  
      | (18, 0) ->
         let ctr = ctr_op ~mode:RW in
         CBranchDecrementZero (PWR, false, bo, bi, BPNone, bd, ctr)

      | _ ->
         BranchConditional (PWR, false, bo, bi, bd))

  | 1 ->
     (* <  16>< bo>< bi><------bd---->01   bcl *)
     let btea = iaddr#add_int bdval in
     let bd = pwr_absolute_op btea RD in
     (match (bo, bi) with
      (* <  16>< 20>< 31><------bd---->01   bcl *)
      | (20, 31) ->
         BranchConditionalLink (PWR, false, bo, bi, bd)

      | _ ->
         NotRecognized
           ("bcl:" ^ (string_of_int bo) ^ "_" ^ (string_of_int bi), instr))

  | _ ->
     NotRecognized
        ("bcalr:" ^ (string_of_int bo) ^ "_" ^ (string_of_int bi), instr)


let parse_opcode_18
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let li = b 6 29 in
  let li = if (b 6 6) = 1 then li - e24 else li in
  
  match (b 30 31) with
  | 0 ->
     (* <  18><----------LI---------->00  b *)
     let btea = iaddr#add_int (4 * li) in
     let tgt = pwr_absolute_op btea RD in
     (* b LI *)
     Branch (PWR, tgt)

  | 1 ->
  (* <  18><----------LI---------->01   bl *)
     let btea = iaddr#add_int (4 * li) in
     let lr = lr_op ~mode:WR in
     let tgt = pwr_absolute_op btea RD in
     (* bl LI *)
     BranchLink (PWR, tgt, lr)

  | p ->
     NotRecognized ("Branch:" ^ (string_of_int p), instr)
    

let parse_opcode_19
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let opc = b 21 30 in

  
  match opc with
  | 16 ->
     let lr = lr_op ~mode:RD in
     let bo = b 6 10 in
     let bi = b 11 15 in
     let bh = b 19 20 in

     if (b 31 31) = 0 then
     
       (match (bo, bi, bh) with
        (* <  19><  4><c>00///00<----16-->0    bgelr *)
        | (4, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28), 0) ->
           let crf = crbi_op bi ~mode:RD in
           (* bgelr cr *)
           CBranchGreaterEqualLinkRegister (PWR, bo, bi, bh, BPNone, crf, lr)

        (* <  19><  4><c>01///00<----16-->0    blelr *)
        | (4, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29), 0) ->           
           let crf = crbi_op bi ~mode:RD in
           (* blelr cr *)
           CBranchLessEqualLinkRegister (PWR, bo, bi, bh, BPNone, crf, lr)

        (* <  19><  4><c>10///00<----16-->0    bnelr *)
        | (4, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30), 0) ->           
           let crf = crbi_op bi ~mode:RD in
           (* bnelr cr *)
           CBranchNotEqualLinkRegister (PWR, bo, bi, bh, BPNone, crf, lr)

        (* <  19><  5><c>10///00<----16-->0    bnelr *)
        | (5, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30), 0) ->           
           let crf = crbi_op bi ~mode:RD in
           (* bnelr cr *)
           CBranchNotEqualLinkRegister (PWR, bo, bi, bh, BPPlus 1, crf, lr)

        (* <  19>< 12><c>00///00<----16-->0    bltlr *)
        | (12, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28), 0) ->
           let crf = crbi_op bi ~mode:RD in
           (* bltlr cr *)
           CBranchLessThanLinkRegister (PWR, bo, bi, bh, BPNone, crf, lr)

        (* <  19>< 12><c>01///00<----16-->0    bgtlr *)
        | (12, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29), 0) ->           
           let crf = crbi_op bi ~mode:RD in
           (* bgtlr cr *)
           CBranchGreaterThanLinkRegister (PWR, bo, bi, bh, BPNone, crf, lr)

        (* <  19>< 12><c>10///00<----16-->0    beqlr *)
        | (12, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30), 0) ->           
           let crf = crbi_op bi ~mode:RD in
           (* beqlr cr *)
           CBranchEqualLinkRegister (PWR, bo, bi, bh, BPNone, crf, lr)

        (* <  19>< 13><c>00///00<----16-->0    bltlr+ *)
        | (13, (0 | 4 | 8 | 12 | 16 | 20 | 24 | 28), 0) ->
           let crf = crbi_op bi ~mode:RD in
           (* bltlr+ cr *)
           CBranchLessThanLinkRegister (PWR, bo, bi, bh, BPPlus 1, crf, lr)

        (* <  19>< 13><c>01///00<----16-->0    bgtlr+ *)
        | (13, (1 | 5 | 9 | 13 | 17 | 21 | 25 | 29), 0) ->           
           let crf = crbi_op bi ~mode:RD in
           (* bgtlr+ cr *)
           CBranchGreaterThanLinkRegister (PWR, bo, bi, bh, BPPlus 1, crf, lr)

        (* <  19>< 13><c>10///00<----16-->0    beqlr+ *)
        | (13, (2 | 6 | 10 | 14 | 18 | 22 | 26 | 30), 0) ->           
           let crf = crbi_op bi ~mode:RD in
           (* beqlr+ cr *)
           CBranchEqualLinkRegister (PWR, bo, bi, bh, BPPlus 1, crf, lr)
           
        (* <  19>< 20><  0>///00<----16-->0   blr *)         
        | (20, 0, 0) ->
           BranchLinkRegister (PWR, lr)
        | _ ->  
           BranchConditionalLinkRegister (PWR, bo, bi, bh, lr))

     else
       BranchConditionalLinkRegisterLink (PWR, bo, bi, bh, lr)

  (* <  19><crd><cra><cra><----33-->/    crnot *)
  | 33 when (b 11 15) = (b 16 20) ->
     let crd = crbit_op (b 6 10) ~mode:WR in
     let cra = crbit_op (b 11 15) ~mode:RD in
     (* crnot *)
     ConditionRegisterNot (PWR, crd, cra)

  (* <  19>///////////////<----38-->0   rfmci *)
  | 38 ->
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:WR in
     let mcsr0 = pwr_special_register_op ~reg:PowerMCSRR0 ~mode:RD in
     let mcsr1 = pwr_special_register_op ~reg:PowerMCSRR1 ~mode:RD in
     (* rfmci *)
     ReturnFromMachineCheckInterrupt (PWR, msr, mcsr0, mcsr1)

  (* <  19>///////////////<----39-->/   rfdi *)
  | 39 ->
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:WR in
     let dsr0 = pwr_special_register_op ~reg:PowerDSRR0 ~mode:RD in
     let dsr1 = pwr_special_register_op ~reg:PowerDSRR1 ~mode:RD in
     (* rfdi *)
     ReturnFromDebugInterrupt (PWR, msr, dsr0, dsr1)

  (* <  19>///////////////<----50-->/   rfi *)
  | 50 ->
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:WR in
     let sr0 = pwr_special_register_op ~reg:PowerSRR0 ~mode:RD in
     let sr1 = pwr_special_register_op ~reg:PowerSRR1 ~mode:RD in
     (* rfi *)
     ReturnFromInterrupt (PWR, msr, sr0, sr1)

  (* <  19>///////////////<---150-->/   isync *)
  | 150 ->
     (* isync *)
     InstructionSynchronize PWR

  (* <  19>< 20><  0>///00<---528-->0   bctr *)
  | 528 ->
     let ctr = ctr_op ~mode:RD in
     (* bctr *)
     BranchCountRegister (PWR, ctr)

  | _ ->
     NotRecognized ("parse_opcode_19:" ^ (string_of_int opc), instr)


let parse_opcode_20
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in

  (* <  20>< rs>< ra>< sh>< mb>< me>c   rlwimi/insrwi *)
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
    InsertRightWordImmediate (PWR, false, ra ~mode:WR, rs ~mode:RD, n, mb, cr)
  else
    NotRecognized ("InsertRightWordImmediate", instr)


let parse_opcode_21
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let rs = pwr_gp_register_op ~index:(b 6 10) in
  let ra = pwr_gp_register_op ~index:(b 11 15) in
  let cr0 = cr0_op ~mode:WR in
  let rc = (b 31 31) = 1 in
  let sh = b 16 20 in
  let mb = b 21 25 in
  let me = b 26 30 in

  if sh = 0 && mb = 0 then
    (* <  21>< rs>< ra><  0>< 0>< me>c   clrrwi *)
    let n = 31 - me in
    let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical n) in
    (* clrrwi rA,rS,n *)
    ClearRightWordImmediate (PWR, rc, ra ~mode:WR, rs ~mode:RD, n, cr0)    

  else if sh = 0 && me = 31 then
    (* <  21>< rs>< ra><  0>< mb>< 31>c   clrlwi *)
    let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical mb) in
    (* clrlwi rA, rS, n *)
    ClearLeftWordImmediate (PWR, rc, ra ~mode:WR, rs ~mode:RD, n)

  else if mb = 0 && me = 31 - sh then
    (* <  21>< rs>< ra>< sh><  0>< me>c   slwi *)
    let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical sh) in
    (* slwi rA,rS,n *)
    ShiftLeftWordImmediate (PWR, rc, ra ~mode:WR, rs ~mode:RD, n, cr0)

  else if me = 31 then
    (* <  21>< rs>< ra>< sh>< mb>< 31>c   extrwi *)        
     let n = 32 - mb in
     let b = (sh + mb) - 32 in
     let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical n) in
     let b = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical b) in
     (* extrwi rA,rS,n,b *)   
     ExtractRightJustifyWordImmediate
       (PWR, rc, ra ~mode:WR, rs ~mode:RD, n, b, cr0)

  else if me = 31 - sh then
    let n = sh in
    let b = mb + sh in
    let n = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical n) in
    let b = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical b) in
    (* clrlslwi rA,rS,b,n *)
    ClearLeftShiftLeftWordImmediate
      (PWR, rc, ra ~mode:WR, rs ~mode:RD, b, n, cr0)

  else
    (* <  21>< rs>< ra>< sh>< mb>< me>c *)
    let sh = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical sh) in
    let mb = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical mb) in
    let me = pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical me) in
    (* rlwinm rA,rS,SH,MB,ME *)
    RotateLeftWordImmediateAndMask
      (PWR, rc, ra ~mode:WR, rs ~mode:RD, sh, mb, me, cr0)


let parse_opcode_23
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let rs = pwr_gp_register_op ~index:(b 6 10) in
  let ra = pwr_gp_register_op ~index:(b 11 15) in
  let rb = pwr_gp_register_op ~index:(b 16 20) in
  let cr0 = cr0_op ~mode:WR in
  let rc = (b 31 31) = 1 in
  let mb = b 21 25 in
  let me = b 26 30 in

  if mb = 0 && me = 31 then
    (* <  23>< rs>< ra>< rb><  0>< 31>c   rotlw *)
    (* rotlw rA,rS,rB *)
    RotateLeftWord (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr0)

  else
    NotRecognized ("RotateLeftWordAndMask", instr)


let parse_opcode_24_29
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let shifted = (b 5 5) = 1 in
  let rs = pwr_gp_register_op ~index:(b 6 10) in
  let ra = pwr_gp_register_op ~index:(b 11 15) in
  let uimm =
    pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical (b 16 31)) in
  let cr = cr0_op ~mode:NT in
  let crw = cr0_op ~mode:WR in

  if (b 0 4) = 12 then
    (* <  24>< rs>< ra><------uimm------>   ori *)
    (* <  25>< rs>< ra><------uimm------>   oris *)
    (* ori rA,rS,UIMM *)
    OrImmediate (PWR, false, shifted, false, ra ~mode:WR, rs ~mode:RD, uimm, cr)

  else if (b 0 4) = 13 then
    (* <  26>< rs>< ra><------uimm------>   xori *)
    (* <  27>< rs>< ra><------uimm------>   xoris *)
    XorImmediate (PWR, false, shifted, ra ~mode:WR, rs ~mode:RD, uimm, cr)

  else
    (* <  28>< rs>< ra><------uimm------>   andi. *)
    (* <  29>< rs>< ra><------uimm------>   andis. *)
    AndImmediate (PWR, shifted, false, true, ra ~mode:WR, rs ~mode:RD, uimm, crw)

    
let parse_opcode_31
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let opc = b 22 30 in
  let b1 = b 21 21 in
  match (b1, opc) with

  (* < 7>11<<c>/0< ra>< rb><----0-->/   cmpw *)
  | (0, 0) when (b 10 10) = 0 ->
     let crd = crf_op (b 6 8) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     (* cmpw cfrD,rA,rB *)
     CompareWord (PWR, crd ~mode:WR, ra ~mode:RD, rb ~mode:RD)

  (* < 7>11< rd>< ra>< rb>E<----8-->c   subfc *)
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
     
  (* < 7>11< rd>< ra>< rb>E<---10-->c   addc *)
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
     
  (* < 7>11< rd>< ra>< rb>/<---11-->c   mulhwu *)
  | (0, 11) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let rc = (b 31 31) = 1 in
     let cr = cr0_op ~mode:WR in
     (* mulhwu rD,rA,rB *)
     MultiplyHighWordUnsigned
       (PWR, rc, rd ~mode:WR, ra ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11< rd>< ra>< rb>0<---15-->/   isellt (simplified) *)
  | (0, 15) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op_convert (b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:RD in
     (* isellt rD,rA,rB *)
     IntegerSelectLessThan (PWR, rd ~mode:WR, ra, rb ~mode:RD, cr)
     
  (* < 7>11< rd>0/////////0<---19-->/   mfcr *)
  | (0, 19) when (b 11 11) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let cr = pwr_special_register_op ~reg:PowerCR ~mode:RD in
     (* mfcr rD *)
     MoveFromConditionRegister (PWR, rd ~mode:WR, cr)
    
  (* < 7>11< rd>< ra>< rb>0<---23-->/   lwzx *)
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
     
  (* < 7>11< rs>< ra>< rb>0<---24-->c   slw *)
  | (0, 24) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let rc = (b 31 31) = 1 in
     let cr0 = cr0_op ~mode:WR in
     (* slw rA,rS,rB *)
     ShiftLeftWord (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr0)

  (* < 7>11< rs>< ra>/////0<---26-->c   cntlzw *)
  | (0, 26) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr0 = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* cntlzw ra,rs) *)
     CountLeadingZerosWord (PWR, rc, ra ~mode:WR, rs ~mode:RD, cr0)
     
  (* < 7>11< rs>< ra>< rb>0<---28-->c   and *)
  | (0, 28) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* and rA,rS,rB *)
     And (PWR, rc, ra ~mode:WR, rs ~mode:WR, rb ~mode:WR, cr)
     
  (* < 7>11<c>/0< ra>< rb>0<---32-->/   cmplw (simplified mnemonic) *)
  | (0, 32) ->
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let crfd = crf_op (b 6 8) ~mode:WR in
     (* cmplw crfd, rA, rB *)
     CompareLogical (PWR, crfd, ra ~mode:RD, rb ~mode:RD)
    
  (* < 7>11< rd>< ra>< rb>E<---40-->c   subf *)
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

  (* < 7>11< rs>< ra>< rb>0<---60-->c   andc *)
  | (0, 60) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* andc rA,rS,rB *)
     AndComplement (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr)
     
  (* < 7>11< rd>< ra>< rb>0<---79-->/   iseleq (simplified *)
  | (0, 79) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op_convert (b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:RD in
     (* iseleq rD,rA,rB *)
     IntegerSelectEqual (PWR, rd ~mode:WR, ra, rb ~mode:RD, cr)
     
  (* < 7>11< rd>//////////0<---83-->/   mfmsr *)
  | (0, 83) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:RD in
     (* mfmsr rD *)
     MoveFromMachineStateRegister (PWR, rd ~mode:WR, msr)

  (* < 7>11< rd>< ra>< rb>0<---87-->/   lbzx *)
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

  (* < 7>11< rd>< ra>/////E<--104-->c   neg *)
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

  (* < 7>11< rs>< ra>< rb>0<--124-->c   not *)
  | (0, 124) when (b 6 10) = (b 16 20) ->
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* not rA,rB *)
     ComplementRegister (PWR, rc, ra ~mode:WR, rb ~mode:RD, cr)

  (* < 7>11< rd>< ra>< rb>E<--136-->c   subfe *)
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
     
  (* < 7>11< rd>< ra>< rb>E<--138-->c   adde *)
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
     
  (* < 7>11< rs>0<15><15>/0<--144-->/   mtcr (simplified) *)
  | (0, 144) when (b 11 11) = 0 && (b 12 19) = 255 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let cr = pwr_special_register_op ~reg:PowerCR ~mode:WR in
     (* mtcr rS *)
     MoveToConditionRegister (PWR, cr, rs ~mode:RD)

  (* < 7>11< rs>0<--crm->/0<--144-->/   mtcrf *)
  | (0, 144) when (b 11 11) = 0 ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let crm = b 12 19 in
     let crmop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical crm) in
     (* mtcrf CRM,rS *)
     let crfs = pwr_cr_field_list crm in
     MoveToConditionRegisterFields (PWR, crmop, rs ~mode:RD, crfs ~mode:WR)

  (* < 7>11<rs><.........>0<--146-->/  mtmsr *)
  | (0, 146) ->
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let msr = pwr_special_register_op ~reg:PowerMSR in
     (* mtmsr RS *)
     MoveToMachineStateRegister (PWR, msr ~mode:WR, rx ~mode:RD)

  (* < 7>11< rs>< ra>< rb>0<--151-->/   stwx *)
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
     
  (* < 7>11//////////E////0<--163-->/   wrteei *)
  | (0, 163) ->
     let msr = pwr_special_register_op ~reg:PowerMSR ~mode:WR in
     let enable = (b 16 16) = 1 in
     (* wrteei E *)
     WriteMSRExternalEnableImmediate (PWR, enable, msr)

  (* < 7>11< rd>< ra>/////E<--200-->c   subfze *)
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
     
  (* < 7>11< rd>< ra>/////E<--202-->c   addze *)
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

  (* < 7>11< rs>< ra>< rb>0<--215-->/   stbx *)
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

  (* < 7>11< rd>< ra>/////E<--234-->c   addme *)
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

  (* < 7>11< rd>< ra>< rb>E<--235-->c   mullw *)
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
     
  (* < 7>11< rd>< ra>< rb>E<--266-->c   add *)
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
     
  (* < 7>11< rs>< ra>< rb>0<--316-->c   xor *)
  | (0, 316) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* xor rA,rS,rB *)
     Xor (PWR, rc, ra ~mode:WR, rs ~mode:WR, rb ~mode:WR, cr)
     
  (* < 7>11< rd>< 0 >< 1 >0<--339-->/   mfxer (simplified) *)
  | (0, 339) when (b 11 15) = 1 && (b 16 20) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let xer = pwr_special_register_op ~reg:PowerXER ~mode:RD in
     (* mfxer rD *)
     MoveFromExceptionRegister (PWR, rd ~mode:WR, xer)
     
  (* < 7>11< rd><  9><  0>0<--339-->/   mfctr (simplified) *)
  | (0, 339) when (b 11 15) = 9 && (b 16 20) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ctr = ctr_op ~mode:RD in
     (* mfctr rd *)
     MoveFromCountRegister (PWR, rd ~mode:WR, ctr)
     
  (* < 7>11< rd><  8><  0>0<--339-->/   mflr (simplified) *)
  | (0, 339) when (b 11 15) = 8 && (b 16 20) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let lr = lr_op ~mode:RD in
     (* mflr rd *)
     MoveFromLinkRegister (PWR, rd ~mode:WR, lr)
     
  (* < 7>11< rd><spr><spr>0<--339-->/   mfspr *)
  | (0, 339) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let spr = ((b 16 20) lsl 5) + (b 11 15) in
     let spr =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical spr) in
     (* mfspr rD, sprn *)
     MoveFromSpecialPurposeRegister (PWR, rd ~mode:WR, spr)

  (* < 7>11< rS>< rA>< rB>0<--444-->c   mr *)
  | (0, 444) when (b 6 10) = (b 16 20) ->
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let rc = (b 31 31) = 1 in
     (* mr rA,rS *)
     MoveRegister (PWR, rc, ra ~mode:WR, rs ~mode:RD)

  (* < 7>11< rs>< ra>< rb>0<--444-->c   or *)
  | (0, 444) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode: WR in
     let rc = (b 31 31) = 1 in
     (* or rA,rS,rB *)
     Or (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11< rd>< ra>< rb>E<--459-->c   divwu *)
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

  (* < 7>11< rs><  1><  0>0<--467-->/   mtxer *)
  | (0, 467) when (b 11 15) = 1 && (b 16 20) = 0 ->
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let xer = xer_op ~mode:WR in
     (* mtxer rS *)
     MoveToExceptionRegister (PWR, xer, rx ~mode:RD)
     
  (* < 7>11< rs><  8><  0>0<--467-->/   mtlr *)
  | (0, 467) when (b 11 15) = 8 && (b 16 20) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let lr = lr_op ~mode:WR in
     (* mtlr rS *)
     MoveToLinkRegister (PWR, lr, rd ~mode:RD)

  (* < 7>11< rs><  9><  0>0<--467-->/   mtctr *)
  | (0, 467) when (b 11 15) = 9 && (b 16 20) = 0 ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ctr = ctr_op ~mode:WR in
     (* mtctr rS *)
     MoveToCountRegister (PWR, ctr, rd ~mode:RD)
     
  (* < 7>11< rs><spr><spr>0<--467-->/   mtspr *)    
  | (0, 467) ->
     let sprn = ((b 16 20) lsl 5) + (b 11 15) in
     let rx = pwr_gp_register_op ~index:(b 6 10) in
     let immop =
       pwr_immediate_op ~signed:false ~size:4 ~imm:(mkNumerical sprn) in
     (* mtspr sprN, rS *)
     MoveToSpecialPurposeRegister(PWR, immop, rx ~mode:WR)

  (* < 7>11< rd>< ra>< rb>E<--491-->c   divw *)
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
     
  (* < 7>11< rs>< ra>< rb>1<---24-->c   srw *)
  | (1, 24) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* srw rA,rS,rB *)
     ShiftRightWord (PWR, rc, ra ~mode:WR, rs ~mode:RD, rb ~mode:RD, cr)

  (* < 7>11< rs>< ra>< rb>1<--280-->c   sraw *)
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
     
  (* < 7>11< rs>< ra>< sh>1<--312-->c   srawi *)
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
     
  (* < 7>11< mo>//////////1<--342-->/   eieio *)
  | (1, 342) ->
     let mo = b 6 10 in
     let mo = pwr_immediate_op ~signed:false ~size:1 ~imm:(mkNumerical mo) in
     (* mbar *)
     EnforceInOrderExecutionIO (PWR, mo)

  (* < 7>11< rs>< ra>/////1<--410-->c   extsh *)
  | (1, 410) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let cr = cr0_op ~mode:WR in
     let rc = (b 31 31) = 1 in
     (* extsh rA,rS *)
     ExtendSignHalfword (PWR, rc, ra ~mode:WR, rs ~mode:RD, cr)
     
  (* < 7>11< rs>< ra>/////1<--442-->c   extsb *)
  | (1, 442) ->
     let rs = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op ~index:(b 11 15) in
     let rc = (b 31 31) = 1 in
     let cr = cr0_op ~mode:WR in
     (* extsb rA,rS *)
     ExtendSignByte (PWR, rc, ra ~mode:WR, rs ~mode:RD, cr)

  (* < 7>11< rd>< ra>< rb>1<--463-->/   isel (4*cr7+eq) *)
  | (1, (399 | 463)) ->
     let rd = pwr_gp_register_op ~index:(b 6 10) in
     let ra = pwr_gp_register_op_convert (b 11 15) in
     let rb = pwr_gp_register_op ~index:(b 16 20) in
     let crb = crbit_op (b 21 25) ~mode:RD in
     (* isel rD,rA,rB,crb *)
     IntegerSelect (PWR, rd ~mode:WR, ra, rb ~mode:RD, crb)

  (* < 7>110//////////////1<--466-->/   tlbwe *)
  | (1, 466) when (b 6 6) = 0 ->
     (* tlbwe *)
     TLBWriteEntry PWR
     
  | _ ->
     NotRecognized ("parse_opcode_31:" ^ (string_of_int opc), instr)


let parse_load_opcodes
      (opc: int)
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let rd = pwr_gp_register_op ~index:(b 6 10) ~mode:WR in
  let ra = pwr_gp_register_op ~index:(b 11 15) ~mode:RD in
  let offset = (b 16 31) in
  let offset = if (b 16 16) = 1 then offset - e16 else offset in
  let offset = mkNumerical offset in
  let mem = pwr_indirect_register_op ~basegpr:(b 11 15) ~offset ~mode:RD in
  
  match opc with

  (* <  32>< rd>< ra><------D------->   lwz *)
  | 32 ->
     (* lwz rD,D(rA) *)
     LoadWordZero (PWR, false, rd, ra, mem)

  (* <  33>< rd>< ra><------D------->   lwzu *)
  | 33 ->
     (* lwzu rD,D(rA) *)
     LoadWordZero (PWR, true, rd, ra, mem)

  (* <  34>< rd>< ra><------D------->   lbz *)
  | 34 ->
     (* lbz rD,D(rA) *)
     LoadByteZero (PWR, false, rd, ra, mem)

  (* <  35>< rd>< ra><------D------->   lbzu *)
  | 35 ->
     (* lbzu rD,D(rA) *)
     LoadByteZero (PWR, true, rd, ra, mem)

  (* <  40>< rd>< ra><------D------->   lhz *)
  | 40 ->
     (* lhz rD,D(rA) *)
     LoadHalfwordZero (PWR, false, rd, ra, mem)

  (* <  41>< rd>< ra><------D------->   lhzu *)
  | 41 ->
     (* lhzu rD,D(rA) *)
     LoadHalfwordZero (PWR, true, rd, ra, mem)

  (* <  46>< rd>< ra><------D------->   lmw *)    
  | 46 ->
     (* lmw rD,D(rA) *)
     LoadMultipleWord (PWR, rd, ra, mem)

  | _ ->
     NotRecognized ("Load opcodes:" ^ (string_of_int opc), instr)


let parse_store_opcodes
      (opc: int)
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  let b = instr#get_reverse_segval 32 in
  let rs = pwr_gp_register_op ~index:(b 6 10) ~mode:RD in
  let ra = pwr_gp_register_op ~index:(b 11 15) ~mode:RD in
  let offset = (b 16 31) in
  let offset = if (b 16 16) = 1 then offset - e16 else offset in
  let offset = mkNumerical offset in
  let mem = pwr_indirect_register_op ~basegpr:(b 11 15) ~offset ~mode:WR in

  match opc with

  (* <  36>< rs>< ra><------D------->   stw *)
  | 36 ->
     (* stw rS,D(rA) *)
     StoreWord (PWR, false, rs, ra, mem)

  (* <  37>< rs>< ra><------D------->   stwu *)    
  | 37 ->
     (* stwu rS,D(rA) *)
     StoreWord (PWR, true, rs, ra, mem)

  (* <  38>< rs>< ra><------D------->   stb *)
  | 38 ->
     (* stb rS,D(rA) *)
     StoreByte (PWR, false, rs, ra, mem)
    
  (* <  39>< rs>< ra><------D------->   stbu *)
  | 39 ->
     (* stbu rS,D(rA) *)
     StoreByte (PWR, true, rs, ra, mem)

  (* <  44>< rs>< ra><------D------->   sth *)
  | 44 ->
     (* sth rS,D(rA) *)
     StoreHalfword (PWR, false, rs, ra, mem)

  (* <  45>< rs>< ra><------D------->   sthu *)
  | 45 ->
     (* sthu rS,D(rA) *)
     StoreHalfword (PWR, true, rs, ra, mem)

  (* <  47>< rs>< ra><------D------->   stmw *)
  | 47 ->
     (* stmw rS,D(rA) *)
     StoreMultipleWord (PWR, rs, ra, mem)

  | _ ->
     NotRecognized ("Store opcodes:" ^ (string_of_int opc), instr)

    
let parse_pwr_opcode
      (ch: pushback_stream_int)
      (iaddr: doubleword_int)
      (instr: doubleword_int): pwr_opcode_t =
  if instr#equal wordzero then
    OpcodeIllegal 0
  else
    let b = instr#get_reverse_segval 32 in
    let opc = b 0 5 in
    match opc with
    | 1 | 5 | 6 | 57 | 60 | 61 -> OpcodeIllegal opc
    | 4 -> parse_opcode_4 ch iaddr instr
    | 7 -> parse_opcode_7 ch iaddr instr
    | 8 -> parse_opcode_8 ch iaddr instr
    | 10 -> parse_opcode_10 ch iaddr instr
    | 11 -> parse_opcode_11 ch iaddr instr
    | 12 | 13 -> parse_opcode_12_13 ch iaddr instr
    | 14 | 15 -> parse_opcode_14_15 ch iaddr instr
    | 16 -> parse_opcode_16 ch iaddr instr
    | 18 -> parse_opcode_18 ch iaddr instr
    | 19 -> parse_opcode_19 ch iaddr instr
    | 20 -> parse_opcode_20 ch iaddr instr
    | 21 -> parse_opcode_21 ch iaddr instr
    | 23 -> parse_opcode_23 ch iaddr instr
    | 24 | 25 | 26 | 27 | 28 | 29 -> parse_opcode_24_29 ch iaddr instr
    | 31 -> parse_opcode_31 ch iaddr instr
    | 32 | 33 | 34 | 35 | 40 | 41 | 42 |43 | 46 ->
       parse_load_opcodes opc ch iaddr instr
    | 36 | 37 | 38 | 39 | 44 | 45 | 47 ->
       parse_store_opcodes opc ch iaddr instr
    | _ ->
       NotRecognized ("parse_opcode:" ^ (string_of_int opc), instr)

    
let disassemble_pwr_instruction
      (ch: pushback_stream_int) (iaddr: doubleword_int) (instr: doubleword_int) =
  try
    parse_pwr_opcode ch iaddr instr
  with
  | BCH_failure p ->
     begin
       ch_error_log#add
         "disassembly - power"
         (LBLOCK [
              STR "Error in disassembling power: ";
              iaddr#toPretty;
              STR ": ";
              p]);
       raise (BCH_failure p)
     end

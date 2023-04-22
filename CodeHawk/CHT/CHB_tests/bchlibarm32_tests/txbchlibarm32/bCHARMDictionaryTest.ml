(* =============================================================================
   CodeHawk Unit Testing Framework 
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs LLC

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


module TS = TCHTestSuite
module ARMA = TCHBchlibarm32Assertion

(* chlib *)
open CHNumerical

(* chutil *)
open CHFileIO
open CHXmlDocument

(* bchlib *)
open BCHDictionary
open BCHDoubleword
open BCHImmediate
open BCHLibTypes
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMDictionary
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMPseudocode
open BCHARMSumTypeSerializer
open BCHARMTypes

module B = Big_int_Z

module G = TCHGenerator
module ARMG = TCHBchlibarm32Generator

module TR = CHTraceResult


let testname = "bCHARMDictionaryTest"
let lastupdated = "2023-04-22"

let e8 = 256
let e16 = e8 * e8
let e24 = e16 * e8


let get_bch_root (info:string):xml_element_int =
  let root = xmlElement "codehawk-binary-analyzer" in
  let hNode = xmlElement "header" in
  begin
    hNode#setAttribute "info" info;
    hNode#setAttribute "time" (current_time_to_string ());
    root#appendChildren [hNode];
    root
  end
                
let save_bdictionary filename =
  let doc = xmlDocument () in
  let root = get_bch_root "bdictionary" in
  let fnode = xmlElement  "bdictionary" in
  begin
    bdictionary#write_xml fnode;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end
                

let arm_opcode_tests () =
  begin
    TS.new_testsuite (testname ^ "_arm_opcode_tests") lastupdated;
    system_info#set_elf_is_code_address wordzero wordmax;
    let pc_addr = TR.tget_ok (string_to_doubleword "0x400000") in
    let prngstate = G.make_random_seed 0 in
    let int15 = G.make_int 0 15 in
    let boolvalue () = (fst G.bool) prngstate in
    let intvalue ?(min=0) v = (fst (G.make_int min v)) prngstate in
    let select_int l = (fst (G.select_int l)) prngstate in

    (* arm_operand_int generators *)
    let armreg_op mode = (fst (ARMG.arm_reg_op int15 mode)) prngstate in
    let armimmshiftreg_op mode =
      (fst (ARMG.arm_imm_shift_reg_op int15 mode)) prngstate in
    let armrotatedreg_op mode =
      (fst (ARMG.arm_rotated_reg_op int15 mode)) prngstate in
    let armregbitsequence_op mode =
      (fst (ARMG.arm_reg_bit_sequence_op int15 mode)) prngstate in
    let armreglist_op mode = (fst (ARMG.arm_reglist_op mode)) prngstate in
    let armxsinglereg_op mode = (fst (ARMG.arm_xsingle_reg_op mode)) prngstate in
    let armdualxsinglereg_op mode =
      (fst (ARMG.arm_dual_xsingle_reg_op mode)) prngstate in
    let armxdoublereg_op mode = (fst (ARMG.arm_xdouble_reg_op mode)) prngstate in
    let armxquadreg_op mode = (fst (ARMG.arm_xquad_reg_op mode)) prngstate in
    let armxsinglereglist_op mode =
      (fst (ARMG.arm_xsingle_reglist_op mode)) prngstate in
    let armxdoublereglist_op mode =
      (fst (ARMG.arm_xdouble_reglist_op mode)) prngstate in
    let armvfp_su_dt () = (fst ARMG.arm_vfp_signed_unsigned_int_dt) prngstate in
    let armvfp_op (dp: bool) (mode: arm_operand_mode_t) =
      (fst (ARMG.arm_vfp_op dp mode)) prngstate in
    let literal_op imm = (fst (ARMG.arm_literal_op pc_addr imm)) prngstate in
    let absolute_op mode = (fst (ARMG.arm_absolute_op mode)) prngstate in
    let armimmoffsetaddress_op
          (reg: arm_reg_t) (imm: int) (mode: arm_operand_mode_t) =
      (fst (ARMG.arm_imm_offset_address_op reg imm mode)) prngstate in
    let armindexoffsetaddress_op
          (basereg: arm_reg_t) (indexreg: arm_reg_t) (mode: arm_operand_mode_t) =
      (fst (ARMG.arm_index_offset_address_op basereg indexreg mode)) prngstate in
    let armdualindexoffsetaddresses_op
          (basereg: arm_reg_t) (indexreg: arm_reg_t) (mode: arm_operand_mode_t) =
      (fst
         (ARMG.arm_dual_index_offset_addresses_op
            basereg indexreg mode)) prngstate in
    let armshiftedindexoffsetaddress_op
          (basereg: arm_reg_t) (indexreg: arm_reg_t) (mode: arm_operand_mode_t) =
      (fst
         (ARMG.arm_shifted_index_offset_address_op
            basereg indexreg mode)) prngstate in

    (* other generators *)
    let armreg () = (fst (ARMG.arm_reg int15)) prngstate in
    let lsb_width_msb () = (fst (ARMG.lsb_width_msb)) prngstate in
    let cc () = (fst ARMG.arm_opcode_cc) prngstate in
    let dmb_op () = (fst ARMG.dmb_option_operand) prngstate in
    
    let armd = arm_dictionary in
    let doc = xmlDocument () in
    let root = xmlElement "codehawk-binary-analysis" in
    let tNode = xmlElement "arm-opcode-tests" in
    let _ = tNode#setAttribute "time" (current_time_to_string ()) in
    let _ = root#appendChildren [tNode] in
    let fNode = xmlElement "arm-dictionary" in
    let nNode = xmlElement "arm_opcode_strings" in
    let _ = root#appendChildren [nNode; fNode] in

    let index_opc (opc: arm_opcode_t) =
      let index = armd#index_arm_opcode opc in
      let opcnode = xmlElement "opc" in
      begin
        opcnode#setIntAttribute "iopc" index;
        opcnode#setAttribute "opc" (arm_opcode_to_string opc);
        nNode#appendChildren [opcnode];
        armd#retrieve_arm_opcode_key index
      end in
    let index_check_opc (opc: arm_opcode_t) (mnem: string) (cnt: int) =
      let (tags, args) = index_opc opc in
      ARMA.equal_dictionary_key
        ~expected:([mnem], cnt)
        ~received:(tags, args)
        () in
    let index_check_opc_c
          (opc: arm_opcode_t) (c: arm_opcode_cc_t) (mnem: string) (cnt: int) =
      let (tags, args) = index_opc opc in
      let ccode = arm_opcode_cc_mfts#ts c in
      ARMA.equal_dictionary_key
        ~expected:([mnem; ccode], cnt)
        ~received:(tags, args)
        () in
    let filename = "arm_opcodes.xml" in

    TS.add_simple_test
      ~title:"Add (register)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = Add (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "ADD" 5);

    TS.add_simple_test
      ~title:"AddCarry (register)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = AddCarry (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "ADC" 5);

    TS.add_simple_test
      ~title:"Address"
      (fun () ->
        let rd = armreg_op WR in
        let label = absolute_op RD in
        let c = cc () in
        let opc = Adr (c, rd, label) in
        index_check_opc_c opc c "ADR" 2);

    TS.add_simple_test
      ~title:"AESInverseMixColumns"
      (fun () ->
        let dt = VfpSize 8 in
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = AESInverseMixColumns (c, dt, vd, vm) in
        index_check_opc_c opc c "AESIMC" 3);

    TS.add_simple_test
      ~title:"AESMixColumns"
      (fun () ->
        let dt = VfpSize 8 in
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = AESMixColumns (c, dt, vd, vm) in
        index_check_opc_c opc c "AESMC" 3);

    TS.add_simple_test
      ~title:"AESSingleRoundDecryption"
      (fun () ->
        let dt = VfpSize 8 in
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = AESSingleRoundDecryption (c, dt, vd, vm) in
        index_check_opc_c opc c "AESD" 3);

    TS.add_simple_test
      ~title:"AESSingleRoundEncryption"
      (fun () ->
        let dt = VfpSize 8 in
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = AESSingleRoundEncryption (c, dt, vd, vm) in
        index_check_opc_c opc c "AESE" 3);

    TS.add_simple_test
      ~title:"ArithmeticShiftRight"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = ArithmeticShiftRight (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "ASR" 5);

    TS.add_simple_test
      ~title:"BitFieldClear"
      (fun () ->
        let rd = armreg_op WR in
        let (lsb, width, msb) = lsb_width_msb () in
        let c = cc () in
        let opc = BitFieldClear (c, rd, lsb, width, msb) in
        index_check_opc_c opc c "BFC" 4);

    TS.add_simple_test
      ~title:"BitFieldInsert"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let (lsb, width, msb) = lsb_width_msb () in
        let c = cc () in
        let opc = BitFieldInsert (c, rd, rn, lsb, width, msb) in
        index_check_opc_c opc c "BFI" 5);

    TS.add_simple_test
      ~title:"BitwiseAnd (register)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = BitwiseAnd (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "AND" 5);

    TS.add_simple_test
      ~title:"BitwiseNot (register)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = BitwiseNot (setflags, c, rd, rm, tw) in
        index_check_opc_c opc c "MVN" 4);

    TS.add_simple_test
      ~title:"BitwiseOrNot (register)"
      (fun () ->
        let setflags = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = BitwiseOrNot (setflags, c, rd, rn, rm) in
        index_check_opc_c opc c "ORN" 4);

    TS.add_simple_test
      ~title:"BitwiseBitClear (imm-shifted)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = BitwiseBitClear (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "BIC" 5);

    TS.add_simple_test
      ~title:"BitwiseExclusiveOr (imm-shifted)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = BitwiseExclusiveOr (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "EOR" 5);

    TS.add_simple_test
      ~title:"BitwiseOr (imm-shifted)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = BitwiseOr (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "ORR" 5);

    TS.add_simple_test
      ~title:"Branch"
      (fun () ->
        let tw = boolvalue () in        
        let tgt = absolute_op RD in
        let c = cc () in
        let opc = Branch (c, tgt, tw) in
        index_check_opc_c opc c "B" 2);

    TS.add_simple_test
      ~title:"BranchExchange"
      (fun () ->
        let rm = armreg_op RD in
        let c = cc () in
        let opc = BranchExchange (c, rm) in
        index_check_opc_c opc c "BX" 1);

    TS.add_simple_test
      ~title:"BranchLink"
      (fun () ->
        let tgt = absolute_op RD in
        let c = cc () in
        let opc = BranchLink (c, tgt) in
        index_check_opc_c opc c "BL" 1);

    TS.add_simple_test
      ~title:"BranchLinkExchange"
      (fun () ->
        let tgt = absolute_op RD in
        let c = cc () in
        let opc = BranchLinkExchange (c, tgt) in
        index_check_opc_c opc c "BLX" 1);

    TS.add_simple_test
      ~title:"ByteReverseWord"
      (fun () ->
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = ByteReverseWord (c, rd, rm, tw) in
        index_check_opc_c opc c "REV" 3);

    TS.add_simple_test
      ~title:"ByteReversePackedHalfword"
      (fun () ->
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = ByteReversePackedHalfword (c, rd, rm, tw) in
        index_check_opc_c opc c "REV16" 3);

    TS.add_simple_test
      ~title:"Compare (register)"
      (fun () ->
        let tw = boolvalue () in
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = Compare (c, rn, rm, tw) in
        index_check_opc_c opc c "CMP" 3);

    TS.add_simple_test
      ~title:"CompareNegative (register)"
      (fun () ->
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = CompareNegative (c, rn, rm) in
        index_check_opc_c opc c "CMN" 2);

    TS.add_simple_test
      ~title:"CountLeadingZeros (register)"
      (fun () ->
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = CountLeadingZeros (c, rd, rm) in
        index_check_opc_c opc c "CLZ" 2);

    TS.add_simple_test
      ~title:"CompareBranchNonzero"
      (fun () ->
        let rn = armreg_op RD in
        let tgt = absolute_op RD in
        let opc = CompareBranchNonzero (rn, tgt) in
        index_check_opc opc "CBNZ" 2);

    TS.add_simple_test
      ~title:"CompareBranchZero"
      (fun () ->
        let rn = armreg_op RD in
        let tgt = absolute_op RD in
        let opc = CompareBranchZero (rn, tgt) in
        index_check_opc opc "CBZ" 2);

    TS.add_simple_test
      ~title:"DataMemoryBarrier"
      (fun () ->
        let op = dmb_op () in
        let c = cc () in
        let opc = DataMemoryBarrier (c, op) in
        index_check_opc_c opc c "DMB" 1);

    TS.add_simple_test
      ~title:"IfThen"
      (fun () ->
        let xyz = (fst ARMG.ifthen_xyz) prngstate in
        let c = cc () in
        let opc = IfThen (c, xyz) in
        let (tags, args) = index_opc opc in
        let ccode = arm_opcode_cc_mfts#ts c in
        let pccode = get_cond_mnemonic_extension c in
        let mnem = "IT" ^ xyz ^ " " ^ (pccode) in
        ARMA.equal_dictionary_key
          ~expected:([mnem; ccode; xyz], 0)
          ~received:(tags, args)
          ());

    TS.add_simple_test
      ~title:"FLoadMultipleIncrementAfter"
      (fun () ->
        let wback = boolvalue () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let xrl = armxdoublereglist_op WR in
        let rlen = List.length xrl#get_extension_register_op_list in
        let mem = mk_arm_mem_multiple_op ~size:8 rnreg rlen RD in
        let c = cc () in
        let opc = FLoadMultipleIncrementAfter (wback, c, rn, xrl, mem) in
        index_check_opc_c opc c "FLDMIAX" 4);

    TS.add_simple_test
      ~title:"FStoreMultipleIncrementAfter"
      (fun () ->
        let wback = boolvalue () in
        let rn = intvalue 13 in
        let rnreg = get_arm_reg rn in
        let rnop = arm_register_op rnreg WR in
        let xrl = armxdoublereglist_op RD in
        let rlen = List.length xrl#get_extension_register_op_list in
        let mem = mk_arm_mem_multiple_op ~size:8 rnreg rlen WR in
        let c = cc () in
        let opc = FStoreMultipleIncrementAfter (wback, c, rnop, xrl, mem) in
        index_check_opc_c opc c "FSTMIAX" 4);

    TS.add_simple_test
      ~title:"LoadCoprocessor"
      (fun () ->
        let islong = boolvalue () in
        let coproc = intvalue 16 in
        let crd = intvalue 16 in
        let c = cc () in
        let imm = intvalue 1024 in
        let rnreg = armreg () in
        let mem = armimmoffsetaddress_op rnreg imm RD in
        let opc = LoadCoprocessor (islong, false, c, coproc, crd, mem, None) in
        let mnem = if islong then "LDCL" else "LDC" in
        index_check_opc_c opc c mnem 6);

    TS.add_simple_test
      ~title:"LoadMultipleDecrementAfter"
      (fun () ->
        let wback = boolvalue () in
        let c = cc () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg (if wback then RW else RD) in
        let rl = armreglist_op WR in
        let rlen = List.length rl#get_register_op_list in
        let mem = mk_arm_mem_multiple_op rnreg rlen RD in
        let opc = LoadMultipleDecrementAfter (wback, c, rn, rl, mem) in
        index_check_opc_c opc c "LDMDA" 4);

    TS.add_simple_test
      ~title:"LoadMultipleDecrementBefore"
      (fun () ->
        let wback = boolvalue () in
        let c = cc () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg (if wback then RW else RD) in
        let rl = armreglist_op WR in
        let rlen = List.length rl#get_register_op_list in
        let mem = mk_arm_mem_multiple_op rnreg rlen RD in
        let opc = LoadMultipleDecrementBefore (wback, c, rn, rl, mem) in
        index_check_opc_c opc c "LDMDB" 4);

    TS.add_simple_test
      ~title:"LoadMultipleIncrementAfter"
      (fun () ->
        let wback = boolvalue () in
        let c = cc () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg (if wback then RW else RD) in
        let rl = armreglist_op WR in
        let rlen = List.length rl#get_register_op_list in
        let mem = mk_arm_mem_multiple_op rnreg rlen RD in
        let opc = LoadMultipleIncrementAfter (wback, c, rn, rl, mem) in
        index_check_opc_c opc c "LDM" 4);

    TS.add_simple_test
      ~title:"LoadMultipleIncrementBefore"
      (fun () ->
        let wback = boolvalue () in
        let c = cc () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg (if wback then RW else RD) in
        let rl = armreglist_op WR in
        let rlen = List.length rl#get_register_op_list in
        let mem = mk_arm_mem_multiple_op rnreg rlen RD in
        let opc = LoadMultipleIncrementBefore (wback, c, rn, rl, mem) in
        index_check_opc_c opc c "LDMIB" 4);

    TS.add_simple_test
      ~title:"LoadRegister (literal)"
      (fun () ->
        let pc = arm_register_op (get_arm_reg 15) RD in
        let rt = armreg_op WR in
        let imm = intvalue 4096 in
        let imm_op = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
        let addrop = literal_op imm in
        let c = cc () in
        let opc = LoadRegister (c, rt, pc, imm_op, addrop, false) in
        index_check_opc_c opc c "LDR" 5);

    TS.add_simple_test
      ~title:"LoadRegister (immediate)"
      (fun () ->
        let tw = boolvalue () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let rt = armreg_op WR in
        let imm = intvalue 4096 in
        let imm_op = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
        let mem = armimmoffsetaddress_op rnreg imm RD in
        let c = cc () in
        let opc = LoadRegister (c, rt, rn, imm_op, mem, tw) in
        index_check_opc_c opc c "LDR" 5);

    TS.add_simple_test
      ~title:"LoadRegister (register)"
      (fun () ->
        let tw = boolvalue () in
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armshiftedindexoffsetaddress_op rnreg rmreg RD in
        let c = cc () in
        let opc = LoadRegister (c, rt, rn, rm, mem, tw) in
        index_check_opc_c opc c "LDR" 5);

    TS.add_simple_test
      ~title:"LoadRegisterByte (register)"
      (fun () ->
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armindexoffsetaddress_op rnreg rmreg RD in
        let c = cc () in
        let opc = LoadRegisterByte (c, rt, rn, rm, mem, false) in
        index_check_opc_c opc c "LDRB" 5);

    TS.add_simple_test
      ~title:"LoadRegisterDual (register)"
      (fun () ->
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rt2 = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let (mem, mem2) = armdualindexoffsetaddresses_op rnreg rmreg RD in
        let c = cc () in
        let opc = LoadRegisterDual (c, rt, rt2, rn, rm, mem, mem2) in
        index_check_opc_c opc c "LDRD" 6);

    TS.add_simple_test
      ~title:"LoadRegisterExclusive"
      (fun () ->
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let rt = armreg_op WR in
        let imm = intvalue 4096 in
        let imm_op = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
        let mem = armimmoffsetaddress_op rnreg imm RD in
        let c = cc () in
        let opc = LoadRegisterExclusive (c, rt, rn, imm_op, mem) in
        index_check_opc_c opc c "LDREX" 4);

    TS.add_simple_test
      ~title:"LoadRegisterHalfword (register)"
      (fun () ->
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armindexoffsetaddress_op rnreg rmreg RD in
        let c = cc () in
        let opc = LoadRegisterHalfword (c, rt, rn, rm, mem, false) in
        index_check_opc_c opc c "LDRH" 5);
    
    TS.add_simple_test
      ~title:"LoadRegisterSignedByte (register)"
      (fun () ->
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armshiftedindexoffsetaddress_op rnreg rmreg RD in
        let c = cc () in
        let opc = LoadRegisterSignedByte (c, rt, rn, rm, mem, false) in
        index_check_opc_c opc c "LDRSB" 5);

    TS.add_simple_test
      ~title:"LoadRegisterSignedHalfword (register)"
      (fun () ->
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armshiftedindexoffsetaddress_op rnreg rmreg RD in
        let c = cc () in
        let opc = LoadRegisterSignedHalfword (c, rt, rn, rm, mem, false) in
        index_check_opc_c opc c "LDRSH" 5);
    
    TS.add_simple_test
      ~title:"LogicalShiftLeft"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = LogicalShiftLeft (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "LSL" 5);

    TS.add_simple_test
      ~title:"LogicalShiftRight"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = LogicalShiftRight (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "LSR" 5);

    TS.add_simple_test
      ~title:"Move"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let aw = if tw then false else boolvalue () in
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = Move (setflags, c, rd, rm, tw, aw) in
        let mnem = if aw then "MOVW" else "MOV" in
        index_check_opc_c opc c mnem 5);

    TS.add_simple_test
      ~title:"MoveRegisterCoprocessor"
      (fun () ->
        let rt = armreg_op WR in
        let opc1 = intvalue 8 in
        let crn = intvalue 16 in
        let coproc = intvalue 16 in
        let opc2 = intvalue 8 in
        let crm = intvalue 16 in
        let c = cc () in
        let opc = MoveRegisterCoprocessor (c, coproc, opc1, rt, crn, crm, opc2) in
        index_check_opc_c opc c "MRC" 6);

    TS.add_simple_test
      ~title:"MoveToCoprocessor"
      (fun () ->
        let rt = armreg_op RD in
        let opc1 = intvalue 8 in
        let crn = intvalue 16 in
        let coproc = intvalue 16 in
        let opc2 = intvalue 8 in
        let crm = intvalue 16 in
        let c = cc () in
        let opc = MoveToCoprocessor (c, coproc, opc1, rt, crn, crm, opc2) in
        index_check_opc_c opc c "MCR" 6);

    TS.add_simple_test
      ~title:"MoveTop"
      (fun () ->
        let rd = armreg_op WR in
        let imm = intvalue e16 in
        let imm16 =
          TR.tget_ok (make_immediate false 2 (mkNumerical imm)) in
        let imm16 = arm_immediate_op imm16 in
        let c = cc () in
        let opc = MoveTop (c, rd, imm16) in
        index_check_opc_c opc c "MOVT" 2);

    TS.add_simple_test
      ~title:"MoveTwoRegisterCoprocessor"
      (fun () ->
        let rt = armreg_op WR in
        let rt2 = armreg_op WR in
        let coproc = intvalue 16 in
        let opc = intvalue 16 in
        let crm = intvalue 16 in
        let c = cc () in
        let opc = MoveTwoRegisterCoprocessor (c, coproc, opc, rt, rt2, crm) in
        index_check_opc_c opc c "MRRC" 5);

    TS.add_simple_test
      ~title:"Multiply"
      (fun () ->
        let setflags = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = Multiply (setflags, c, rd, rn, rm) in
        index_check_opc_c opc c "MUL" 4);

    TS.add_simple_test
      ~title:"MultiplyAccumulate"
      (fun () ->
        let setflags = boolvalue () in
        let rd = armreg_op WR in
        let ra = armreg_op RD in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = MultiplyAccumulate (setflags, c, rd, rn, rm, ra) in
        index_check_opc_c opc c "MLA" 5);

    TS.add_simple_test
      ~title:"MultiplySubtract"
      (fun () ->
        let rd = armreg_op WR in
        let ra = armreg_op RD in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = MultiplySubtract (c, rd, rn, rm, ra) in
        index_check_opc_c opc c "MLS" 4);

    TS.add_simple_test
      ~title:"Pop"
      (fun () ->
        let tw = boolvalue () in
        let sp = arm_register_op (get_arm_reg 13) RW in
        let rl = armreglist_op WR in
        let c = cc () in
        let opc = Pop (c, sp, rl, tw) in
        index_check_opc_c opc c "POP" 3);

    TS.add_simple_test
      ~title:"PreloadData (immediate)"
      (fun () ->
        let pldw = boolvalue () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let imm = intvalue 4096 in
        let mem = armimmoffsetaddress_op rnreg imm WR in
        let c = cc () in
        let opc = PreloadData (pldw, c, rn, mem) in
        let mnem = if pldw then "PLDW" else "PLD" in
        index_check_opc_c opc c mnem 3);
                
    TS.add_simple_test
      ~title:"Push"
      (fun () ->
        let tw = boolvalue () in
        let sp = arm_register_op (get_arm_reg 13) RW in
        let rl = armreglist_op RD in
        let c = cc () in
        let opc = Push (c, sp, rl, tw) in
        index_check_opc_c opc c "PUSH" 3);

    TS.add_simple_test
      ~title:"ReverseBits"
      (fun () ->
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = ReverseBits (c, rd, rm) in
        index_check_opc_c opc c "RBIT" 2);

    TS.add_simple_test
      ~title:"ReverseSubtract (shifted register)"
      (fun () ->
        let setflags = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = ReverseSubtract (setflags, c, rd, rn, rm, false) in
        index_check_opc_c opc c "RSB" 5);

    TS.add_simple_test
      ~title:"ReverseSubtractCarry"
      (fun () ->
        let setflags = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = ReverseSubtractCarry (setflags, c, rd, rn, rm) in
        index_check_opc_c opc c "RSC" 4);
    
    TS.add_simple_test
      ~title:"RotateRight (register)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = RotateRight (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "ROR" 5);

    TS.add_simple_test
      ~title:"RotateRightExtend"
      (fun () ->
        let setflags = boolvalue () in
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = RotateRightExtend (setflags, c, rd, rm) in
        index_check_opc_c opc c "RRX" 3);

    TS.add_simple_test
      ~title:"SaturatingAdd"
      (fun () ->
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SaturatingAdd (c, rd, rm, rn) in
        index_check_opc_c opc c "QADD" 3);

    TS.add_simple_test
      ~title:"SaturatingDoubleAdd"
      (fun () ->
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SaturatingDoubleAdd (c, rd, rm, rn) in
        index_check_opc_c opc c "QDADD" 3);
    
    TS.add_simple_test
      ~title:"SaturatingDoubleSubtract"
      (fun () ->
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SaturatingDoubleSubtract (c, rd, rm, rn) in
        index_check_opc_c opc c "QDSUB" 3);

    TS.add_simple_test
      ~title:"SaturatingSubtract"
      (fun () ->
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SaturatingSubtract (c, rd, rm, rn) in
        index_check_opc_c opc c "QSUB" 3);

    TS.add_simple_test
      ~title:"SelectBytes"
      (fun () ->
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SelectBytes (c, rd, rm, rn) in
        index_check_opc_c opc c "SEL" 3);

    TS.add_simple_test
      ~title:"SHA1FixedRotate"
      (fun () ->
        let dt = VfpSize 8 in
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA1FixedRotate (c, dt, vd, vm) in
        index_check_opc_c opc c "SHA1H" 3);
    
    TS.add_simple_test
      ~title:"SHA1HashUpdateChoose"
      (fun () ->
        let dt = VfpSize 8 in
        let vd = armxquadreg_op WR in
        let vn = armxquadreg_op RD in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA1HashUpdateChoose (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "SHA1C" 4);

    TS.add_simple_test
      ~title:"SHA1HashUpdateMajority"
      (fun () ->
        let dt = VfpSize 8 in
        let vd = armxquadreg_op WR in
        let vn = armxquadreg_op RD in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA1HashUpdateMajority (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "SHA1M" 4);

    TS.add_simple_test
      ~title:"SHA1HashUpdateParity"
      (fun () ->
        let dt = VfpSize 32 in
        let vd = armxquadreg_op WR in
        let vn = armxquadreg_op RD in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA1HashUpdateParity (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "SHA1P" 4);

    TS.add_simple_test
      ~title:"SHA1ScheduleUpdate0"
      (fun () ->
        let dt = VfpSize 32 in
        let vd = armxquadreg_op WR in
        let vn = armxquadreg_op RD in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA1ScheduleUpdate0 (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "SHA1SU0" 4);

    TS.add_simple_test
      ~title:"SHA1ScheduleUpdate1"
      (fun () ->
        let dt = VfpSize 32 in
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA1ScheduleUpdate1 (c, dt, vd, vm) in
        index_check_opc_c opc c "SHA1SU1" 3);

    TS.add_simple_test
      ~title:"SHA256HashUpdatePart1"
      (fun () ->
        let dt = VfpSize 32 in
        let vd = armxquadreg_op WR in
        let vn = armxquadreg_op RD in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA256HashUpdatePart1 (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "SHA256H" 4);

    TS.add_simple_test
      ~title:"SHA256HashUpdatePart2"
      (fun () ->
        let dt = VfpSize 32 in
        let vd = armxquadreg_op WR in
        let vn = armxquadreg_op RD in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA256HashUpdatePart2 (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "SHA256H2" 4);

    TS.add_simple_test
      ~title:"SHA256ScheduleUpdate0"
      (fun () ->
        let dt = VfpSize 32 in
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA256ScheduleUpdate0 (c, dt, vd, vm) in
        index_check_opc_c opc c "SHA256SU0" 3);

    TS.add_simple_test
      ~title:"SHA256ScheduleUpdate1"
      (fun () ->
        let dt = VfpSize 32 in
        let vd = armxquadreg_op WR in
        let vn = armxquadreg_op RD in
        let vm = armxquadreg_op RD in
        let c = cc () in
        let opc = SHA256ScheduleUpdate1 (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "SHA256SU1" 4);

    TS.add_simple_test
      ~title:"SignedBitFieldExtract"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armregbitsequence_op RD in
        let c = cc () in
        let opc = SignedBitFieldExtract (c, rd, rn) in
        index_check_opc_c opc c "SBFX" 2);

    TS.add_simple_test
      ~title:"SignedDivide"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = SignedDivide (c, rd, rn, rm) in
        index_check_opc_c opc c "SDIV" 3);

    TS.add_simple_test
      ~title:"SignedExtendByte"
      (fun () ->
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rm = armrotatedreg_op RD in
        let c = cc () in
        let opc = SignedExtendByte (c, rd, rm, tw) in
        index_check_opc_c opc c "SXTB" 3);

    TS.add_simple_test
      ~title:"SignedExtendHalfword"
      (fun () ->
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rm = armrotatedreg_op RD in
        let c = cc () in
        let opc = SignedExtendHalfword (c, rd, rm, tw) in
        index_check_opc_c opc c "SXTH" 3);

    TS.add_simple_test
      ~title:"SignedMostSignificantWordMultiply"
      (fun () ->
        let roundf = intvalue 2 in
        let rd = armreg_op WR in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SignedMostSignificantWordMultiply (c, rd, rn, rm, roundf) in
        let mnem = if roundf = 1 then "SMMULR" else "SMMUL" in
        index_check_opc_c opc c mnem 4);

    TS.add_simple_test
      ~title:"SignedMostSignificantWordMultiplyAccumulate"
      (fun () ->
        let roundf = intvalue 2 in
        let rd = armreg_op WR in
        let ra = armreg_op WR in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc =
          SignedMostSignificantWordMultiplyAccumulate
            (c, rd, rn, rm, ra, roundf) in
        let mnem = if roundf = 1 then "SMMLAR" else "SMMLA" in
        index_check_opc_c opc c mnem 5);
    
    TS.add_simple_test
      ~title:"SignedMultiplyAccumulateBB"
      (fun () ->
        let rd = armreg_op WR in
        let ra = armreg_op RD in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SignedMultiplyAccumulateBB (c, rd, rn, rm, ra) in
        index_check_opc_c opc c "SMLABB" 4);

    TS.add_simple_test
      ~title:"SignedMultiplyAccumulateBT"
      (fun () ->
        let rd = armreg_op WR in
        let ra = armreg_op RD in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SignedMultiplyAccumulateBT (c, rd, rn, rm, ra) in
        index_check_opc_c opc c "SMLABT" 4);

    TS.add_simple_test
      ~title:"SignedMultiplyAccumulateTB"
      (fun () ->
        let rd = armreg_op WR in
        let ra = armreg_op RD in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SignedMultiplyAccumulateTB (c, rd, rn, rm, ra) in
        index_check_opc_c opc c "SMLATB" 4);

    TS.add_simple_test
      ~title:"SignedMultiplyAccumulateTT"
      (fun () ->
        let rd = armreg_op WR in
        let ra = armreg_op RD in
        let rm = armreg_op RD in
        let rn = armreg_op RD in
        let c = cc () in
        let opc = SignedMultiplyAccumulateTT (c, rd, rn, rm, ra) in
        index_check_opc_c opc c "SMLATT" 4);

    TS.add_simple_test
      ~title:"SignedMultiplyAccumulateLong"
      (fun () ->
        let setflags = boolvalue () in
        let rdlo = armreg_op WR in
        let rdhi = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc =
          SignedMultiplyAccumulateLong (setflags, c, rdlo, rdhi, rn, rm) in
        index_check_opc_c opc c "SMLAL" 5);

    TS.add_simple_test
      ~title:"SignedMultiplyAccumualteWordB"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let ra = armreg_op RD in
        let c = cc () in
        let opc = SignedMultiplyAccumulateWordB (c, rd, rn, rm, ra) in
        index_check_opc_c opc c "SMLAWB" 4);

    TS.add_simple_test
      ~title:"SignedMultiplyAccumualteWordT"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let ra = armreg_op RD in
        let c = cc () in
        let opc = SignedMultiplyAccumulateWordT (c, rd, rn, rm, ra) in
        index_check_opc_c opc c "SMLAWT" 4);

    TS.add_simple_test
      ~title:"SignedMultiplyHalfwordsBB"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c =  cc () in
        let opc = SignedMultiplyHalfwordsBB (c, rd, rn, rm) in
        index_check_opc_c opc c "SMULBB" 3);

    TS.add_simple_test
      ~title:"SignedMultiplyHalfwordsBT"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c =  cc () in
        let opc = SignedMultiplyHalfwordsBT (c, rd, rn, rm) in
        index_check_opc_c opc c "SMULBT" 3);

    TS.add_simple_test
      ~title:"SignedMultiplyHalfwordsTB"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c =  cc () in
        let opc = SignedMultiplyHalfwordsTB (c, rd, rn, rm) in
        index_check_opc_c opc c "SMULTB" 3);

    TS.add_simple_test
      ~title:"SignedMultiplyHalfwordsTT"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c =  cc () in
        let opc = SignedMultiplyHalfwordsTT (c, rd, rn, rm) in
        index_check_opc_c opc c "SMULTT" 3);
    
    TS.add_simple_test
      ~title:"SignedMultiplyLong"
      (fun () ->
        let setflags = boolvalue () in
        let rdlo = armreg_op WR in
        let rdhi = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = SignedMultiplyLong (setflags, c, rdlo, rdhi, rn, rm) in
        index_check_opc_c opc c "SMULL" 5);

    TS.add_simple_test
      ~title:"SignedMultiplyWordB"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c =  cc () in
        let opc = SignedMultiplyWordB (c, rd, rn, rm) in
        index_check_opc_c opc c "SMULWB" 3);

    TS.add_simple_test
      ~title:"SignedMultiplyWordT"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c =  cc () in
        let opc = SignedMultiplyWordT (c, rd, rn, rm) in
        index_check_opc_c opc c "SMULWT" 3);

    TS.add_simple_test
      ~title:"StoreCoprocessor"
      (fun () ->
        let islong = boolvalue () in
        let coproc = intvalue 16 in
        let crd = intvalue 16 in
        let c = cc () in
        let imm = intvalue 1024 in
        let rnreg = armreg () in
        let mem = armimmoffsetaddress_op rnreg imm WR in
        let opc = StoreCoprocessor (islong, false, c, coproc, crd, mem, None) in
        let mnem = if islong then "STCL" else "STC" in
        index_check_opc_c opc c mnem 6);

    TS.add_simple_test
      ~title:"StoreMultipleDecrementAfter"
      (fun () ->
        let wback = boolvalue () in
        let c = cc () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg (if wback then RW else RD) in
        let rl = armreglist_op RD in
        let rlen = List.length rl#get_register_op_list in
        let mem = mk_arm_mem_multiple_op rnreg rlen WR in
        let opc = StoreMultipleDecrementAfter (wback, c, rn, rl, mem) in
        index_check_opc_c opc c "STMDA" 4);
    
    TS.add_simple_test
      ~title:"StoreMultipleDecrementBefore"
      (fun () ->
        let wback = boolvalue () in
        let c = cc () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg (if wback then RW else RD) in
        let rl = armreglist_op RD in
        let rlen = List.length rl#get_register_op_list in
        let mem = mk_arm_mem_multiple_op rnreg rlen WR in
        let opc = StoreMultipleDecrementBefore (wback, c, rn, rl, mem) in
        index_check_opc_c opc c "STMDB" 4);

    TS.add_simple_test
      ~title:"StoreMultipleIncrementAfter"
      (fun () ->
        let tw = boolvalue () in
        let wback = false in
        let c = cc () in
        let rn = intvalue 13 in
        let rnreg = get_arm_reg rn in
        let rnop = arm_register_op rnreg (if wback then RW else RD) in
        let rl = armreglist_op RD in
        let rlen = List.length rl#get_register_op_list in
        let mem = mk_arm_mem_multiple_op rnreg rlen WR in
        let opc = StoreMultipleIncrementAfter (wback, c, rnop, rl, mem, tw) in
        index_check_opc_c opc c "STM" 5);
    
    TS.add_simple_test
      ~title:"StoreMultipleIncrementBefore"
      (fun () ->
        let wback = boolvalue () in
        let c = cc () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg (if wback then RW else RD) in
        let rl = armreglist_op RD in
        let rlen = List.length rl#get_register_op_list in
        let mem = mk_arm_mem_multiple_op rnreg rlen WR in
        let opc = StoreMultipleIncrementBefore (wback, c, rn, rl, mem) in
        index_check_opc_c opc c "STMIB" 4);
    
    TS.add_simple_test
      ~title:"StoreRegister (immediate)"
      (fun () ->
        let tw = boolvalue () in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let rt = armreg_op RD in
        let imm = intvalue 4096 in
        let imm_op = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
        let mem = armimmoffsetaddress_op rnreg imm WR in
        let c = cc () in
        let opc = StoreRegister (c, rt, rn, imm_op, mem, tw) in
        index_check_opc_c opc c "STR" 5);

    TS.add_simple_test
      ~title:"StoreRegister (register)"
      (fun () ->
        let tw = boolvalue () in
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armshiftedindexoffsetaddress_op rnreg rmreg WR in
        let c = cc () in
        let opc = StoreRegister (c, rt, rn, rm, mem, tw) in
        index_check_opc_c opc c "STR" 5);
    
    TS.add_simple_test
      ~title:"StoreRegisterByte (register)"
      (fun () ->
        let tw = boolvalue () in
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armshiftedindexoffsetaddress_op rnreg rmreg WR in
        let c = cc () in
        let opc = StoreRegisterByte (c, rt, rn, rm, mem, tw) in
        index_check_opc_c opc c "STRB" 5);

    TS.add_simple_test
      ~title:"StoreRegisterDual (register)"
      (fun () ->
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op RD in
        let rt2 = armreg_op RD in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let (mem, mem2) = armdualindexoffsetaddresses_op rnreg rmreg WR in
        let c = cc () in
        let opc = StoreRegisterDual (c, rt, rt2, rn, rm, mem, mem2) in
        index_check_opc_c opc c "STRD" 6);

    TS.add_simple_test
      ~title:"StoreRegisterExclusive"
      (fun () ->
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let rt = armreg_op RD in
        let imm = intvalue 4096 in
        let imm_op = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
        let mem = armimmoffsetaddress_op rnreg imm WR in
        let c = cc () in
        let opc = StoreRegisterExclusive (c, rt, rn, imm_op, mem) in
        index_check_opc_c opc c "STREX" 4);
    
    TS.add_simple_test
      ~title:"StoreRegisterHalfword (register)"
      (fun () ->
        let tw = boolvalue () in
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rt = armreg_op WR in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armshiftedindexoffsetaddress_op rnreg rmreg WR in
        let c = cc () in
        let opc = StoreRegisterHalfword (c, rt, rn, rm, mem, tw) in
        index_check_opc_c opc c "STRH" 5);

    TS.add_simple_test
      ~title:"Subtract (register)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let aw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = Subtract (setflags, c, rd, rn, rm, tw, aw) in
        let mnem = if aw then "SUBW" else "SUB" in        
        index_check_opc_c opc c mnem 6);
    
    TS.add_simple_test
      ~title:"SubtractCarry (register)"
      (fun () ->
        let setflags = boolvalue () in
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = SubtractCarry (setflags, c, rd, rn, rm, tw) in
        index_check_opc_c opc c "SBC" 5);

    TS.add_simple_test
      ~title:"Swap"
      (fun () ->
        let rt = armreg_op WR in
        let rt2 = armreg_op WR in
        let rnreg = armreg () in
        let mem =
          mk_arm_offset_address_op
            rnreg (ARMImmOffset 0) ~isadd:true ~isindex:false ~iswback:false WR in
        let c = cc () in
        let opc = Swap (c, rt, rt2, mem) in
        index_check_opc_c opc c "SWP" 3);

    TS.add_simple_test
      ~title:"SwapByte"
      (fun () ->
        let rt = armreg_op WR in
        let rt2 = armreg_op WR in
        let rnreg = armreg () in
        let mem =
          mk_arm_offset_address_op
            rnreg (ARMImmOffset 0) ~isadd:true ~isindex:false ~iswback:false WR in
        let c = cc () in
        let opc = SwapByte (c, rt, rt2, mem) in
        index_check_opc_c opc c "SWPB" 3);

    TS.add_simple_test
      ~title:"TableBranchByte"
      (fun () ->
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armindexoffsetaddress_op rnreg rmreg RD in
        let c = cc () in
        let opc = TableBranchByte (c, rn, rm, mem) in
        index_check_opc_c opc c "TBB" 3);

    TS.add_simple_test
      ~title:"TableBranchHalfword"
      (fun () ->
        let rnreg = armreg () in
        let rmreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let rm = arm_register_op rmreg RD in
        let mem = armindexoffsetaddress_op rnreg rmreg RD in
        let c = cc () in
        let opc = TableBranchHalfword (c, rn, rm, mem) in
        index_check_opc_c opc c "TBH" 3);

    TS.add_simple_test
      ~title:"Test"
      (fun () ->
        let tw = boolvalue () in
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = Test (c, rn, rm, tw) in
        index_check_opc_c opc c "TST" 3);

    TS.add_simple_test
      ~title:"TestEquivalence"
      (fun () ->
        let rn = armreg_op RD in
        let rm = armimmshiftreg_op RD in
        let c = cc () in
        let opc = TestEquivalence (c, rn, rm) in
        index_check_opc_c opc c "TEQ" 2);

    TS.add_simple_test
      ~title:"UnsignedAdd8"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = UnsignedAdd8 (c, rd, rn, rm) in
        index_check_opc_c opc c "UADD8" 3);

    TS.add_simple_test
      ~title:"UnsignedBitFieldExtract"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armregbitsequence_op RD in
        let c = cc () in
        let opc = UnsignedBitFieldExtract (c, rd, rn) in
        index_check_opc_c opc c "UBFX" 2);

    TS.add_simple_test
      ~title:"UnsignedDivide"
      (fun  () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = UnsignedDivide (c, rd, rn, rm) in
        index_check_opc_c opc c "UDIV" 3);

    TS.add_simple_test
      ~title:"UnsignedExtendAddByte"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armrotatedreg_op RD in
        let c = cc () in
        let opc = UnsignedExtendAddByte (c, rd, rn, rm) in
        index_check_opc_c opc c "UXTAB" 3);

    TS.add_simple_test
      ~title:"UnsignedExtendAddHalfword"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armrotatedreg_op RD in
        let c = cc () in
        let opc = UnsignedExtendAddHalfword (c, rd, rn, rm) in
        index_check_opc_c opc c "UXTAH" 3);
    
    TS.add_simple_test
      ~title:"UnsignedExtendByte"
      (fun () ->
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rm = armrotatedreg_op RD in
        let c = cc () in
        let opc = UnsignedExtendByte (c, rd, rm, tw) in
        index_check_opc_c opc c "UXTB" 3);

    TS.add_simple_test
      ~title:"UnsignedExtendHalfword"
      (fun () ->
        let tw = boolvalue () in
        let rd = armreg_op WR in
        let rm = armrotatedreg_op RD in
        let c = cc () in
        let opc = UnsignedExtendHalfword (c, rd, rm, tw) in
        index_check_opc_c opc c "UXTH" 3);

    TS.add_simple_test
      ~title:"UnsignedMultiplyAccumulateLong"
      (fun () ->
        let setflags = boolvalue () in
        let rdhi = armreg_op WR in
        let rdlo = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc =
          UnsignedMultiplyAccumulateLong (setflags, c, rdlo, rdhi, rn, rm) in
        index_check_opc_c opc c "UMLAL" 5);

    TS.add_simple_test
      ~title:"UnsignedMultiplyLong"
      (fun () ->
        let setflags = boolvalue () in
        let rdhi = armreg_op WR in
        let rdlo = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc =
          UnsignedMultiplyLong (setflags, c, rdlo, rdhi, rn, rm) in
        index_check_opc_c opc c "UMULL" 5);

    TS.add_simple_test
      ~title:"UnsignedSaturatingSubtract8"
      (fun () ->
        let rd = armreg_op WR in
        let rn = armreg_op RD in
        let rm = armreg_op RD in
        let c = cc () in
        let opc = UnsignedSaturatingSubtract8 (c, rd, rn, rm) in
        index_check_opc_c opc c "UQSUB8" 3);

    TS.add_simple_test
      ~title:"VectorAbsolute"
      (fun () ->
        let dp = boolvalue () in
        let vd = armvfp_op dp WR in
        let vm = armvfp_op dp RD in
        let dt = if dp then VfpFloat 64 else VfpFloat 32 in
        let c = cc () in
        let opc = VectorAbsolute (c, dt, vd, vm) in
        index_check_opc_c opc c "VABS" 3);

    TS.add_simple_test
      ~title:"VectorAdd (floating point)"
      (fun () ->
        let dp = boolvalue () in
        let vd = armvfp_op dp WR in
        let vn = armvfp_op dp RD in
        let vm = armvfp_op dp RD in
        let dt = if dp then VfpFloat 64 else VfpFloat 32 in
        let c = cc () in
        let opc = VectorAdd (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "VADD" 4);

    TS.add_simple_test
      ~title:"VectorAddLong"
      (fun () ->
        let qd = armxquadreg_op WR in
        let dn = armxdoublereg_op RD in
        let dm = armxdoublereg_op RD in
        let dt = armvfp_su_dt () in
        let c = cc () in
        let opc = VectorAddLong (c, dt, qd, dn, dm) in
        index_check_opc_c opc c "VADDL" 4);

    TS.add_simple_test
      ~title:"VectorAddWide"
      (fun () ->
        let qd = armxquadreg_op WR in
        let qn = armxquadreg_op RD in
        let dm = armxdoublereg_op RD in
        let dt = armvfp_su_dt () in
        let c = cc () in
        let opc = VectorAddWide (c, dt, qd, qn, dm) in
        index_check_opc_c opc c "VADDW" 4);

    TS.add_simple_test
      ~title:"VectorBitwiseAnd (Quad)"
      (fun () ->
        let qd = armxquadreg_op WR in
        let qn = armxquadreg_op RD in
        let qm = armxquadreg_op RD in
        let c = cc () in
        let opc = VectorBitwiseAnd (c, qd, qn, qm) in
        index_check_opc_c opc c "VAND" 3);

    TS.add_simple_test
      ~title:"VectorBitwiseBitClear (Quad, register)"
      (fun () ->
        let qd = armxquadreg_op WR in
        let qn = armxquadreg_op RD in
        let qm = armxquadreg_op RD in
        let dt = VfpNone in
        let c = cc () in
        let opc = VectorBitwiseBitClear (c, dt, qd, qn, qm) in
        index_check_opc_c opc c "VBIC" 4);

    TS.add_simple_test
      ~title:"VectorBitwiseExclusiveOr (Quad)"
      (fun () ->
        let qd = armxquadreg_op WR in
        let qn = armxquadreg_op RD in
        let qm = armxquadreg_op RD in
        let c = cc () in
        let opc = VectorBitwiseExclusiveOr (c, qd, qn, qm) in
        index_check_opc_c opc c "VEOR" 3);

    TS.add_simple_test
      ~title:"VectorBitwiseNot (Quad, register)"
      (fun () ->
        let qd = armxquadreg_op WR in
        let qm = armxquadreg_op RD in
        let c = cc () in
        let dt = VfpNone in
        let opc = VectorBitwiseNot (c, dt, qd, qm) in
        index_check_opc_c opc c "VMVN" 3);

    TS.add_simple_test
      ~title:"VectorBitwiseOr (Quad, register)"
      (fun () ->
        let qd = armxquadreg_op WR in
        let qn = armxquadreg_op RD in
        let qm = armxquadreg_op RD in
        let c = cc () in
        let dt = VfpNone in
        let opc = VectorBitwiseOr (c, dt, qd, qn, qm) in
        index_check_opc_c opc c "VORR" 4);

    TS.add_simple_test
      ~title:"VectorBitwiseOr (Double, immediate)"
      (fun () ->
        let d = prefix_bit (intvalue 2) (intvalue 16) in
        let vd = arm_extension_register_op XDouble d WR in
        let vm = arm_extension_register_op XDouble d RD in
        let imm8 = ((intvalue 8) lsl 4) + (intvalue 16) in
        let immop = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm8)) in
        let cm = select_int [1; 3; 5; 7; 9; 11] in
        let dt =
          match cm with
          | 1 | 3 | 5 | 7 -> VfpInt 32
          | _ -> VfpInt 16 in
        let c = cc () in
        let opc = VectorBitwiseOr (c, dt, vd, vm, immop) in
        index_check_opc_c opc c "VORR" 4);

    TS.add_simple_test
      ~title:"VectorBitwiseOrNot (Quad, register)"
      (fun () ->
        let qd = armxquadreg_op WR in
        let qn = armxquadreg_op RD in
        let qm = armxquadreg_op RD in
        let c = cc () in
        let dt = VfpNone in
        let opc = VectorBitwiseOrNot (c, dt, qd, qn, qm) in
        index_check_opc_c opc c "VORN" 4);

    TS.add_simple_test
      ~title:"VectorBitwiseSelect (Double)"
      (fun () ->
        let dd = armxdoublereg_op WR in
        let dn = armxdoublereg_op RD in
        let dm = armxdoublereg_op RD in
        let c = cc () in
        let dt = VfpNone in
        let opc = VectorBitwiseSelect (c, dt, dd, dn, dm) in
        index_check_opc_c opc c "VBSL" 4);

    TS.add_simple_test
      ~title:"VCompare (register)"
      (fun () ->
        let nan = boolvalue () in
        let dp = boolvalue () in
        let vd = armvfp_op dp RD in
        let vm = armvfp_op dp RD in
        let dt = if dp then VfpFloat 64 else VfpFloat 32 in
        let fdst = arm_special_register_op FPSCR WR in
        let c = cc () in
        let opc = VCompare (nan, c, dt, fdst, vd, vm) in
        let mnem = if nan then "VCMPE" else "VCMP" in
        index_check_opc_c opc c mnem 4);

    TS.add_simple_test
      ~title:"VectorConvert (float-int)"
      (fun () ->
        let qd = armxquadreg_op WR in
        let qm = armxquadreg_op RD in
        let dt1 = VfpSignedInt 32 in
        let dt2 = VfpFloat 32 in
        let c = cc () in
        let imm0_op = arm_immediate_op imm0 in
        let opc = VectorConvert (false, false, c, dt1, dt2, qd, qm, imm0_op) in
        index_check_opc_c opc c "VCVT" 7);

    TS.add_simple_test
      ~title:"VDivide (double-precision)"
      (fun () ->
        let dd = armxdoublereg_op WR in
        let dn = armxdoublereg_op RD in
        let dm = armxdoublereg_op RD in
        let dt = VfpFloat 64 in
        let c = cc () in
        let opc = VDivide (c, dt, dd, dn, dm) in
        index_check_opc_c opc c "VDIV" 4);

    TS.add_simple_test
      ~title:"VectorDuplicate (ARM core)"
      (fun () ->
        let qd = armxquadreg_op WR in
        let rt = armreg_op RD in
        let dt = VfpSize 32 in
        let elements = 2 in
        let regs = 2 in
        let c = cc () in
        let opc = VectorDuplicate (c, dt, regs, elements, qd, rt) in
        index_check_opc_c opc c "VDUP" 5);

    TS.add_simple_test
      ~title:"VectorExtract"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vn = armxdoublereg_op RD in
        let vm = armxdoublereg_op RD in
        let imm = intvalue 8 in
        let imm = TR.tget_ok (mk_arm_immediate_op false 4 (mkNumerical imm)) in
        let c = cc () in
        let opc = VectorExtract (c, VfpSize 8, vd, vn, vm, imm) in
        index_check_opc_c opc c "VEXT" 5);

    TS.add_simple_test
      ~title:"VectorLoadMultipleIncrementAfter"
      (fun () ->
        let wback = false in
        let rl = armxsinglereglist_op WR in
        let regs = List.length rl#get_extension_register_op_list in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let mem = mk_arm_mem_multiple_op ~size:4 rnreg regs RD in
        let c = cc () in
        let opc = VectorLoadMultipleIncrementAfter (wback, c, rn, rl, mem) in
        index_check_opc_c opc c "VLDM" 4);

    TS.add_simple_test
      ~title:"VectorLoadOne (1 register)"
      (fun () ->
        let c = ACCUnconditional in
        let align = 1 in
        let rnreg = intvalue 13 in
        let wb = false in
        let wback = SIMDNoWriteback in
        let sz = intvalue 4 in
        let ebytes = 1 lsl sz in
        let esize = 8 * ebytes in
        let dbit = intvalue 2 in
        let dval = intvalue 16 in
        let vd = prefix_bit dbit dval in
        let rlist = arm_simd_reg_list_op XDouble [vd] WR in
        let mem = mk_arm_simd_address_op (get_arm_reg rnreg) align wback RD in
        let rn = arm_register_op (get_arm_reg rnreg) RD in
        let rm = armreg_op RD in
        let opc = VectorLoadOne (wb, c, VfpSize esize, rlist, rn, mem, rm) in
        index_check_opc_c opc c "VLD1" 6);

    TS.add_simple_test
      ~title:"VectorLoadFour (single 4-elt to one lane)"
      (fun () ->
        let c = ACCUnconditional in
        let rmreg = intvalue 16 in
        let rm = get_arm_reg rmreg in
        let rmop = arm_register_op rm RD in
        let rn = armreg () in
        let d = intvalue 2 in
        let vd = prefix_bit d (intvalue 16) in
        let sz = intvalue 3 in
        let (ebytes, esize, index, inc, alignment) =
          match sz with
          | 0 -> (1, 8, intvalue 8, 1, select_int [1; 4])
          | 1 -> (2, 16, intvalue 4, select_int [1; 2], select_int [1; 8])
          | _ -> (4, 32, intvalue 2, select_int [1; 2], select_int [1; 4; 8; 16]) in
        let (wb, wback) =
          match rmreg with
          | 15 -> (false, SIMDNoWriteback)
          | 13 -> (true, SIMDBytesTransferred ebytes)
          | _ -> (true, SIMDAddressOffsetRegister rm) in
        let rnop = arm_register_op rn (if wb then WR else RD) in
        let mem = mk_arm_simd_address_op rn alignment wback in
        let rlist =
          arm_simd_reg_elt_list_op
            XDouble [vd; vd + inc; vd + (2 * inc); vd + (3 * inc)] index esize in
        let opc = VectorLoadFour (wb, c, VfpSize esize, rlist RD, rnop, mem WR, rmop) in
        index_check_opc_c opc c "VLD4" 6);

    TS.add_simple_test
      ~title:"VLoadRegister (A2-add)"
      (fun () ->
        let vd = armxsinglereg_op WR in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let imm = 4 * (intvalue 256) in
        let mem = armimmoffsetaddress_op rnreg imm RD in
        let c = cc () in
        let opc = VLoadRegister (c, vd, rn, mem) in
        index_check_opc_c opc c "VLDR" 3);

    TS.add_simple_test
      ~title:"VectorMoveDDSS (2 core -> 2 sp)"
      (fun () ->
        let (sm, sm1, smd) = armdualxsinglereg_op RD in
        let rtreg = armreg () in
        let rt2reg = armreg () in
        let rt = arm_register_op rtreg WR in
        let rt2 = arm_register_op rt2reg WR in
        let rtd = arm_double_register_op rtreg rt2reg WR in
        let c = cc () in
        let opc = VectorMoveDDSS (c, VfpNone, rt, rt2, rtd, sm, sm1, smd) in
        index_check_opc_c opc c "VMOV" 5);
        
    TS.add_simple_test
      ~title:"VectorMoveLong"
      (fun () ->
        let qd = armxquadreg_op WR in
        let dm = armxdoublereg_op RD in
        let dt = VfpSignedInt 8 in
        let c = cc () in
        let opc = VectorMoveLong (c, dt, qd, dm) in
        index_check_opc_c opc c "VMOVL" 3);

    TS.add_simple_test
      ~title:"VectorMoveNarrow"
      (fun () ->
        let dd = armxdoublereg_op WR in
        let qm = armxquadreg_op RD in
        let dt = VfpSize (8 lsl (intvalue 4)) in
        let c = cc () in
        let opc = VectorMoveNarrow (c, dt, dd, qm) in
        index_check_opc_c opc c "VMOVN" 3);

    TS.add_simple_test
      ~title:"VMoveRegisterStatus"
      (fun () ->
        let rt = armreg_op WR in
        let fpscr = arm_special_register_op FPSCR RD in
        let c = cc () in
        let opc = VMoveRegisterStatus (c, rt, fpscr) in
        index_check_opc_c opc c "VMRS" 2);

    TS.add_simple_test
      ~title:"VMoveToSystemRegister"
      (fun () ->
        let rt = armreg_op RD in
        let fpscr = arm_special_register_op FPSCR WR in
        let c = cc () in
        let opc = VMoveToSystemRegister (c, fpscr, rt) in
        index_check_opc_c opc c "VMSR" 2);

    TS.add_simple_test
      ~title:"VectorMultiply (floating-point)"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vn = armxdoublereg_op RD in
        let vm = armxdoublereg_op RD in
        let dt = VfpFloat 64 in
        let c = cc () in
        let opc = VectorMultiply (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "VMUL" 4);

    TS.add_simple_test
      ~title:"VectorMultiplyAccumulate (floating-point)"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vn = armxdoublereg_op RD in
        let vm = armxdoublereg_op RD in
        let dt = VfpFloat 64 in
        let c = cc () in
        let opc = VectorMultiplyAccumulate (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "VMLA" 4);

    TS.add_simple_test
      ~title:"VectorMultiplyAccumulateLong (by scalar)"
      (fun () ->
        let vd = armxquadreg_op WR in
        let vn = armxdoublereg_op RD in
        let dt = VfpSignedInt 16 in
        let index = intvalue 4 in
        let m = intvalue 8 in
        let elt = arm_extension_register_element_op XDouble m index 16 RD in
        let c = cc () in
        let opc = VectorMultiplyAccumulateLong (c, dt, vd, vn, elt) in
        index_check_opc_c opc c "VMLAL" 4);

    TS.add_simple_test
      ~title:"VectorMultiplyLong (by scalar)"
      (fun () ->
        let vd = armxquadreg_op WR in
        let vn = armxdoublereg_op RD in
        let dt = VfpSignedInt 32 in
        let m = intvalue 16 in
        let index = intvalue 2 in
        let elt = arm_extension_register_element_op XDouble m index 32 RD in
        let c = cc () in
        let opc = VectorMultiplyLong (c, dt, vd, vn, elt) in
        index_check_opc_c opc c "VMULL" 4);
                    
    TS.add_simple_test
      ~title:"VectorMultiplySubtract (floating-point)"
      (fun () ->
        let vd = armxsinglereg_op WR in
        let vn = armxsinglereg_op RD in
        let vm = armxsinglereg_op RD in
        let dt = VfpFloat 32 in
        let c = cc () in
        let opc = VectorMultiplySubtract (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "VMLS" 4);

    TS.add_simple_test
      ~title:"VectorNegate (VFP)"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vm = armxdoublereg_op RD in
        let dt = VfpFloat 64 in
        let c = cc () in
        let opc = VectorNegate (c, dt, vd, vm) in
        index_check_opc_c opc c "VNEG" 3);

    TS.add_simple_test
      ~title:"VectorPop (A1)"
      (fun () ->
        let spreg = get_arm_reg 13 in
        let sp = arm_register_op spreg WR in
        let rl = armxsinglereglist_op WR in
        let regs = List.length rl#get_extension_register_op_list in
        let mem = mk_arm_mem_multiple_op ~size:8 spreg regs RD in
        let c = cc () in
        let opc = VectorPop (c, sp, rl, mem) in
        index_check_opc_c opc c "VPOP" 3);
        
    TS.add_simple_test
      ~title:"VectorPush (A1)"
      (fun () ->
        let spreg = get_arm_reg 13 in
        let sp = arm_register_op spreg WR in
        let rl = armxsinglereglist_op RD in
        let regs = List.length rl#get_extension_register_op_list in
        let mem = mk_arm_mem_multiple_op ~size:8 spreg regs WR in
        let c = cc () in
        let opc = VectorPush (c, sp, rl, mem) in
        index_check_opc_c opc c "VPUSH" 3);

    TS.add_simple_test
      ~title:"VectorReverseDoublewords"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vm = armxdoublereg_op RD in
        let dt = VfpSize (8 lsl (intvalue 4)) in
        let c = cc () in
        let opc = VectorReverseDoublewords (c, dt, vd, vm) in
        index_check_opc_c opc c "VREV64" 3);

    TS.add_simple_test
      ~title:"VectorReverseHalfwords"
      (fun () ->
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let dt = VfpSize (8 lsl (intvalue 4)) in
        let c = cc () in
        let opc = VectorReverseHalfwords (c, dt, vd, vm) in
        index_check_opc_c opc c "VREV16" 3);

    TS.add_simple_test
      ~title:"VectorReverseWords"
      (fun () ->
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let dt = VfpSize (8 lsl (intvalue 4)) in
        let c = cc () in
        let opc = VectorReverseWords (c, dt, vd, vm) in
        index_check_opc_c opc c "VREV32" 3);

    TS.add_simple_test
      ~title:"VectorRoundingHalvingAdd"
    (fun () ->
      let vd = armxdoublereg_op WR in
      let vn = armxdoublereg_op RD in
      let vm = armxdoublereg_op RD in
      let size = 8 lsl (intvalue 3) in
      let unsigned = boolvalue () in
      let dt = if unsigned then VfpUnsignedInt size else VfpSignedInt size in
      let c = cc () in
      let opc = VectorRoundingHalvingAdd (c, dt, vd, vn, vm) in
      index_check_opc_c opc c "VRHADD" 4);

    TS.add_simple_test
      ~title:"VectorRoundingShiftRightAccumulate"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vm = armxdoublereg_op RD in
        let imm6 = intvalue ~min:8 16 in
        let esize = 8 in
        let sam = 16 - imm6 in
        let dt = VfpSignedInt esize in
        let imm = TR.tget_ok (mk_arm_immediate_op true 4 (mkNumerical sam)) in
        let c = cc () in
        let opc = VectorRoundingShiftRightAccumulate (c, dt, vd, vm, imm) in
        index_check_opc_c opc c "VRSRA" 4);

    TS.add_simple_test
      ~title:"VectorShiftLeft (immediate)"
      (fun () ->
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let imm6 = intvalue ~min:8 16 in
        let esize = 8 in
        let sam = imm6 - 8 in
        let dt = VfpInt esize in
        let imm = TR.tget_ok (mk_arm_immediate_op true 4 (mkNumerical sam)) in
        let c = cc () in
        let opc = VectorShiftLeft (c, dt, vd, vm, imm) in
        index_check_opc_c opc c "VSHL" 4);

    TS.add_simple_test
      ~title:"VectorShiftLeftInsert"
      (fun () ->
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let imm6 = intvalue ~min:16 32 in
        let esize = 16 in
        let sam = imm6 - 16 in
        let dt = VfpInt esize in
        let imm = TR.tget_ok (mk_arm_immediate_op true 4 (mkNumerical sam)) in
        let c = cc () in
        let opc = VectorShiftLeftInsert (c, dt, vd, vm, imm) in
        index_check_opc_c opc c "VSLI" 4);

    TS.add_simple_test
      ~title:"VectorShiftRight"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vm = armxdoublereg_op RD in
        let imm6 = intvalue ~min:16 32 in
        let esize = 16 in
        let sam = 32 - imm6 in
        let dt = VfpSignedInt esize in
        let imm = TR.tget_ok (mk_arm_immediate_op true 4 (mkNumerical sam)) in
        let c = cc () in
        let opc = VectorShiftRight (c, dt, vd, vm, imm) in
        index_check_opc_c opc c "VSHR" 4);

    TS.add_simple_test
      ~title:"VectorShiftRightInsert"
      (fun () ->
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let imm6 = intvalue ~min:32 64 in
        let esize = 32 in
        let sam = 64 - imm6 in
        let dt = VfpSize esize in
        let imm = TR.tget_ok (mk_arm_immediate_op true 4 (mkNumerical sam)) in
        let c = cc () in
        let opc = VectorShiftRightInsert (c, dt, vd, vm, imm) in
        index_check_opc_c opc c "VSRI" 4);

    TS.add_simple_test
      ~title:"VectorShiftRightAccumulate"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vm = armxdoublereg_op RD in
        let imm6 = intvalue 64 in
        let esize = 64 in
        let sam = 64 - imm6 in
        let dt = VfpSize esize in
        let imm = TR.tget_ok (mk_arm_immediate_op true 4 (mkNumerical sam)) in
        let c = cc () in
        let opc = VectorShiftRightAccumulate (c, dt, vd, vm, imm) in
        index_check_opc_c opc c "VSRA" 4);

    TS.add_simple_test
      ~title:"VectorShiftRightNarrow"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vm = armxquadreg_op RD in
        let esize = 8 in
        let imm6 = intvalue ~min:8 16 in
        let sam = 16 - imm6 in
        let dt = VfpInt esize in
        let imm = TR.tget_ok (mk_arm_immediate_op true 4 (mkNumerical sam)) in
        let c = cc () in
        let opc = VectorShiftRightNarrow (c, dt, vd, vm, imm) in
        index_check_opc_c opc c "VSHRN" 4);

    TS.add_simple_test
      ~title:"VStoreRegister"
      (fun () ->
        let vd = armxsinglereg_op RD in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let imm = 4 * (intvalue 256) in
        let mem = armimmoffsetaddress_op rnreg imm WR in
        let c = cc () in
        let opc = VStoreRegister (c, vd, rn, mem) in
        index_check_opc_c opc c "VSTR" 3);

    TS.add_simple_test
      ~title:"VectorStoreMultipleDecrementBefore"
      (fun () ->
        let wb = boolvalue () in
        let rl = armxsinglereglist_op RD in
        let regs = List.length rl#get_extension_register_op_list in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let mem = mk_arm_mem_multiple_op ~size:4 rnreg regs WR in
        let c = cc () in
        let opc = VectorStoreMultipleDecrementBefore (wb, c, rn, rl, mem) in
        index_check_opc_c opc c "VSTMDB" 4);
    
    TS.add_simple_test
      ~title:"VectorStoreMultipleIncrementAfter"
      (fun () ->
        let wb = boolvalue () in
        let rl = armxdoublereglist_op RD in
        let regs = List.length rl#get_extension_register_op_list in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg RD in
        let mem = mk_arm_mem_multiple_op ~size:8 rnreg regs WR in
        let c = cc () in
        let opc = VectorStoreMultipleIncrementAfter (wb, c, rn, rl, mem) in
        index_check_opc_c opc c "VSTM" 4);

    TS.add_simple_test
      ~title:"VectorStoreOne (multiple single elements)"
      (fun () ->
        let wb = true in
        let wback = SIMDBytesTransferred 8 in
        let alignment = 4 in
        let sz = intvalue 4 in
        let ebytes = 1 lsl sz in
        let esize = 8 * ebytes in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg WR in
        let rm = armreg_op RD in
        let mem = mk_arm_simd_address_op rnreg alignment wback WR in
        let vd = prefix_bit (intvalue 2) (intvalue 16) in
        let rl = arm_simd_reg_list_op XDouble [vd] RD in
        let c = cc () in
        let opc = VectorStoreOne (wb, c, VfpSize esize, rl, rn, mem, rm) in
        index_check_opc_c opc c "VST1" 6);

    TS.add_simple_test
      ~title:"VectorStoreTwo (single 2-elt from one lane)"
      (fun () ->
        let wb = true in
        let wback = SIMDBytesTransferred 8 in
        let alignment = 4 in
        let sz = intvalue 4 in
        let ebytes = 1 lsl sz in
        let esize = 8 * ebytes in
        let rnreg = armreg () in
        let rn = arm_register_op rnreg WR in
        let rm = armreg_op RD in
        let mem = mk_arm_simd_address_op rnreg alignment wback WR in
        let vd = prefix_bit (intvalue 2) (intvalue 16) in
        let rl = arm_simd_reg_list_op XDouble [vd; vd + 1] RD in
        let c = cc () in
        let opc = VectorStoreTwo (wb, c, VfpSize esize, rl, rn, mem, rm) in
        index_check_opc_c opc c "VST2" 6);

    TS.add_simple_test
      ~title:"VectorStoreFour (single 4-elt from one lane)"
      (fun () ->
        let c = ACCUnconditional in
        let rmreg = intvalue 16 in
        let rm = get_arm_reg rmreg in
        let rmop = arm_register_op rm RD in
        let rn = armreg () in
        let d = intvalue 2 in
        let vd = prefix_bit d (intvalue 15) in
        let sz = intvalue 3 in
        let (ebytes, esize, index, inc, alignment) =
          match sz with
          | 0 -> (1, 8, intvalue 8, 1, select_int [1; 4])
          | 1 -> (2, 16, intvalue 4, select_int [1; 2], select_int [1; 8])
          | _ -> (4, 32, intvalue 2, select_int [1; 2], select_int [1; 4; 8; 16]) in
        let (wb, wback) =
          match rmreg with
          | 15 -> (false, SIMDNoWriteback)
          | 13 -> (true, SIMDBytesTransferred ebytes)
          | _ -> (true, SIMDAddressOffsetRegister rm) in
        let rnop = arm_register_op rn (if wb then WR else RD) in
        let mem = mk_arm_simd_address_op rn alignment wback in
        let rlist =
          arm_simd_reg_elt_list_op
            XDouble [vd; vd + inc; vd + (2 * inc); vd + (3 * inc)] index esize in
        let opc = VectorStoreFour (wb, c, VfpSize esize, rlist WR, rnop, mem RD, rmop) in
        index_check_opc_c opc c "VST4" 6);

    TS.add_simple_test
      ~title:"VectorSubtract (floating point)"
      (fun () ->
        let dp = boolvalue () in
        let vd = armvfp_op dp WR in
        let vn = armvfp_op dp RD in
        let vm = armvfp_op dp RD in
        let dt = if dp then VfpFloat 64 else VfpFloat 32 in
        let c = cc () in
        let opc = VectorSubtract (c, dt, vd, vn, vm) in
        index_check_opc_c opc c "VSUB" 4);

    TS.add_simple_test
      ~title:"VectorTableLookup"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vm = armxdoublereg_op RD in
        let n = prefix_bit (intvalue 2) (intvalue 14) in
        let rl = arm_extension_register_list_op XDouble n 3 RD in
        let dt = VfpSize 8 in
        let c = cc () in
        let opc = VectorTableLookup (c, dt, vd, rl, vm) in
        index_check_opc_c opc c "VTBL" 4);

    TS.add_simple_test
      ~title:"VectorTranspose"
      (fun () ->
        let vd = armxdoublereg_op WR in
        let vm = armxdoublereg_op RD in
        let dt = VfpSize (8 lsl (intvalue 4)) in
        let c = cc () in
        let opc = VectorTranspose (c, dt, vd, vm) in
        index_check_opc_c opc c "VTRN" 3);

    TS.add_simple_test
      ~title:"VectorZip"
      (fun () ->
        let vd = armxquadreg_op WR in
        let vm = armxquadreg_op RD in
        let dt = VfpSize (8 lsl (intvalue 4)) in
        let c = cc () in
        let opc = VectorZip (c, dt, vd, vm) in
        index_check_opc_c opc c "VZIP" 3);

    TS.add_simple_test
      ~title:"NoOperation"
      (fun () ->
        let c = cc () in
        let opc = NoOperation c in
        index_check_opc_c opc c "NOP" 0);

    TS.add_simple_test
      ~title:"SupervisorCall"
      (fun () ->
        let c = cc () in
        let op = intvalue e24 in
        let imm32 = arm_immediate_op (TR.tget_ok (signed_immediate_from_int op)) in
        let opc = SupervisorCall (c, imm32) in
        index_check_opc_c opc c "SVC" 1);
    
    TS.launch_tests ();
    armd#write_xml fNode;
    doc#setNode root;
    file_output#saveFile filename doc#toPretty;
    save_bdictionary "armdictionary_bdict.xml"
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    arm_opcode_tests ();
    TS.exit_file ()
  end
       

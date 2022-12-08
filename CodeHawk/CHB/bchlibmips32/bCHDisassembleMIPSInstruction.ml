(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

(* bchlibmips32 *)
open BCHMIPSDisassemblyUtils
open BCHMIPSOpcodeRecords
open BCHMIPSOperand
open BCHMIPSTypes

module TR = CHTraceResult


let parse_branch
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (rrs:int)
      (rrt:int)
      (immval:int) =
  let tgtop = mk_mips_target_op ch base immval in
  let rs = select_mips_reg rrs in
  let r_op = mips_register_op in
  let imm = mkNumerical immval in
  match rrt with
  | 0 -> BranchLTZero (r_op rs RD, tgtop)
  | 1 -> BranchGEZero (r_op rs RD, tgtop)
  | 2 -> BranchLTZeroLikely (r_op rs RD, tgtop)
  | 3 -> BranchGEZeroLikely (r_op rs RD, tgtop)
  | 12 -> TrapIfEqualImmediate (r_op rs RD, mips_immediate_op true 2 imm)
  | 16 -> BranchLTZeroLink (r_op rs RD, tgtop)
  | 17 when rrs = 0 -> BranchLink tgtop
  | 17 -> BranchGEZeroLink (r_op rs RD, tgtop)
  | _ ->
     begin
       pverbose [ STR "branch with rt: " ; INT rrt ; NL ] ;
       OpInvalid
     end


let parse_I_opcode
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (opc:int)
      (rrs:int)
      (rrt:int)
      (immval:int) =
  let rs = select_mips_reg rrs in
  let rt = select_mips_reg rrt in
  let imm = mkNumerical immval in  
  let r_op = mips_register_op in
  let f_op = mips_fp_register_op in
  let i_op = mips_indirect_register_op in
  let imm_op = mips_immediate_op in
  let tgt_op () = mk_mips_target_op ch base immval in
  match opc with
  | 1 -> parse_branch ch base rrs rrt immval
  | 4 when rrs = 0 && rrt = 0 && immval = (-1) -> Halt
  | 4 when rrs = 0 && rrt = 0 -> Branch (tgt_op ())
  | 4 -> BranchEqual (r_op rs RD,r_op rt RD,tgt_op ())
  | 5 -> BranchNotEqual (r_op rs RD,r_op rt RD,tgt_op ())
  | 6 -> BranchLEZero (r_op rs RD,tgt_op ())
  | 7 -> BranchGTZero (r_op rs RD,tgt_op ())
  | 8 -> AddImmediate (r_op rt WR,r_op rs RD,imm_op true 2 imm)
  | 9 when rrs = 0 -> LoadImmediate (r_op rt WR,imm_op true 2 imm)    (* pseudo *)
  | 9 -> AddImmediateUnsigned (r_op rt WR,r_op rs RD,imm_op true 2 imm)
  | 10 -> SetLTImmediate (r_op rt WR,r_op rs RD,imm_op true 2 imm)
  | 11 -> SetLTImmediateUnsigned (r_op rt WR,r_op rs RD,imm_op true 2 imm)
  | 12 -> AndImmediate (r_op rt WR,r_op rs RD,imm_op false 2 imm)
  | 13 -> OrImmediate (r_op rt WR,r_op rs RD,imm_op false 2 imm)
  | 14 -> XorImmediate (r_op rt WR,r_op rs RD,imm_op false 2 imm)
  | 15 when rrs = 0 -> LoadUpperImmediate (r_op rt WR,imm_op false 2 imm)
  | 15 -> AddUpperImmediate (r_op rt WR,r_op rs RD, imm_op true 2 imm)
  | 20 -> BranchEqualLikely (r_op rs RD,r_op rt RD,tgt_op ())
  | 18 ->
     (match rrs with
      | 0 -> MoveWordFromCoprocessor2 (r_op rt WR, immval lsr 3, immval mod 8)
      | 3 -> MoveWordFromHighHalfCoprocessor2 (r_op rt WR, immval lsr 3, immval mod 8)
      | 4 -> MoveWordToCoprocessor2 (r_op rt RD, immval lsr 3, immval mod 8)
      | _ ->
         begin
           pverbose [ STR "    I-opcode 18: " ; INT rrs ; NL ];
           OpInvalid
         end)
  | 21 -> BranchNotEqualLikely (r_op rs RD,r_op rt RD,tgt_op ())
  | 22 -> BranchLEZeroLikely (r_op rs RD,tgt_op ())
  | 23 -> BranchGTZeroLikely (r_op rs RD,tgt_op ())
  | 32 -> LoadByte (r_op rt WR,i_op rs imm RD)
  | 33 -> LoadHalfWord (r_op rt WR,i_op rs imm RD)
  | 34 -> LoadWordLeft (r_op rt WR,i_op rs imm RD)
  | 35 -> LoadWord (r_op rt WR,i_op rs imm RD)
  | 36 -> LoadByteUnsigned (r_op rt WR,i_op rs imm RD)
  | 37 -> LoadHalfWordUnsigned (r_op rt WR,i_op rs imm RD)
  | 38 -> LoadWordRight (r_op rt WR,i_op rs imm RD)
  | 40 -> StoreByte (i_op rs imm WR,r_op rt RD)
  | 41 -> StoreHalfWord (i_op rs imm WR,r_op rt RD)
  | 42 -> StoreWordLeft (i_op rs imm WR,r_op rt RD)
  | 43 -> StoreWord (i_op rs imm WR,r_op rt RD)
  | 46 -> StoreWordRight (i_op rs imm WR, r_op rt RD)
  | 48 -> LoadLinkedWord (r_op rt WR, i_op rs imm RD)
  | 49 -> LoadWordFP (f_op rrt WR,i_op rs imm RD)
  | 51 -> Prefetch (i_op rs imm RD, rrt)
  | 53 -> LoadDoublewordToFP (f_op rrt WR,i_op rs imm RD)
  | 56 -> StoreConditionalWord (i_op rs imm WR, r_op rt RD)
  | 57 -> StoreWordFromFP (i_op rs imm RD, f_op rrt RD)
  | 61 -> StoreDoublewordFromFP (i_op rs imm RD, f_op rrt RD)
  | _ ->
     begin
       pverbose [ STR "     I-opcode: " ; INT opc ; NL ] ;
       OpInvalid
     end


let parse_J_opcode (ch:pushback_stream_int) (base:doubleword_int) (opc:int) (immval:int) =
  match opc with
  | 2 -> Jump (mk_mips_absolute_target_op ~delay:4 ch base immval)
  | 3 -> JumpLink (mk_mips_absolute_target_op ~delay:4 ch base immval)
  | _ ->
  begin
    pverbose [ STR "     J-opcode: " ; INT opc ; NL ] ;
    OpInvalid
  end


let parse_R_opcode (opc:int) (rrs:int) (rrt:int) (rrd:int) (samt:int) (fnct:int) =
  let rs = select_mips_reg rrs in
  let rt = select_mips_reg rrt in
  let rd = select_mips_reg rrd in
  let r_op = mips_register_op in
  let imm_op i = mips_immediate_op false 1 (mkNumerical i) in
  match fnct with
  | 0 when rrs = 0 && rrt = 0 && rrd = 0 && samt = 0 -> NoOperation
  | 0 -> ShiftLeftLogical (r_op rd WR,r_op rt RD,imm_op samt)
  | 2 -> ShiftRightLogical (r_op rd WR,r_op rt RD,imm_op samt)
  | 3 -> ShiftRightArithmetic (r_op rd WR,r_op rt RD,imm_op samt)
  | 4 -> ShiftLeftLogicalVariable (r_op rd WR,r_op rt RD,r_op rs RD)
  | 6 -> ShiftRightLogicalVariable (r_op rd WR,r_op rt RD,r_op rs RD)
  | 7 -> ShiftRightArithmeticVariable (r_op rd WR,r_op rt RD,r_op rs RD)
  | 8 -> JumpRegister (r_op rs RD)
  | 9 -> JumpLinkRegister (r_op rd WR,r_op rs RD)
  | 10 -> MoveConditionalZero (r_op rd WR, r_op rs RD, r_op rt RD)
  | 11 -> MoveConditionalNotZero (r_op rd WR, r_op rs RD, r_op rt RD)
  (* 12: Syscall, handled in MIPSDisassemblyUtils *)
  | 16 -> MoveFromHi (r_op rd WR,mips_hi_op RD)
  | 17 -> MoveToHi (mips_hi_op WR, r_op rs RD)
  | 18 -> MoveFromLo (r_op rd WR,mips_lo_op RD)
  | 19 -> MoveToLo (r_op rs RD,mips_lo_op RD)
  | 24 -> MultiplyWord (mips_hi_op WR,mips_lo_op WR,r_op rs RD, r_op rt RD)
  | 25 -> MultiplyUnsignedWord (mips_hi_op WR,mips_lo_op WR,r_op rs RD, r_op rt RD)
  | 26 -> DivideWord (mips_hi_op WR,mips_lo_op WR,r_op rs RD,r_op rt RD)
  | 27 -> DivideUnsignedWord (mips_hi_op WR,mips_lo_op WR, r_op rs RD, r_op rt RD)
  | 32 -> Add (r_op rd WR,r_op rs RD,r_op rt RD)
  | 33 when rrd = 0 -> NoOperation                             (* pseudo *)
  | 33 when rrs = 0 -> Move (r_op rd WR, r_op rt RD)           (* pseudo *)
  | 33 when rrt = 0 -> Move (r_op rd WR, r_op rs RD)           (* pseudo *)
  | 33 -> AddUnsigned (r_op rd WR,r_op rs RD,r_op rt RD)
  | 34 -> Subtract (r_op rd WR,r_op rs RD,r_op rt RD)
  | 35 -> SubtractUnsigned (r_op rd WR,r_op rs RD,r_op rt RD)
  | 36 -> And (r_op rd WR,r_op rs RD,r_op rt RD)
  | 37 when rrs = 1 && rrt = 0 && rrd  = 1 &&  samt = 0 -> NoOperation
  | 37 -> Or (r_op rd WR,r_op rs RD,r_op rt RD)
  | 38 -> Xor (r_op rd WR,r_op rs RD,r_op rt RD)
  | 39 -> Nor (r_op rd WR,r_op rs RD,r_op rt RD)
  | 42 -> SetLT (r_op rd WR,r_op rs RD,r_op rt RD)
  | 43 -> SetLTUnsigned (r_op rd WR,r_op rs RD,r_op rt RD)
  | 52 -> TrapIfEqual ((rrd lsl 5) + samt,r_op rs RD,r_op rt RD)
  | _ ->
     begin
       pverbose [ STR "     R-opcode: " ; INT fnct ; NL ] ;
       OpInvalid
     end


let parse_R2_opcode (opc:int) (rrs:int) (rrt:int) (rrd:int) (samt:int) (fnct:int) =
  let rs = select_mips_reg rrs in
  let rt = select_mips_reg rrt in
  let rd = select_mips_reg rrd in
  let r_op = mips_register_op in
  match fnct with
  | 0 -> MultiplyAddWord
           (mips_hi_op RW, mips_lo_op RW, r_op rs RD, r_op rt RD)
  | 1 -> MultiplyAddUnsignedWord
           (mips_hi_op RW, mips_lo_op RW, r_op rs RD, r_op rt RD)
  | 2 -> MultiplyWordToGPR (r_op rd WR, r_op rs RD, r_op rt RD)
  | 32 -> CountLeadingZeros (r_op rd WR, r_op rs RD)
  | _ ->
     begin
       pverbose [ STR "    R2-opcode: " ; INT fnct ; NL ] ;
       OpInvalid
     end


let parse_R3_opcode (opc:int) (rrs:int) (rrt:int) (rrd:int) (samt:int) (fnct:int) =
  let rd = select_mips_reg rrd in
  let rt = select_mips_reg rrt in
  let rs = select_mips_reg rrs in
  let r_op = mips_register_op in
  match fnct with
  | 0 -> ExtractBitField (r_op rt WR, r_op rs RD, rrd, samt)
  | 4 -> InsertBitField (r_op rt WR, r_op rs RD,rrd,samt)
  | 32 ->
     (match samt with
      | 2 -> WordSwapBytesHalfwords (r_op rd WR, r_op rt RD)
      | 16 -> SignExtendByte (r_op rd WR, r_op rt RD)
      | 24 -> SignExtendHalfword (r_op rd WR, r_op rt RD)
      | _ ->
         begin
           pverbose [ STR "    R3-opcode BSHFL: " ; INT samt ; NL ];
           OpInvalid
         end)
  | 59 -> ReadHardwareRegister (r_op rt WR, rrd)
  | _ ->
     begin
       pverbose [ STR "    R3-opcode fnct: " ; INT fnct ; NL ];
       OpInvalid
     end


let parse_FPMC_opcode (opc:int) (rrs:int) (cc:int) (tf:int) (rrd:int) (ffd:int) (funct:int) =
  let rs = select_mips_reg rrs in
  let rd = select_mips_reg rrd in
  let r_op = mips_register_op in
  match funct with
  | 1 ->
     (match tf with
      | 0 -> MovF (cc, r_op rd WR, r_op rs RD)
      | 1 -> MovT (cc, r_op rd WR, r_op rs RD)
      | _ ->
         begin
           pverbose [ STR "     FPCM-opcode: " ; INT tf ; NL ] ;
           OpInvalid
         end)
  | _ ->
     begin
       pverbose [ STR "    FPCM-opcode: " ; INT funct ; NL ] ;
       OpInvalid
     end


let parse_FPRI_opcode (opc:int) (sub:int) (rrt:int) (fs:int) (imm:int) =
  let rt = select_mips_reg rrt in
  let rd = select_mips_reg fs in
  let r_op = mips_register_op in
  let f_op = mips_fp_register_op in
  match sub with
  | 0 ->
     (match imm with
      | 0 -> MoveWordFromFP (r_op rt WR, f_op fs RD)
      | _ when imm < 8 ->
         MoveFromCoprocessor0 (r_op rt WR, r_op rd RD, imm)
      | _ ->
         begin
           pverbose [ STR "  FPRIType-opcode 0: " ; INT imm ; NL ];
           OpInvalid
         end)
  | 2 ->
     (match imm with
      | 0 -> ControlWordFromFP (r_op rt WR, f_op fs RD)
      | _ when imm < 8 ->
         MoveFromHighCoprocessor0 (r_op rt WR, r_op rd RD, imm)
      | _ ->
         begin
           pverbose [ STR "  FPRIType-opcode 2: " ; INT imm ; NL ];
           OpInvalid
         end)
  | 3 ->
     (match imm with
      | 0 -> MoveWordFromHighHalfFP (r_op rt WR, f_op fs RD)
      | _ ->
         begin
           pverbose [ STR "   FPRIType-opcode 3: " ; INT imm ; NL ];
           OpInvalid
         end)
  | 4 ->
     (match imm with
      | 0 -> MoveWordToFP (r_op rt RD, f_op fs WR)
      | _ when imm < 8 ->
         MoveToCoprocessor0 (r_op rt RD, r_op rd RD, imm)
      | _ ->
         begin
           pverbose [ STR "   FPRType-opcode 4: " ; INT imm ; NL ];
           OpInvalid
         end)
  | 6 ->
     (match imm with
      | 0 -> ControlWordToFP (r_op rt RD, f_op fs WR)
      | _ when imm < 8 ->
         MoveToHighCoprocessor0 (r_op rt RD, r_op rd RD, imm)
      | _ ->
         begin
           pverbose [ STR "   FPRIType-opcode 6: " ; INT imm ; NL ];
           OpInvalid
         end)
  | 7 ->
     (match imm with
      | 0 -> MoveWordToHighHalfFP (r_op rt RD, f_op fs WR )
      | _ ->
         begin
           pverbose [ STR "   FPRIType-opcode 7: " ; INT imm ; NL ];
           OpInvalid
         end)
  | _ ->
     begin
       pverbose [ STR "   FPRIType-opcode: " ; INT sub ; NL ] ;
       OpInvalid
     end


let parse_FPR_opcode (opc:int) (fmt:int) (ft:int) (fs:int) (fd:int) (funct:int) =
  let fmt = code_to_mips_fp_format fmt in
  let f_op = mips_fp_register_op in
  match funct with
  | 0 -> FPAddfmt (fmt,f_op fd WR, f_op fs RD, f_op ft RD)
  | 1 -> FPSubfmt (fmt,f_op fd WR, f_op fs RD, f_op ft RD)
  | 2 -> FPMulfmt (fmt,f_op fd WR, f_op fs RD, f_op ft RD)
  | 3 -> FPDivfmt (fmt,f_op fd WR, f_op fs RD, f_op ft RD)
  | 4 -> FPSqrtfmt (fmt,f_op fd WR, f_op fs RD)
  | 5 -> FPAbsfmt (fmt,f_op fd WR, f_op fs RD)
  | 6 -> FPMovfmt (fmt,f_op fd WR, f_op fs RD)
  | 7 -> FPNegfmt (fmt,f_op fd WR, f_op fs RD)
  | 8 -> FPRoundLfmt (fmt, f_op fd WR, f_op fs RD)
  | 9 -> FPTruncLfmt  (fmt, f_op fd WR, f_op fs RD)
  | 10 -> FPCeilLfmt (fmt, f_op fd WR, f_op fs RD)
  | 11 -> FPFloorLfmt (fmt, f_op fd WR, f_op fs RD)
  | 12 -> FPRoundWfmt (fmt, f_op fd WR, f_op fs RD)
  | 13 -> FPTruncWfmt (fmt, f_op fd WR, f_op fs RD)
  | 14 -> FPCeilWfmt (fmt, f_op fd WR, f_op fs RD)
  | 15 -> FPFloorWfmt (fmt, f_op fd WR, f_op fs RD)
  | 22 -> FPRSqrtfmt (fmt,f_op fd WR, f_op fs RD)
  | 32 -> FPCVTSfmt (fmt,f_op fd WR, f_op fs RD)
  | 33 -> FPCVTDfmt (fmt,f_op fd WR, f_op fs RD)
  | 36 -> FPCVTWfmt (fmt,f_op fd WR, f_op fs RD)
  | 37 -> FPCVTLfmt (fmt,f_op fd WR, f_op fs RD)
  | 40 -> FPCVTSPfmt (fmt,f_op fd WR, f_op fs RD)
  | _ ->
     begin
       pverbose [ STR "     FPRType-opcode: " ; INT funct  ; NL ] ;
       OpInvalid
     end


let parse_FPICC_opcode
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (opc:int)
      (sub:int)
      (cc:int)
      (nd:int)
      (tf:int)
      (offset:int) =
  let offset = mk_mips_target_op ch base offset in
  match (nd,tf) with
  | (0,0) -> BranchFPFalse (cc,offset)
  | (0,1) -> BranchFPTrue (cc,offset)
  | (1,0) -> BranchFPFalseLikely (cc,offset)
  | (1,1) -> BranchFPTrueLikely (cc,offset)
  | _ ->
     begin
       pverbose [STR "     FPICC-opcode: "; INT nd; STR ", "; INT tf; NL];
       OpInvalid
     end


let parse_FPCompare_opcode
      (fmt:int)
      (ft:int)
      (fs:int)
      (cc:int)
      (cond:int) =
  let fmt = code_to_mips_fp_format fmt in
  let f_op f = mips_fp_register_op f RD in
  let exc = cond lsr 3 in
  let predicate = cond mod 8 in
  FPCompare (fmt, cc, predicate, exc, f_op fs, f_op ft)


let parse_opcode
      (ch:pushback_stream_int)
      (base:doubleword_int)
      (instrbytes:doubleword_int): mips_opcode_t =
  let p = TR.tget_ok (numerical_to_doubleword (mkNumerical ch#pos)) in
  let addr = (base#add p)#add_int (-4) in
  let instr = decompose_instr instrbytes in
  let opcode =
    match instr with
    | SyscallType code -> Syscall code
    | RBreakType (_,code,_) -> Break code
    | RSyncType (_,_,stype,_) -> Sync stype
    | IType (opc,rs,rt,imm) -> parse_I_opcode ch base opc rs rt imm
    | JType (opc,tgt) -> parse_J_opcode ch base opc tgt
    | RType (opc,rs,rt,rd,sa,fn) -> parse_R_opcode opc rs rt rd sa fn
    | R2Type (opc,rs,rt,rd,sa,fn) -> parse_R2_opcode opc rs rt rd sa fn
    | R3Type (opc,rs,rt,rd,sa,fn) -> parse_R3_opcode opc rs rt rd sa fn
    | FPMCType (opc,rs,cc,nd,tf,rd,fd,funct) -> parse_FPMC_opcode opc rs cc tf rd fd funct
    | FPRIType (opc,sub,rt,fs,imm) -> parse_FPRI_opcode opc sub rt fs imm
    | FPRType (opc,fmt,ft,fs,fd,funct) -> parse_FPR_opcode opc fmt ft fs fd funct
    | FPICCType (opc,sub,cc,nd,tf,offset) -> parse_FPICC_opcode ch base opc sub cc nd tf offset
    | FPCompareType (opc,fmt,ft,fs,cc,cond) -> parse_FPCompare_opcode fmt ft fs cc cond
    | FormatUnknown(opc,otherbits) -> OpInvalid in
  let _ = match opcode with
    | OpInvalid ->
       pverbose [
           addr#toPretty;
           STR "  ";
           STR (instrbytes#to_fixed_length_hex_string);
           STR " not recognized";
           NL]
    | _ -> () in
  opcode


let disassemble_mips_instruction
      (ch:pushback_stream_int) (base:doubleword_int) (instrbytes:doubleword_int) =
  try
    parse_opcode ch base instrbytes
  with
  | IO.No_more_input ->
    let address = base#add_int ch#pos in
    begin
      ch_error_log#add
        "no more input"
	(LBLOCK [
             STR "No more input at position ";
             address#toPretty;
             STR " (";
	     INT ch#pos;
             STR ")"]);
      raise IO.No_more_input
    end

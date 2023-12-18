(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHTraceResult
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

type mips_fp_format_t =
  | FPSingle   (* 16 *)
  | FPDouble   (* 17 *)
  | FPFixedWord  (* 20 *)
  | FPFixedLong  (* 21 *)
  | FPPair (* 22 *)

type mips_instr_format_t =
  | SyscallType of int
  | RSyncType of   (* SPECIAL:0 *)
      int (* opcode:6 (0) *)
      * int (* 0:15 bits *)
      * int (* stype:5 *)
      * int (* funct:6 *)
  | RBreakType of  (* SPECIAL:0 *)
      int (* opcode:6 (0) *)
      * int (* code:20 *)
      * int (* funct:6 *)
  | RType of     (* SPECIAL:0 *)
      int (* opcode:6 (0) *)
      * int (* rs:5 *)
      * int (* rt:5 *)
      * int (* rd:5 *)
      * int (* shamt:5 *)
      * int (* funct:6 *)
  | R2Type of    (*  SPECIAL2:28 *)
      int (* opcode:6 (28) *)
      * int (* rs:5 *)
      * int (* rt:5 *)
      * int (* rd:5 *)
      * int (* shamt:5 *)
      * int (* funct:6 *)
  | R3Type of    (*  SPECIAL3:31 *)
      int (* opcode:6 (31) *)
      * int (* rs:5 *)
      * int (* rt:5 *)
      * int (* rd:5 *)
      * int (* shamt:5 *)
      * int (* funct:6 *)
  | IType of
      int (* opcode:6 *)
      * int (* rs:5 *)
      * int (* rt:5 *)
      * int (* immediate:16 *)
  | JType of
      int (* opcode:6 (2,3) *)
      * int (* address:26 *)
  | FPMCType of (* Floating Point (Register) Move Conditional *)
      int (* opcode:6 (SPECIAL:0) *)
      * int (* rs:5 *)
      * int (* cc:3 *)
      * int (* nd:1 *)
      * int (* tf:1 *)
      * int (* rd:5 *)
      * int (* fd:5 *)
      * int (* funct:6 *)
  | FPRType of
      int (* opcode:6 (COP1:17) *)
      * int (* fmt:5 *)
      * int (* ft:5 *)
      * int (* fs:5 *)
      * int (* fd:5 *)
      * int (* funct:6 *)
  | FPRIType of   (* Floating Point Register Immediate *)
      int (* opcode:6 (COP1:17) *)
      * int (* sub:5 *)
      * int (* rt:5 *)
      * int (* fs:5 *)
      * int (* imm:11 *)
  | FPCompareType of
      int (* opcode:6 (COP1:17) *)
      * int (* fmt:5 *)
      * int (* ft:5 *)
      * int (* fs:5 *)
      * int (* cc:3 *)
      (* 4 bits: 0011 *)
      * int (* cond:4 *)
 | FPICCType of  (* Floating Point Immediate with Condition Code *)
      int (* opcode:6 (COP1:17) *)
      * int (* sub:5  (BCC1:8) *)
      * int (* cc:3  *)
      * int (* nd:1 *)
      * int (* tf:1 *)
      * int (* offset:16 *)
 | FormatUnknown of
     int (* opcode:6 *)
     * int (* rest:26 *)

(* ================================================================= Operand === *)

type mips_operand_kind_t =
  | MIPSReg of mips_reg_t
  | MIPSSpecialReg of mips_special_reg_t
  | MIPSFPReg of int
  | MIPSIndReg of mips_reg_t * numerical_t
  | MIPSAbsolute of doubleword_int
  | MIPSImmediate of immediate_int

type mips_operand_mode_t = RD | WR | RW

class type mips_operand_int =
  object ('a)

    (* accessors *)
    method get_kind: mips_operand_kind_t
    method get_mode: mips_operand_mode_t
    method get_register: mips_reg_t
    method get_register_index: int
    method get_indirect_register: mips_reg_t
    method get_indirect_register_index: int
    method get_indirect_offset: numerical_t
    method get_absolute_address: doubleword_int
    method get_address_alignment: int

    (* converters *)
    method to_register: register_t
    method to_numerical: numerical_t
    method to_address: floc_int -> xpr_t
    method to_variable: floc_int -> variable_t
    method to_expr: floc_int -> xpr_t
    method to_lhs : floc_int -> variable_t * cmd_t list

    (* predicate *)
    method is_read : bool
    method is_write: bool
    method is_register: bool
    method is_register_zero: bool
    method is_special_register: bool
    method is_absolute_address: bool

    (* printing *)
    method toString: string
    method toPretty: pretty_t

  end

type not_code_t = DataBlock of data_block_int

type mips_opcode_t =
  | Add of                                                     (* ADD; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | AddImmediate of                         (* ADDI; I-type; arithmetic/logic *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* imm: immediate *)
  | AddImmediateUnsigned of                (* ADDIU; I-type; arithmetic/logic *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* imm: immediate *)
  | AddUpperImmediate of                               (* AUI; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* imm: immediate *)
  | AddUnsigned of                                            (* ADDU; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | And of                                                     (* AND; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | AndImmediate of                         (* ANDI; I-type; arithmetic/logic *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* imm: immediate *)
  | Branch of                                            (* B: I-type: branch *)
      mips_operand_int   (* offset: relative target offset *)
  | BranchEqual of                                     (* BEQ; I-type: branch *)
      mips_operand_int   (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchEqualLikely of                              (* BEQL; I-type: branch *)
      mips_operand_int   (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchFPFalse of                                      (* BC1F; FPICC Type *)
      int                (* cc: FP condition code *)
      * mips_operand_int (* offset: relatieve target offset *)
  | BranchFPFalseLikely of                               (* BC1FL; FPICC Type *)
      int                (* cc: FP condition code *)
      * mips_operand_int (* offset: relatieve target offset *)
  | BranchFPTrue of                                       (* BC1T; FPICC Type *)
      int                (* cc: FP condition code *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchFPTrueLikely of                                (* BC1TL; FPICC Type *)
      int                (* cc: FP condition code *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchGEZero of                                   (* BGEZ; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchGEZeroLikely of                            (* BGEZL; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchGEZeroLink of                             (* BGEZAL; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchGTZero of                                   (* BGTZ; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchGTZeroLikely of                            (* BGTZL; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchLEZero of                                   (* BLEZ; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchLEZeroLikely of                            (* BLEZL; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchLink of                               (* BAL: I-type: function call *)
      mips_operand_int   (* offset: relative target offset *)
  | BranchLTZero of                                   (* BLTZ; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchLTZeroLikely of                            (* BLTZL; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchLTZeroLink of                             (* BLTZAL; I-type: branch *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchNotEqual of                                  (* BNE; I-type: branch *)
      mips_operand_int   (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
      * mips_operand_int (* offset: relative target offset *)
  | BranchNotEqualLikely of                           (* BNEL; I-type: branch *)
      mips_operand_int   (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
      * mips_operand_int (* offset: relative target offset *)
  | Break of                                            (* BREAK; RBreak type *)
      int                (* code: software parameters *)
  | ControlWordFromFP of  (* FPRI Type *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* fs: source *)
  | ControlWordToFP of    (* FPRI Type *)
      mips_operand_int   (* rt: source *)
      * mips_operand_int (* fs: destination *)
  | CountLeadingZeros of                                      (* CLZ; R2-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source *)
  | DivideWord of                                              (* DIV; R-type *)
      mips_operand_int   (* hi: special register HI *)
      * mips_operand_int (* lo: special register LO *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | DivideUnsignedWord of                                     (* DIVU; R-type *)
      mips_operand_int   (* hi: special register HI *)
      * mips_operand_int (* lo: special register LO *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | ExtractBitField of                                        (* EXT; R3-type *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source *)
      * int              (* pos: starting position *)
      * int              (* size: number of bits to be extracted *)
  | InsertBitField of                                         (* INS; R3-type *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source *)
      * int              (* pos: starting position *)
      * int              (* size: number of bits to be inserted *)
  | FPAbsfmt of                                          (* ABS.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPAddfmt of                                          (* ADD.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source 1 *)
      * mips_operand_int (* ft: source 2 *)
  | FPCeilLfmt of                                     (* CEIL.L.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPCeilWfmt of                                     (* CEIL.W.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPCompare of                                                (* C.cond.fmt *)
      mips_fp_format_t
      * int              (* cc: condition code *)
      * int              (* cond: predicate *)
      * int              (* exception *)
      * mips_operand_int (* fs: source 1 *)
      * mips_operand_int (* ft: source 2 *)
  | FPCVTDfmt of                                        (* CVTD.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPCVTLfmt of                                        (* CVTL.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPCVTSfmt of                                        (* CVTS.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPCVTSPfmt of                                      (* CVTSP.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPCVTWfmt of                                        (* CVTW.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPDivfmt of                                          (* DIV.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source 1 *)
      * mips_operand_int (* ft: source 2 *)
  | FPFloorLfmt of                                   (* FLOOR.L.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPFloorWfmt of                                   (* FLOOR.W.fmt; FPR type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPRoundLfmt of                                   (* ROUND.L.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPMovfmt of                                          (* MOV.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPMulfmt of                                          (* MUL.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source 1 *)
      * mips_operand_int (* fd: source 2 *)
  | FPNegfmt of                                          (* NEG.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPRoundWfmt of                                   (* ROUND.W.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPRSqrtfmt of                                      (* RSQRT.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPSqrtfmt of                                        (* SQRT.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPSubfmt of                                          (* SUB.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source 1 *)
      * mips_operand_int (* ft: source 2 *)
  | FPTruncLfmt of                                   (* TRUNC.L.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | FPTruncWfmt of                                   (* TRUNC.W.fmt; FPR-type *)
      mips_fp_format_t
      * mips_operand_int (* fd: destination *)
      * mips_operand_int (* fs: source *)
  | Jump of                                                      (* J; J-type *)
      mips_operand_int   (* tgt: target address *)
  | JumpLink of                                                (* JAL; J-type *)
      mips_operand_int   (* tgt: target address *)
  | JumpLinkRegister of                                       (* JALR; R-type *)
      mips_operand_int   (* rd: return address *)
      * mips_operand_int (* rs: target address *)
  | JumpRegister of                                             (* JR; R-type *)
      mips_operand_int   (* rs: target address *)
  | LoadByte of                                         (* LB; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadByteUnsigned of                                (* LBU; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadDoublewordToFP of                             (* LDC1; I-type: memory *)
      mips_operand_int   (* ft: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadHalfWord of                                     (* LH; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadHalfWordUnsigned of                            (* LHU; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadImmediate of                               (* LI;  pseudo instruction *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* imm: immediate *)
  | LoadLinkedWord of                                   (* LL; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadUpperImmediate of                              (* LUI; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* imm: immediate *)
  | LoadWord of                                         (* LW; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadWordFP of                                     (* LWC1; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadWordLeft of                                    (* LWL; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | LoadWordRight of                                   (* LWR; I-type: memory *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* addr: base-offset address *)
  | MoveConditionalNotZero of                                 (* MOVN; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source *)
      * mips_operand_int (* rt: value to be tested for not zero *)
  | MoveConditionalZero of                                    (* MOVZ; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source *)
      * mips_operand_int (* rt: value to be tested for zero *)
  | MovF of  (* FPCM type *)
      int                (* cc: fp condition code *)
      * mips_operand_int (* rd: destination *)
      * mips_operand_int (* rs: source *)
  | MovT of  (* FPCM type *)
      int                (* cc: fp condition code *)
      * mips_operand_int (* rd: destination *)
      * mips_operand_int (* rs: source *)
  | Move of                                             (* pseudo instruction *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source *)
  | MoveFromHi of                                             (* MFHI; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* hi: source (special register HI) *)
  | MoveToHi of                                               (* MTHI; R-type *)
      mips_operand_int   (* hi: destination (special register HI) *)
      * mips_operand_int (* rs: source *)
  | MoveFromLo of                                             (* MFLO; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* lo: source (special register LO) *)
  | MoveToLo of                                               (* MTLO; R-type *)
      mips_operand_int   (* lo: destination (special register LO) *)
      * mips_operand_int (* rs: source *)
  | MoveWordFromFP of                                      (* MFC1; FPRI type *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* fs: floating point register *)
  | MoveWordFromHighHalfFP of                             (* MFHC1; FPRI type *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* fs: floating point register *)
  | MoveWordToHighHalfFP of                               (* MTHC1; FPRI type *)
      mips_operand_int   (* rt: source *)
      * mips_operand_int (* fs: destination *)
  | MoveWordToFP of                                        (* MTC1; FPRI type *)
      mips_operand_int   (* rt: source *)
      * mips_operand_int (* fs: destination *)
  | MoveFromCoprocessor0 of                                (* MFC0; FPRI type *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rd: source selector *)
      * int              (* sel: selector *)
  | MoveToCoprocessor0 of                                  (* MTC0; FPRI type *)
      mips_operand_int   (* rt: source *)
      * mips_operand_int (* rd: destination selector *)
      * int              (* sel: selector *)
  | MoveFromHighCoprocessor0 of                           (* MFHC0; FPRI type *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rd: source selector *)
      * int              (* sel: selector *)
  | MoveToHighCoprocessor0 of                             (* MTHC0; FPRI type *)
      mips_operand_int   (* rt: source *)
      * mips_operand_int (* rd: destination selector *)
      * int              (* sel: selector *)
  | MoveWordFromCoprocessor2 of                (* MFC2; I-type floating point *)
      mips_operand_int   (* rt: destination *)
      * int              (* rd: source selector *)
      * int              (* sel: selector *)
  | MoveWordFromHighHalfCoprocessor2 of       (* MFHC2; I-type floating point *)
      mips_operand_int   (* rt: destination *)
      * int              (* rd: source selector *)
      * int              (* sel: selector *)
  | MoveWordToCoprocessor2 of                  (* MTC2; I-type floating point *)
      mips_operand_int   (* rt: source *)
      * int              (* rd: destination selector *)
      * int              (* sel: selector *)
  | MultiplyAddWord of                                       (* MADD; R2-type *)
      mips_operand_int   (* hi: high word destination *)
      * mips_operand_int (* lo: low word destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | MultiplyAddUnsignedWord of                               (* MADDU; R-type *)
      mips_operand_int   (* hi: high word destination *)
      * mips_operand_int (* lo: low word destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | MultiplyUnsignedWord of                                  (* MULTU; R-type *)
      mips_operand_int   (* hi: high word destination *)
      * mips_operand_int (* lo: low word destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | MultiplyWord of                                           (* MULT; R-type *)
      mips_operand_int   (* hi: high word destination *)
      * mips_operand_int (* lo: low word destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | MultiplyWordToGPR of                                      (* MUL; R2-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | Nor of                                                     (* NOR; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | Or of                                                       (* OR; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rd: source 2 *)
  | OrImmediate of                           (* ORI; I-type: arithmetic/logic *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* imm: immediate *)
  | Prefetch of                                       (* PREF; I-type: memory *)
      mips_operand_int   (* offset(base) *)
      * int              (* hint *)
  | ReadHardwareRegister of                                 (* RDHWR; R3-type *)
      mips_operand_int   (* rt: destination *)
      * int              (* rd: hardware selection *)
  | SetLT of                                                   (* SLT; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2*)
  | SetLTImmediate of                       (* SLTI; I-type: arithmetic/logic *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* imm: immediate *)
  | SetLTImmediateUnsigned of              (* SLTIU; I-type: arithmetic/logic *)
      mips_operand_int   (* rt: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* imm: immediate *)
  | SetLTUnsigned of                                          (* SLTU; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2*)
  | ShiftLeftLogical of                                        (* SLL; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rt: source 1 *)
      * mips_operand_int (* sa: source 2*)
  | ShiftLeftLogicalVariable of                               (* SLLV; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2*)
  | ShiftRightArithmetic of                                    (* SRA; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2*)
  | ShiftRightArithmeticVariable of                           (* SRAV; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2*)
  | ShiftRightLogical of                                       (* SRL; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2*)
  | ShiftRightLogicalVariable of                              (* SRLV; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2*)
  | SignExtendByte of                                         (* SEB; R3-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rt: source *)
  | SignExtendHalfword of                                     (* SEH; R3-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rt: source *)
  | StoreByte of                                        (* SB; I-type: memory *)
      mips_operand_int   (* addr: base offset address *)
      * mips_operand_int (* rt: source register *)
  | StoreConditionalWord of                             (* SC; I-type: memory *)
      mips_operand_int   (* addr: base offset address *)
      * mips_operand_int (* rt: source register *)
  | StoreDoublewordFromFP of                          (* SDC1; I-type: memory *)
      mips_operand_int   (* addr: base offset address *)
      * mips_operand_int (* ft: source register *)
  | StoreHalfWord of                                    (* SH; I-type: memory *)
      mips_operand_int   (* addr: base offset address *)
      * mips_operand_int (* rt: source register *)
  | StoreWord of                                        (* SW; I-type: memory *)
      mips_operand_int   (* addr: base offset address *)
      * mips_operand_int (* rt: source register *)
  | StoreWordFromFP of                                (* SWC1; I-type: memory *)
      mips_operand_int   (* addr: base offset address *)
      * mips_operand_int (* ft: source register *)
  | StoreWordLeft of                                   (* SWL; I-type: memory *)
      mips_operand_int   (* addr: base offset address *)
      * mips_operand_int (* rt: source register *)
  | StoreWordRight of                                  (* SWR; I-type: memory *)
      mips_operand_int   (* addr: base offset address *)
      * mips_operand_int (* rt: source register *)
  | Subtract of                                                (* SUB; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | SubtractUnsigned of                                       (* SUBU; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | Sync of                                               (* SYNC; RSync type *)
      int                (* stype *)
  | Syscall of                                       (* SYSCALL; Syscall type *)
      int (* code: software parameters *)
  | TrapIfEqual of                                             (* TEQ: R-type *)
      int                (* code: ignored by hardware *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | TrapIfEqualImmediate of                           (* TEQI; I-type: memory *)
      mips_operand_int   (* rs: source *)
      * mips_operand_int (* imm: constant to compare against *)
  | Xor of                                                     (* XOR; R-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* rt: source 2 *)
  | XorImmediate of                         (* XORI; I-type: arithmetic/logic *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rs: source 1 *)
      * mips_operand_int (* imm: immediate *)
  | WordSwapBytesHalfwords of                                (* WSBH; R3-type *)
      mips_operand_int   (* rd: destination *)
      * mips_operand_int (* rt: source *)

  (* Pseudo instructions *)
  | NoOperation
  | Halt

  (* Misc *)
  | NotCode of not_code_t option
  | NotRecognized of string * doubleword_int
  | OpcodeUnpredictable of string
  | OpInvalid


(* =================================================== MIPS opcode dictionary === *)

class type mips_dictionary_int =
  object

    method index_mips_opkind: mips_operand_kind_t -> int
    method index_mips_operand: mips_operand_int -> int
    method index_mips_opcode: mips_opcode_t -> int
    method index_mips_bytestring: string -> int
    method index_mips_instr_format: mips_instr_format_t -> int

    method write_xml_mips_bytestring: ?tag:string -> xml_element_int -> string -> unit
    method write_xml_mips_opcode: ?tag:string -> xml_element_int -> mips_opcode_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

(* ===================================================== Assembly instruction === *)

class type mips_assembly_instruction_int =
object
  (* setters *)
  method set_block_entry: unit
  method set_delay_slot: unit
  method set_inlined_call: unit

  (* accessors *)
  method get_address: doubleword_int
  method get_opcode : mips_opcode_t
  method get_instruction_bytes: string
  method get_bytes_ashexstring: string

  (* predicates *)
  method is_block_entry : bool
  method is_delay_slot  : bool
  method is_inlined_call: bool

  (* i/o *)
  method write_xml: xml_element_int -> unit
  method toString: string
  method toPretty: pretty_t

end


type mips_assembly_instruction_result = mips_assembly_instruction_int traceresult

(* ==================================================== Assembly instructions === *)

class type mips_assembly_instructions_int =
object

  (* setters *)

  method set_instruction:
           doubleword_int -> mips_assembly_instruction_int -> unit

  (* method set: int -> mips_assembly_instruction_int -> unit *)

  (** [set_not_code lst] marks the addresses contained within the data blocks
      in [lst] as [NotCode]. Data blocks whose start or end address lie outside
      the declared code space are ingnored. *)
  method set_not_code: data_block_int list -> unit

  (* accessors *)

  (** Return the length of code space (in words).*)
  method length: int

  (** [get_instruction va] returns the instruction located at virtual address
      [va]. If no instruction has been entered yet, a new instruction, with
      opcode [NoOperation] is assigned and returned. If [va] is out-of-range
      an Error result is returned.*)
  method get_instruction: doubleword_int -> mips_assembly_instruction_result

  (** [get_code_addresses_rev low high] returns the list of virtual addresses
      bounded by [low] and [high] that hold valid instructions, in reverse
      order. [low] defaults to [codeBase], [high] defaults to [oxffffffff].*)
  method get_code_addresses_rev:
           ?low:doubleword_int
           -> ?high:doubleword_int
           -> unit
           -> doubleword_int list

  (** Return the number of valid instructions in the code space.*)
  method get_num_instructions: int

  (** Return the number of valid instructions in the code space with unknown
      opcode.*)
  method get_num_unknown_instructions: int

  (* predicates *)

  (** [is_code_address va] returns true if [va] is a virtual address within
      the code space and if the address holds a valid assembly instruction.*)
  method is_code_address: doubleword_int -> bool

  (* iterators *)
  method iteri: (int -> mips_assembly_instruction_int -> unit) -> unit
  method itera:
           (doubleword_int -> mips_assembly_instruction_int -> unit)
           -> unit (* provide virtual address *)

  (* i/o *)
  method write_xml: xml_element_int -> unit
  method toString:
           ?filter:(mips_assembly_instruction_int -> bool) -> unit -> string
  method toPretty: pretty_t

end

(* ======================================================= Assembly block === *)

class type mips_assembly_block_int =
  object

    (* accessors *)

    (** Return the address of the function to which this block belongs. If this
        block is part of an inlined function, the address of the original
        function is returned (the inner function), not the address of the
        function in which the block is inlined.*)
    method get_faddr: doubleword_int

    (** Return the address of the first instruction in this block.*)
    method get_first_address: doubleword_int

    (** Return the location of this block (with full context, if inlined).*)
    method get_location: location_int

    (** Return the context of this block (empty if not inlined).*)
    method get_context: context_t list

    (** Return the context of this block as a string (the first address, if
        not inlined).*)
    method get_context_string: ctxt_iaddress_t

    (** Return the address of the last instruction in this block.*)
    method get_last_address: doubleword_int

    (** Return the list of instructions contained in this basic block.*)
    method get_instructions: mips_assembly_instruction_int list

    (** Return the list of instructions contained in this basic block, in
        reverse order. *)
    method get_instructions_rev: mips_assembly_instruction_int list

    (** Return the successor of this block, inlcuding blocks of the inlining
        function if this block is part of an inlined function.*)
    method get_successors: ctxt_iaddress_t list

    (** [get_instruction va] returns the instruction at virtual address [va].

        Raises an exception if [va] is not within this block, or if [va] does
        not have a valid instruction.*)
    method get_instruction: doubleword_int -> mips_assembly_instruction_int

    (** Return the bytes that make up the instructions of this block as a string
        of hexadecimal characters.*)
    method get_bytes_as_hexstring: string

    (** Return number of instructions in this basic block.*)
    method get_instruction_count: int

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool
    method is_returning: bool

    (* iterators *)
    method itera:
             ?low:doubleword_int -> ?high:doubleword_int -> ?reverse:bool
             -> (ctxt_iaddress_t -> mips_assembly_instruction_int -> unit) -> unit

    (* printing *)
    method toString: string
    method toPretty: pretty_t
  end

(* ==================================================== Assembly function === *)

class type mips_assembly_function_int =
  object

    (* accessors *)
    method get_address: doubleword_int
    method get_blocks: mips_assembly_block_int list
    method get_block: ctxt_iaddress_t -> mips_assembly_block_int
    method get_instruction: doubleword_int -> mips_assembly_instruction_int
    method get_bytes_as_hexstring: string
    method get_function_md5: string
    method get_instruction_count: int
    method get_block_count: int

    (* iterators *)
    method iter: (mips_assembly_block_int -> unit) -> unit
    method itera: (ctxt_iaddress_t -> mips_assembly_block_int -> unit) -> unit
    method iteri:
             (doubleword_int -> ctxt_iaddress_t -> mips_assembly_instruction_int -> unit)
             -> unit

    method populate_callgraph: callgraph_int -> unit

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool

    (* printing *)
    method toPretty: pretty_t
  end

(* =================================================== Assembly functions === *)

class type mips_assembly_functions_int =
  object

    (* reset *)
    method reset: unit

    (* setters *)
    method add_function: mips_assembly_function_int -> unit
    method add_functions_by_preamble: doubleword_int list
    method inline_blocks: unit

    (* accessors *)
    method get_callgraph: callgraph_int
    method get_functions: mips_assembly_function_int list
    method get_function: dw_index_t -> mips_assembly_function_int
    method get_function_by_address: doubleword_int -> mips_assembly_function_int
    method get_function_coverage: int * int * int (* coverage, overlap, multiplicity *)
    method get_num_functions: int

    (* iterators *)
    method iter: (mips_assembly_function_int -> unit) -> unit
    method itera: (doubleword_int -> mips_assembly_function_int -> unit) -> unit
    method bottom_up_itera: (doubleword_int -> mips_assembly_function_int -> unit) -> unit
    method top_down_itera: (doubleword_int -> mips_assembly_function_int -> unit) -> unit

    (* predicates *)
    method has_function_by_address: doubleword_int -> bool
    method includes_instruction_address: doubleword_int -> bool

    (* printing *)
    method dark_matter_to_string: string

  end

(* ====================================================== Disassembly pattern === *)

type disassembly_pattern_t = {
    regex_ds: Str.regexp;
    regex_df: doubleword_int -> string -> string -> doubleword_int
  }

(* ================================================================== Code pc === *)

class type mips_code_pc_int =
object
  (* accessors *)
  method get_next_instruction      : ctxt_iaddress_t * mips_assembly_instruction_int
  method get_block_successors      : ctxt_iaddress_t list
  method get_block_successor       : ctxt_iaddress_t
  method get_false_branch_successor: ctxt_iaddress_t
  method get_true_branch_successor : ctxt_iaddress_t
  method get_conditional_successor_info:
           (location_int * location_int * ctxt_iaddress_t * ctxt_iaddress_t * xpr_t)

  (* predicates *)
  method has_more_instructions: bool
  method has_conditional_successor: bool
end


(* =========================================================== CHIF System === *)

class type mips_chif_system_int =
  object

    (* reset *)
    method reset: unit

    (* setters *)
    method add_mips_procedure: procedure_int -> unit

    (* accessors *)
    method get_mips_system: system_int
    method get_mips_procedure_names: symbol_t list
    method get_mips_procedure: doubleword_int -> procedure_int

    (* predicates *)
    method has_mips_procedure: doubleword_int -> bool
  end

(* ========================================== MIPS instruction dictionary === *)

class type mips_opcode_dictionary_int =
  object

    method index_sp_offset: int * interval_t -> int
    method index_instr:
             mips_assembly_instruction_int
             -> floc_int
             -> block_restriction_t option
             -> int

    method get_sp_offset: int -> (int * interval_t)

    method write_xml_sp_offset: ?tag:string -> xml_element_int -> int * interval_t -> unit
    method write_xml_instr:
             ?tag:string
             -> xml_element_int
             -> mips_assembly_instruction_int
             -> floc_int
             -> block_restriction_t option
             -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t
  end

class type mips_analysis_results_int =
  object

    method record_results: ?save:bool -> mips_assembly_function_int -> unit
    method write_xml: xml_element_int -> unit
    method save: unit

  end

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
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHFunctionData
open BCHLibTypes
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMOperand
open BCHARMTypes


(* Reference: Table A8-1, pg A8-286 *)
let get_cond_mnemonic_extension (c:arm_opcode_cc_t) =
  match c with
  | ACCEqual -> "EQ"
  | ACCNotEqual -> "NE"
  | ACCCarrySet -> "CS"
  | ACCCarryClear -> "CC"
  | ACCNegative -> "MI"
  | ACCNonNegative -> "PL"
  | ACCOverflow -> "VS"
  | ACCNoOverflow -> "VC"
  | ACCUnsignedHigher -> "HI"
  | ACCNotUnsignedHigher -> "LS"
  | ACCSignedGE -> "GE"
  | ACCSignedLT -> "LT"
  | ACCSignedGT -> "GT"
  | ACCSignedLE -> "LE"
  | ACCAlways -> ""
  | ACCUnconditional -> ""


let get_cond_flags_used (c: arm_opcode_cc_t): arm_cc_flag_t list =
  match c with
  | ACCEqual -> [APSR_Z]
  | ACCNotEqual -> [APSR_Z]
  | ACCCarrySet -> [APSR_C]
  | ACCCarryClear -> [APSR_C]
  | ACCNegative -> [APSR_N]
  | ACCNonNegative -> [APSR_N]
  | ACCOverflow -> [APSR_V]
  | ACCNoOverflow -> [APSR_V]
  | ACCUnsignedHigher -> [APSR_C; APSR_Z]
  | ACCNotUnsignedHigher -> [APSR_C; APSR_Z]
  | ACCSignedGE -> [APSR_N; APSR_V]
  | ACCSignedLT -> [APSR_N; APSR_V]
  | ACCSignedGT -> [APSR_Z; APSR_N; APSR_V]
  | ACCSignedLE -> [APSR_Z; APSR_N; APSR_V]
  | ACCAlways -> []
  | ACCUnconditional -> []

let is_cond_conditional (c: arm_opcode_cc_t): bool =
  match c with
  | ACCAlways
    | ACCUnconditional -> false
  | _ -> true


class type ['a] opcode_formatter_int =
  object
    method ops:
             ?preops: string
             -> ?postops: string
             -> string
             -> arm_operand_int list -> 'a
    method opscc:
             ?thumbw: bool
             -> ?dt: vfp_datatype_t
             -> ?dt2: vfp_datatype_t
             -> ?writeback: bool
             -> ?preops: string
             -> ?postops: string
             -> string
             -> arm_opcode_cc_t
             -> arm_operand_int list
             -> 'a
    method no_ops: string -> 'a
  end

type 'a opcode_record_t = {
    mnemonic: string;
    operands: arm_operand_int list;
    ccode: arm_opcode_cc_t option;
    flags_set: arm_cc_flag_t list;
    ida_asm: 'a opcode_formatter_int -> 'a
  }

let get_record (opc:arm_opcode_t): 'a opcode_record_t =
  match opc with
  | Add (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ADD";
      operands = [rd;rn;rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C; APSR_V] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "ADD" c [rd; rn; rm])
    }
  | AddCarry (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ADC";
      operands = [rd;rn;rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C; APSR_V] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "ADC" c [rd; rn; rm])
    }
  | Adr (cc, rd, addr) -> {
      mnemonic = "ADR";
      operands = [ rd; addr ];
      flags_set = [];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "ADR" cc [rd; addr ])
    }
  | AESInverseMixColumns (c, dt, vd, vm) -> {
      mnemonic = "AESIMC";
      operands = [vd; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "AESIMC" c [vd; vm])
    }
  | AESMixColumns (c, dt, vd, vm) -> {
      mnemonic = "AESMC";
      operands = [vd; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "AESMC" c [vd; vm])
    }
  | AESSingleRoundDecryption (c, dt, vd, vm) -> {
      mnemonic = "AESD";
      operands = [vd; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "AESD" c [vd; vm])
    }
  | AESSingleRoundEncryption (c, dt, vd, vm) -> {
      mnemonic = "AESE";
      operands = [vd; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "AESE" c [vd; vm])
    }
  | ArithmeticShiftRight (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ASR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "ASR" ~writeback:s c [rd; rn; rm])
    }
  | BitFieldClear (c, rd, lsb, width, msb) ->
     let postops = ", " ^ (string_of_int lsb) ^ ", " ^ (string_of_int width) in
     { mnemonic = "BFC";
       operands = [rd];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~postops "BFC" c [rd])
     }
  | BitFieldInsert (c, rd, rn, lsb, width, msb) ->
     let postops = ", #" ^ (string_of_int lsb) ^ ", #" ^ (string_of_int width) in
     { mnemonic = "BFI";
       operands = [rd; rn];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~postops "BFI" c [rd; rn])
     }
  | BitwiseAnd (s, c, rd,rn, imm, tw) -> {
      mnemonic = "AND";
      operands = [ rd; rn; imm ];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "AND" c [rd; rn; imm])
    }
  | BitwiseBitClear (s, c, rd, rn, rm, tw) -> {
      mnemonic = "BIC";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "BIC" c [rd;rn;rm])
    }
  | BitwiseExclusiveOr (s, c, rd, rn, rm, tw) -> {
      mnemonic = "EOR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "EOR" c [rd;rn;rm])
    }
  | BitwiseNot (s, c, rd, rm, tw) -> {
      mnemonic = "MVN";
      operands = [rd; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "MVN" c [rd;rm])
    }
  | BitwiseOr (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ORR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "ORR" c [rd; rn; rm])
    }
  | BitwiseOrNot (s, c, rd, rn, rm) -> {
      mnemonic = "ORN";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "ORN" ~writeback:s c [rd; rn; rm])
    }
  | Branch (cc, addr, tw) -> {
      mnemonic = "B";
      operands = [addr];
      flags_set = [];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "B" cc [ addr ])
    }
  | BranchExchange (c,addr) -> {
      mnemonic = "BX";
      operands = [ addr ];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "BX" c [addr])
    }
  | BranchLink (cc, addr) -> {
      mnemonic = "BL";
      operands = [addr];
      flags_set = [];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "BL" cc [addr])
    }
  | BranchLinkExchange (c, addr) -> {
      mnemonic = "BLX";
      operands = [addr];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "BLX" c [ addr ])
    }
  | ByteReverseWord (c, rd, rm, tw) -> {
      mnemonic = "REV";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "REV" c [rd; rm])
    }
  | ByteReversePackedHalfword (c, rd, rm, tw) -> {
      mnemonic = "REV16";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "REV16" c [rd; rm])
    }
  | Compare (c, rn, rm, tw) -> {
      mnemonic = "CMP";
      operands = [rn; rm];
      flags_set = [APSR_N; APSR_Z; APSR_C; APSR_V];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "CMP" c [rn; rm])
    }
  | CompareBranchNonzero (op1, op2) -> {
      mnemonic = "CBNZ";
      operands = [op1; op2];
      flags_set = [];
      ccode = None;
      ida_asm = (fun f -> f#ops "CBNZ" [op1; op2])
    }
  | CompareBranchZero (op1, op2) -> {
      mnemonic = "CBZ";
      operands = [op1; op2];
      flags_set = [];
      ccode = None;
      ida_asm = (fun f -> f#ops "CBZ" [op1; op2])
    }
  | CompareNegative (cc, op1, op2) -> {
      mnemonic = "CMN";
      operands = [op1; op2];
      flags_set = [APSR_N; APSR_Z; APSR_C; APSR_V];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "CMN" cc [op1; op2])
    }
  | CountLeadingZeros (c, rd, rm) -> {
      mnemonic = "CLZ";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "CLZ" c [rd;rm])
    }
  | DataMemoryBarrier (c, option) -> {
      mnemonic = "DMB";
      operands = [option];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "DMB" c [option])
    }
  | IfThen (c, xyz) ->
     let mnemonic = "IT" ^ xyz ^ " " ^ (get_cond_mnemonic_extension c) in
     { mnemonic = mnemonic;
       operands = [];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#ops mnemonic [])
     }
  | FLoadMultipleIncrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "FLDMIAX";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "FLDMIAX" c [rn; rl])
    }
  | FStoreMultipleIncrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "FSTMIAX";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "FSTMIAX" c [rn; rl])
    }
  | LoadCoprocessor (islong, ista2, c, coproc, crd, src, option) ->
     let mnemonic =
       match (islong, ista2) with
       | (false, false) -> "LDC"
       | (false, true) -> "LDC2"
       | (true, false) -> "LDCL"
       | (true, true) -> "LDC2L" in
     let preops =
       "p" ^ (string_of_int coproc) ^ ", " ^ "c" ^ (string_of_int crd) ^ "," in
     {
       mnemonic = mnemonic;
       operands = [src];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~preops mnemonic c [src]);
     }
  | LoadMultipleDecrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "LDMDA";
      operands = [rn; rl; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDMDA" c [ rn; rl ])
    }
  | LoadMultipleDecrementBefore (wb, c, rn, rl, mem) -> {
      mnemonic = "LDMDB";
      operands = [rn; rl; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDMDB" c [rn; rl])
    }
  | LoadMultipleIncrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "LDM";
      operands = [rn; rl; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDM" c [ rn; rl ])
    }
  | LoadMultipleIncrementBefore (wb, c, rn, rl, mem) -> {
      mnemonic = "LDMIB";
      operands = [rn; rl; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDMIB" c [rn; rl])
    }
  | LoadRegister (c, rt, rn, rm, mem, tw) -> {
      mnemonic = "LDR";
      operands = [rt; rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDR" c [rt; mem])
    }
  | LoadRegisterByte (c, rt, rn, rm, mem, tw) -> {
      mnemonic = "LDRB";
      operands = [rt; rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDRB" c [rt; mem])
    }
  | LoadRegisterDual (c, rt, rt2, rn, rm, mem, mem2) -> {
      mnemonic = "LDRD";
      operands = [rt; rt2; rn; rm; mem; mem2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDRD" c [rt; rt2; mem])
    }
  | LoadRegisterExclusive (c, rt, rn, rm, mem) -> {
      mnemonic = "LDREX";
      operands = [rt; rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDREX" c [rt; mem])
    }
  | LoadRegisterHalfword (c, rt, rn, rm, mem, tw) -> {
      mnemonic = "LDRH";
      operands = [rt; rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDRH" c [rt; mem])
    }
  | LoadRegisterSignedByte (c, rt, rn, rm, mem, tw) -> {
      mnemonic = "LDRSB";
      operands = [rt; rn; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDRSB" c [rt; mem])
    }
  | LoadRegisterSignedHalfword (c, rt, rn, rm, mem, tw) -> {
      mnemonic = "LDRSH";
      operands = [rt; rn; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDRSH" c [rt; mem])
    }
  | LogicalShiftLeft (s, c, rd, rn, rm, tw) -> {
      mnemonic = "LSL";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "LSL" c [rd; rn; rm])
    }
  | LogicalShiftRight (s, c, rd, rn, rm, tw) -> {
      mnemonic = "LSR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "LSR" c [rd; rn; rm])
    }
  | Move (s, c, rd, rm, tw, aw) ->
     let mnem = if aw then "MOVW" else "MOV" in
     {
       mnemonic = mnem;
       operands = [rd; rm];
       flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s mnem c [rd;rm])
    }
  | MoveFromSpecialRegister (c, rd, src, _) -> {
      mnemonic = "MRS";
      operands = [rd; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MRS" c [rd; src])
    }
  | MoveRegisterCoprocessor (c, coproc, opc1, rt, crn, crm, opc2) ->
     let preops =
       "p" ^ (string_of_int coproc) ^ ", " ^ (string_of_int opc1) ^ "," in
     let postops =
       ", c"
       ^ (string_of_int crn)
       ^ ", c"
       ^ (string_of_int crm)
       ^ ", "
       ^ (string_of_int opc2) in
     {
      mnemonic = "MRC";
      operands = [rt];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~preops ~postops "MRC" c [rt]);
     }
  | MoveToCoprocessor (c, coproc, opc1, rt, crn, crm, opc2) ->
     let preops =
       "p" ^ (string_of_int coproc) ^ ", " ^ (string_of_int opc1) ^ "," in
     let postops =
       ", c"
       ^ (string_of_int crn)
       ^ ", c"
       ^ (string_of_int crm)
       ^ ", "
       ^ (string_of_int opc2) in
     {
       mnemonic = "MCR";
       operands = [rt];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~preops ~postops "MCR" c [rt]);
     }
  | MoveTop (c, rd, imm) -> {
      mnemonic = "MOVT";
      operands = [rd; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MOVT" c [rd; imm])
    }
  | MoveToSpecialRegister (c, spr, imm, _) -> {
      mnemonic = "MSR";
      operands = [spr; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MSR" c [spr; imm])
    }
  | MoveTwoRegisterCoprocessor (c, coproc, opc, rt, rt2, crm) ->
     let preops =
       "p" ^ (string_of_int coproc) ^ ", " ^ (string_of_int opc) ^ "," in
     let postops = ", c" ^ (string_of_int crm) in
     {
       mnemonic = "MRRC";
       operands = [rt; rt2];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~preops ~postops "MRRC" c [rt; rt2])
     }
  | Multiply (s, c, rd, rn, rm) -> {
      mnemonic = "MUL";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MUL" c [rd; rn; rm])
    }
  | MultiplyAccumulate (s, c, rd, rn, rm, ra) -> {
      mnemonic = "MLA";
      operands = [rd; rn; rm; ra];
      flags_set = if s then [APSR_N; APSR_Z] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MLA" c [rd; rn; rm; ra])
    }
  | MultiplySubtract (c, rd, rn, rm, ra) -> {
      mnemonic = "MLS";
      operands = [rd; rn; rm; ra];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MLS" c [rd; rn; rm; ra])
    }
  | Pop (c, sp, rl, tw) -> {
      mnemonic = "POP";
      operands = [sp; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "POP" c [rl])
    }
  | PreloadData (w, c, base, mem) ->
     let mnemonic = if w then "PLDW" else "PLD" in
     {
       mnemonic = mnemonic;
       operands = [base; mem];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc mnemonic c [mem])
     }
  | Push (c, sp, rl, tw) -> {
      mnemonic = "PUSH";
      operands = [sp; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "PUSH" c [rl])
    }
  | ReverseBits (c, rd, rm) -> {
      mnemonic = "RBIT";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "RBIT" c [rd; rm])
    }
  | ReverseSubtract (s, c, rd, rn, rm, tw) -> {
      mnemonic = "RSB";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C; APSR_V] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "RSB" c [rd; rn; rm])
    }
  | ReverseSubtractCarry (s, c, rd, rn, rm) -> {
      mnemonic = "RSC";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C; APSR_V] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~writeback:s "RSC" c [rd; rn; rm])
    }
  | RotateRight (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ROR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "ROR" c [rd; rn; rm])
    }
  | RotateRightExtend (s, c, rd, rm) -> {
      mnemonic = "RRX";
      operands = [rd; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "RRX" c [rd; rm])
    }
  | SaturatingAdd (c, rd, rm, rn) -> {
      mnemonic = "QADD";
      operands = [rd; rm; rn];
      flags_set = [APSR_Q];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "QADD" c [rd; rm; rn])
    }
  | SaturatingDoubleAdd (c, rd, rm, rn) -> {
      mnemonic = "QDADD";
      operands = [rd; rm; rn];
      flags_set = [APSR_Q];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "QDADD" c [rd; rm; rn])
    }
  | SaturatingDoubleSubtract(c, rd, rm, rn) -> {
      mnemonic = "QDSUB";
      operands = [rd; rm; rn];
      flags_set = [APSR_Q];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "QDSUB" c [rd; rm; rn])
    }
  | SaturatingSubtract (c, rd, rm, rn) -> {
      mnemonic = "QSUB";
      operands = [rd; rm; rn];
      flags_set = [APSR_Q];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "QSUB" c [rd; rm; rn])
    }
  | SelectBytes (c, rd, rn, rm) -> {
      mnemonic = "SEL";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SEL" c [rd; rn; rm])
    }
  | SHA1FixedRotate (c, dt, vd, vm) -> {
      mnemonic = "SHA1H";
      operands = [vd; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA1H" c [vd; vm])
    }
  | SHA1HashUpdateChoose (c, dt, vd, vn, vm) -> {
      mnemonic = "SHA1C";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA1C" c [vd; vn; vm])
    }
  | SHA1HashUpdateMajority (c, dt, vd, vn, vm) -> {
      mnemonic = "SHA1M";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA1M" c [vd; vn; vm])
    }
  | SHA1HashUpdateParity (c, dt, vd, vn, vm) -> {
      mnemonic = "SHA1P";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA1P" c [vd; vn; vm])
    }
  | SHA1ScheduleUpdate0 (c, dt, vd, vn, vm) -> {
      mnemonic = "SHA1SU0";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA1SU0" c [vd; vn; vm])
    }
  | SHA1ScheduleUpdate1 (c, dt, vd, vm) -> {
      mnemonic = "SHA1SU1";
      operands = [vd; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA1SU1" c [vd; vm])
    }
  | SHA256HashUpdatePart1 (c, dt, vd, vn, vm) -> {
      mnemonic = "SHA256H";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA256H" c [vd; vn; vm])
    }
  | SHA256HashUpdatePart2 (c, dt, vd, vn, vm) -> {
      mnemonic = "SHA256H2";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA256H2" c [vd; vn; vm])
    }
  | SHA256ScheduleUpdate0 (c, dt, vd, vm) -> {
      mnemonic = "SHA256SU0";
      operands = [vd; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA256SU0" c [vd; vm])
    }
  | SHA256ScheduleUpdate1 (c, dt, vd, vn, vm) -> {
      mnemonic = "SHA256SU1";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "SHA256SU1" c [vd; vn; vm])
    }
  | SignedDivide (c, rd, rn, rm) -> {
      mnemonic = "SDIV";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SDIV" c [rd; rn; rm])
    }
  | SignedBitFieldExtract (c, rd, rn) -> {
      mnemonic = "SBFX";
      operands = [rd; rn];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SBFX" c [rd; rn])
    }
  | SignedExtendByte (c, rd, rm, tw) -> {
      mnemonic = "SXTB";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "SXTB" c [rd; rm])
    }
  | SignedExtendHalfword (c, rd, rm, tw) -> {
      mnemonic = "SXTH";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "SXTH" c [rd; rm])
    }
  | SignedMostSignificantWordMultiply (c, rd, rm, rn, rf) ->
     let mnemonic = "SMMUL" ^ (if rf = 1 then "R" else "") in
     { mnemonic = mnemonic;
       operands = [rd; rm; rn];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc mnemonic c [rd; rm; rn])
     }
  | SignedMostSignificantWordMultiplyAccumulate (c, rd, rm, rn, ra, rf) ->
     let mnemonic = "SMMLA" ^ (if rf = 1 then "R" else "") in
     { mnemonic = mnemonic;
       operands = [rd; rm; rn; ra];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc mnemonic c [rd; rm; rn; ra])
     }
  | SignedMultiplyAccumulateBB (c, rd, rn, rm, ra) -> {
      mnemonic = "SMLABB";
      operands = [rd; rn; rm; ra];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLABB" c [rd; rn; rm; ra])
    }
  | SignedMultiplyAccumulateBT (c, rd, rn, rm, ra) -> {
      mnemonic = "SMLABT";
      operands = [rd; rn; rm; ra];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLABT" c [rd; rn; rm; ra])
    }
  | SignedMultiplyAccumulateTB (c, rd, rn, rm, ra) -> {
      mnemonic = "SMLATB";
      operands = [rd; rn; rm; ra];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLATB" c [rd; rn; rm; ra])
    }
  | SignedMultiplyAccumulateTT (c, rd, rn, rm, ra) -> {
      mnemonic = "SMLATT";
      operands = [rd; rn; rm; ra];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLATT" c [rd; rn; rm; ra])
    }
  | SignedMultiplyAccumulateLong (s, c, rdlo, rdhi, rn, rm) -> {
      mnemonic = "SMLAL";
      operands = [rdlo; rdhi; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLAL" ~writeback:s c [rdlo; rdhi; rn; rm])
    }
  | SignedMultiplyAccumulateWordB (c, rd, rn, rm, ra) -> {
      mnemonic = "SMLAWB";
      operands = [rd; rn; rm; ra];
      flags_set = [APSR_Q];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLAWB" c [rd; rn; rm; ra])
    }
  | SignedMultiplyAccumulateWordT (c, rd, rn, rm, ra) -> {
      mnemonic = "SMLAWT";
      operands = [rd; rn; rm; ra];
      flags_set = [APSR_Q];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLAWT" c [rd; rn; rm; ra])
    }
  | SignedMultiplyHalfwordsBB (c, rd, rn, rm) -> {
      mnemonic = "SMULBB";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULBB" c [rd; rn; rm])
    }
  | SignedMultiplyHalfwordsBT (c, rd, rn, rm) -> {
      mnemonic = "SMULBT";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULBT" c [rd; rn; rm])
    }
  | SignedMultiplyHalfwordsTB (c, rd, rn, rm) -> {
      mnemonic = "SMULTB";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULTB" c [rd; rn; rm])
    }
  | SignedMultiplyHalfwordsTT (c, rd, rn, rm) -> {
      mnemonic = "SMULTT";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULTT" c [rd; rn; rm])
    }
  | SignedMultiplyLong (s, c, rdlo, rdhi, rn, rm) -> {
      mnemonic = "SMULL";
      operands = [rdlo; rdhi; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULL" c [rdlo; rdhi; rn; rm])
    }
  | SignedMultiplyWordB (c, rd, rn, rm) -> {
      mnemonic = "SMULWB";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULWB" c [rd; rn; rm])
    }
  | SignedMultiplyWordT (c, rd, rn, rm) -> {
      mnemonic = "SMULWT";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULWT" c [rd; rn; rm])
    }
  | StoreCoprocessor (islong, ista2, c, coproc, crd, dst, option) ->
     let mnemonic =
       match (islong, ista2) with
       | (false, false) -> "STC"
       | (false, true) -> "STC2"
       | (true, false) -> "STCL"
       | (true, true) -> "STC2L" in
     let preops =
       "p" ^ (string_of_int coproc) ^ ", " ^ "c" ^ (string_of_int crd) ^ "," in
     {
       mnemonic = mnemonic;
       operands = [dst];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~preops mnemonic c [dst])
     }
  | StoreMultipleDecrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "STMDA";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "STMDA" c [rn; rl])
    }
  | StoreMultipleDecrementBefore (wb, c, rn, rl, mem) -> {
      mnemonic = "STMDB";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "STMDB" c [rn; rl])
    }
  | StoreMultipleIncrementAfter (wb, c, rn, rl, mem, tw) -> {
      mnemonic = "STM";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STM" c [rn; rl])
    }
  | StoreMultipleIncrementBefore (wb, c, rn, rl, mem) -> {
      mnemonic = "STMIB";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "STMIB" c [rn; rl])
    }
  | StoreRegister (c, rt, rn, rm, mem, tw) -> {
      mnemonic = "STR";
      operands = [rt; rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STR" c [rt; mem])
    }
  | StoreRegisterByte (c, rt, rn, rm, mem, tw) -> {
      mnemonic = "STRB";
      operands = [rt; rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STRB" c [rt; mem])
    }
  | StoreRegisterDual (c, rt, rt2, rn, rm, mem, mem2) -> {
      mnemonic = "STRD";
      operands = [rt; rt2; rn; rm; mem; mem2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "STRD" c [rt; rt2; mem])
    }
  | StoreRegisterExclusive (c, rd, rt, rn, mem) -> {
      mnemonic = "STREX";
      operands = [rd; rt; rn; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "STREX" c [rd; rt; mem])
    }
  | StoreRegisterHalfword (c, rt, rn, rm, mem, tw) -> {
      mnemonic = "STRH";
      operands = [rt; rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STRH" c [rt; mem])
    }
  | Subtract (s, c, rd, rn, rm, tw, w) ->
     let mnemonic = if w then "SUBW" else "SUB" in
     {
       mnemonic = mnemonic;
       operands = [rd; rn; rm];
       flags_set = if s then [APSR_N; APSR_Z; APSR_C; APSR_V] else [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s mnemonic c [rd; rn; rm])
    }
  | SubtractCarry (s, c, rd, rn, rm, tw) -> {
      mnemonic = "SBC";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C; APSR_V] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "SBC" c [rd; rn; rm])
    }
  | SupervisorCall (cc, imm) -> {
      mnemonic = "SVC";
      operands = [imm];
      flags_set = [];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "SVC" cc [ imm ])
    }
  | Swap (c, rt, rt2, mem) -> {
      mnemonic = "SWP";
      operands = [rt; rt2; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SWP" c [rt; rt2; mem])
    }
  | SwapByte (c, rt, rt2, mem) -> {
      mnemonic = "SWPB";
      operands = [rt; rt2; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SWPB" c [rt; rt2; mem])
    }
  | TableBranchByte (c, rn, rm, mem) -> {
      mnemonic = "TBB";
      operands = [rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "TBB" c [mem])
    }
  | TableBranchHalfword (c, rn, rm, mem) -> {
      mnemonic = "TBH";
      operands = [rn; rm; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "TBH" c [mem])
    }
  | Test (c, rn, rm, tw) -> {
      mnemonic = "TST";
      operands = [rn; rm];
      flags_set = [APSR_N; APSR_Z; APSR_C];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "TST" c [rn; rm])
    }
  | TestEquivalence (c, rn, rm) -> {
      mnemonic = "TEQ";
      operands = [rn; rm];
      flags_set = [APSR_N; APSR_Z; APSR_C];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "TEQ" c [rn; rm])
    }
  | UnsignedAdd8 (c, rd, rn, rm) -> {
      mnemonic = "UADD8";
      operands = [rd; rn; rm];
      flags_set = [];  (* Note: Armv7 has GE bits for parallel add *)
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UADD8" c [rd; rn; rm])
    }
  | UnsignedBitFieldExtract (c, rd, rn) -> {
      mnemonic = "UBFX";
      operands = [rd; rn];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UBFX" c [rd; rn])
    }
  | UnsignedDivide (c, rd, rn, rm) -> {
      mnemonic = "UDIV";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UDIV" c [rd; rn; rm])
    }
  | UnsignedExtendAddByte (c, rd, rn, rm) -> {
      mnemonic = "UXTAB";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UXTAB" c [rd; rn; rm])
    }
  | UnsignedExtendAddHalfword (c, rd, rn, rm) -> {
      mnemonic = "UXTAH";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UXTAH" c [rd; rn; rm])
    }
  | UnsignedExtendByte (c, rd, rm, tw) -> {
      mnemonic = "UXTB";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "UXTB" c [rd; rm])
    }
  | UnsignedExtendHalfword (c, rd, rm, tw) -> {
      mnemonic = "UXTH";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "UXTH" c [rd; rm])
    }
  | UnsignedMultiplyAccumulateLong (s, c, rdlo, rdhi, rn, rm) -> {
      mnemonic = "UMLAL";
      operands = [rdlo; rdhi; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~writeback:s "UMLAL" c [rdlo; rdhi; rn; rm])
    }
  | UnsignedMultiplyLong (s, c, rdlo, rdhi, rn, rm) -> {
      mnemonic = "UMULL";
      operands = [rdlo; rdhi; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~writeback:s "UMULL" c [rdlo; rdhi; rn; rm])
    }
  | UnsignedSaturate (c, rd, imm, rn) -> {
      mnemonic = "USAT";
      operands = [rd; imm; rn];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "USAT" c [rd; imm; rn])
    }
  | UnsignedSaturatingSubtract8 (c, rd, rn, rm) -> {
      mnemonic = "UQSUB8";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UQSUB8" c [rd; rn; rm])
    }
  | VectorAbsolute (c, dt, dst, src) -> {
      mnemonic = "VABS";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VABS" c [dst; src])
    }
  | VectorAdd (c, dt, dst, src1, src2) -> {
      mnemonic = "VADD";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VADD" c [dst; src1; src2])
    }
  | VectorAddLong (c, dt, dst, src1, src2) -> {
      mnemonic = "VADDL";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VADDL" c [dst; src1; src2])
    }
  | VectorAddWide (c, dt, dst, src1, src2) -> {
      mnemonic = "VADDW";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VADDW" c [dst; src1; src2])
    }
  | VectorBitwiseAnd (c, dst, src1, src2) -> {
      mnemonic = "VAND";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VAND" c [dst; src1; src2])
    }
  | VectorBitwiseBitClear (c, dt, vd, vn, vm) -> {
      mnemonic = "VBIC";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm =
        match dt with
        | VfpNone -> (fun f -> f#opscc "VBIC" c [vd; vn; vm])
        | _ -> (fun f -> f#opscc ~dt "VBIC" c [vd; vm])
    }
  | VectorBitwiseExclusiveOr (c, dst, src1, src2) -> {
      mnemonic = "VEOR";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VEOR" c [dst; src1; src2])
    }
  | VectorBitwiseNot (c, dt, dst, src) -> {
      mnemonic = "VMVN";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMVN" c [dst; src])
    }
  | VectorBitwiseOr (c, dt, dst, src1, src2) -> {
      mnemonic = "VORR";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VORR" c [dst; src1; src2])
    }
  | VectorBitwiseOrNot (c, dt, vd, vn, vm) -> {
      mnemonic = "VORN";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VORN" c [vd; vn; vm])
    }
  | VectorBitwiseSelect (c, dt, vd, vn, vm) -> {
      mnemonic = "VBSL";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VBSL" c [vd; vn; vm])
    }
  | VCompare (nan, c, dt, fdst, op1, op2) ->
     let mnemonic =
       "VCMP" ^ (if nan then "E" else "") in
     { mnemonic = mnemonic;
       operands = [fdst; op1; op2];
       (* use for now, to reflect that the results are often transferred
          via VMRS *)
       flags_set = [APSR_N; APSR_Z; APSR_C; APSR_V];
       (* flags_set = [];  floating point status word not yet supported *)
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~dt mnemonic c [op1; op2])
     }
  | VectorConvert (round, fixed, c, dstdt, srcdt, dst, src, fbits) ->
     let mnemonic =
       "VCVT" ^ (if round then "R" else "") in
     { mnemonic = mnemonic;
       operands = if fixed then [dst; src; fbits] else [dst; src];
       flags_set = [];
       ccode = Some c;
       ida_asm =
         (fun f ->
           f#opscc
             ~dt:dstdt
             ~dt2:srcdt
             mnemonic
             c
             (if fixed then [dst; src; fbits] else [dst; src]))
     }
  | VDivide (c, dt, dst, src1, src2) -> {
      mnemonic = "VDIV";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VDIV" c [dst; src1; src2])
    }
  | VectorDuplicate (c, dt, regs, elements, dst, src) -> {
      mnemonic = "VDUP";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm =
        (fun f -> f#opscc ~dt "VDUP" c [dst; src])
    }
  | VectorExtract (c, dt, dst, src1, src2, imm) -> {
      mnemonic = "VEXT";
      operands = [dst; src1; src2; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VEXT" c [dst; src1; src2; imm])
    }
  | VectorLoadFour (wb, c, dt, rl, rn, mem, rm) -> {
      mnemonic = "VLD4";
      operands = [rl; rn; mem; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VLD4" c [rl; mem])
    }
  | VectorLoadMultipleIncrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "VLDM";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VLDM" c [rn; rl])
    }
  | VectorLoadOne (wb, c, dt, rl, rn, mem, rm) -> {
      mnemonic = "VLD1";
      operands = [rl; rn; mem; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VLD1" c [rl; mem])
    }
  | VLoadRegister (c, dst, base, mem) -> {
      mnemonic = "VLDR";
      operands = [dst; base; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VLDR" c [dst; mem])
    }
  | VectorMoveDS (c, dt, dst, src) -> {
      mnemonic = "VMOV";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMOV" c [dst; src])
    }
  | VectorMoveDDSS (c, dt, dst1, dst2, ddst, src1, src2, ssrc) -> {
      mnemonic = "VMOV";
      operands = [dst1; dst2; ddst; src1; src2; ssrc];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMOV" c [dst1; dst2; src1; src2])
    }
  | VectorMoveDSS (c, dt, dst, src1, src2, ssrc) -> {
      mnemonic = "VMOV";
      operands = [dst; src1; src2; ssrc];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMOV" c [dst; src1; src2])
    }
  | VectorMoveDDS (c, dt, dst1, dst2, ddst, src) -> {
      mnemonic = "VMOV";
      operands = [dst1; dst2; ddst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMOV" c [dst1; dst2; src])
    }
  | VectorMoveLong (c, dt, dst, src) -> {
      mnemonic = "VMOVL";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMOVL" c [dst; src])
    }
  | VectorMoveNarrow (c, dt, dst, src) -> {
      mnemonic = "VMOVN";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMOVN" c [dst; src])
    }
  | VMoveRegisterStatus (c, dst, src) ->
     let flags_set =
     (*  disable to enable shortcut from VCompare
       if dst#is_special_register then
         [APSR_N; APSR_Z; APSR_C; APSR_V]
       else *)
         [] in
     { mnemonic = "VMRS";
       operands = [dst; src];
       flags_set = flags_set;
       ccode = Some c;
       ida_asm = (fun f -> f#opscc "VMRS" c [dst; src])
     }
  | VMoveToSystemRegister (c, dst, src) -> {
      mnemonic = "VMSR";
      operands = [dst; src];
      flags_set = [];
      ccode =Some c;
      ida_asm = (fun f -> f#opscc "VMSR" c [dst; src])
    }
  | VectorMultiply (c, dt, dst, src1, src2) -> {
      mnemonic = "VMUL";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMUL" c [dst; src1; src2])
    }
  | VectorMultiplyAccumulate (c, dt, dst, src1, src2) -> {
      mnemonic = "VMLA";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMLA" c [dst; src1; src2])
    }
  | VectorMultiplyAccumulateLong (c, dt, dst, src1, src2) -> {
      mnemonic = "VMLAL";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMLAL" c [dst; src1; src2])
    }
  | VectorMultiplyLong (c, dt, dst, src1, src2) -> {
      mnemonic = "VMULL";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMULL" c [dst; src1; src2])
    }
  | VectorMultiplySubtract (c, dt, dst, src1, src2) -> {
      mnemonic = "VMLS";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMLS" c [dst; src1; src2])
    }
  | VectorNegate (c, dt, dst, src) -> {
      mnemonic = "VNEG";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VNEG" c [dst; src])
    }
  | VectorNegateMultiply (c, dt, dst, src1, src2) -> {
      mnemonic = "VNMUL";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VNMUL" c [dst; src1; src2])
    }
  | VectorNegateMultiplyAccumulate (c, dt, dst, src1, src2) -> {
      mnemonic = "VNMLA";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VNMLA" c [dst; src1; src2])
    }
  | VectorNegateMultiplySubtract (c, dt, dst, src1, src2) -> {
      mnemonic = "VNMLS";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VNMLS" c [dst; src1; src2])
    }
  | VectorPop (c, sp, rl, mem) -> {
      mnemonic = "VPOP";
      operands = [sp; rl; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VPOP" c [rl])
    }
  | VectorPush (c, sp, rl, mem) -> {
      mnemonic = "VPUSH";
      operands = [sp; rl; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VPUSH" c [rl])
    }
  | VectorReverseDoublewords (c, dt, dst, src) -> {
      mnemonic = "VREV64";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VREV64" c [dst; src])
    }
  | VectorReverseHalfwords (c, dt, dst, src) -> {
      mnemonic = "VREV16";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VREV16" c [dst; src])
    }
  | VectorReverseWords (c, dt, dst, src) -> {
      mnemonic = "VREV32";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VREV32" c [dst; src])
    }
  | VectorRoundingHalvingAdd (c, dt, vd, vn, vm) -> {
      mnemonic = "VRHADD";
      operands = [vd; vn; vm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VRHADD" c [vd; vn; vm])
    }
  | VectorRoundingShiftRightAccumulate (c, dt, dst, src, imm) -> {
      mnemonic = "VRSRA";
      operands = [dst; src; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VRSRA" c [dst; src; imm])
    }
  | VectorShiftLeft (c, dt, dst, src, src2) -> {
      mnemonic = "VSHL";
      operands = [dst; src; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VSHL" c [dst; src; src2])
    }
  | VectorShiftLeftInsert (c, dt, dst, src, imm) -> {
      mnemonic = "VSLI";
      operands = [dst; src; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VSLI" c [dst; src; imm])
    }
  | VectorShiftRight (c, dt, dst, src, imm) -> {
      mnemonic = "VSHR";
      operands = [dst; src; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VSHR" c [dst; src; imm])
    }
  | VectorShiftRightInsert (c, dt, dst, src, imm) -> {
      mnemonic = "VSRI";
      operands = [dst; src; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VSRI" c [dst; src; imm])
    }
  | VectorShiftRightAccumulate (c, dt, dst, src, imm) -> {
      mnemonic = "VSRA";
      operands = [dst; src; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VSRA" c [dst; src; imm])
    }
  | VectorShiftRightNarrow (c, dt, dst, src, imm) -> {
      mnemonic = "VSHRN";
      operands = [dst; src; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VSHRN" c [dst; src; imm])
    }
  | VStoreRegister (c, src, base, mem) -> {
      mnemonic = "VSTR";
      operands = [src; base; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VSTR" c [src; mem])
    }
  | VectorStoreMultipleDecrementBefore (wb, c, rn, rl, mem) -> {
      mnemonic = "VSTMDB";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VSTMDB" c [rn; rl])
    }
  | VectorStoreMultipleIncrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "VSTM";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VSTM" c [rn; rl])
    }
  | VectorStoreFour (wb, c, dt, rl, rn, mem, rm) -> {
      mnemonic = "VST4";
      operands = [rl; rn; mem; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VST4" c [rl; mem])
    }
  | VectorStoreOne (wb, c, dt, rl, rn, mem, rm) -> {
      mnemonic = "VST1";
      operands = [rl; rn; mem; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VST1" c [rl; mem])
    }
  | VectorStoreTwo (wb, c, dt, rl, rn, mem, rm) -> {
      mnemonic = "VST2";
      operands = [rl; rn; mem; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VST2" c [rl; mem])
    }
  | VectorSubtract (c, dt, dst, src1, src2) -> {
      mnemonic = "VSUB";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VSUB" c [dst; src1; src2])
    }
  | VectorTableLookup (c, dt, dst, table, index) -> {
      mnemonic = "VTBL";
      operands = [dst; table; index];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VTBL" c [dst; table; index])
    }
  | VectorTranspose (c, dt, dst, src) -> {
      mnemonic = "VTRN";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VTRN" c [dst; src])
    }
  | VectorZip (c, dt, op1, op2) -> {
      mnemonic = "VZIP";
      operands = [op1; op2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VZIP" c [op1; op2])
    }
  | NoOperation c -> {
      mnemonic = "NOP";
      operands = [];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "NOP" c [])
    }
  | PermanentlyUndefined (c, op) -> {
      mnemonic = "UDF";
      operands = [op];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UDF" c [op])
    }
  | OpInvalid | NotCode _ -> {
      mnemonic = "invalid";
      operands = [];
      flags_set = [];
      ccode = None;
      ida_asm = (fun f -> f#no_ops "invalid")
    }
  | OpcodeUndefined s -> {
      mnemonic = "UNDEFINED";
      operands = [];
      flags_set = [];
      ccode = None;
      ida_asm = (fun f -> f#no_ops ("UNDEFINED: " ^ s))
    }
  | OpcodeUnpredictable s -> {
      mnemonic = "UNPREDICTABLE";
      operands = [];
      flags_set = [];
      ccode = None;
      ida_asm = (fun f -> f#no_ops ("UNPREDICTABLE: " ^ s))
    }
  | NotRecognized (name, dw) -> {
      mnemonic = "unknown";
      operands = [];
      flags_set = [];
      ccode = None;
      ida_asm = (fun f -> f#no_ops ("unknown " ^ name ^ ": " ^ dw#to_hex_string))
    }

class string_formatter_t (width:int): [string] opcode_formatter_int =
object (self)

  method ops
           ?(preops: string="")
           ?(postops: string="")
           (s:string) (operands:arm_operand_int list) =
    let s =
      if preops = "" then
        (fixed_length_string s width)
      else
        (fixed_length_string s width) ^ " " ^ preops in
    let (_,result) =
      List.fold_left
        (fun (isfirst, a) op ->
          if isfirst then
            (false, s ^ " " ^ op#toString)
          else
            (false, a ^ ", " ^ op#toString)) (true,s) operands in
    result ^ postops

  method opscc
           ?(thumbw: bool=false)
           ?(dt: vfp_datatype_t=VfpNone)
           ?(dt2: vfp_datatype_t=VfpNone)
           ?(writeback: bool=false)
           ?(preops: string="")
           ?(postops: string="")
           (s:string)
           (cc:arm_opcode_cc_t)
           (operands:arm_operand_int list) =
    let wmod = if thumbw then ".W" else "" in
    let wdt = vfp_datatype_to_string dt in
    let wdt2 = vfp_datatype_to_string dt2 in
    let wbmod = if writeback then "S" else "" in
    let mnemonic =
      s ^ wbmod ^ (get_cond_mnemonic_extension cc) ^ wmod ^ wdt ^ wdt2 in
    try
      self#ops ~preops ~postops mnemonic operands
    with
    | BCH_failure p ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "Error in opcode: "; STR mnemonic; STR": "; p]))

  method no_ops (s:string) = s

end


let get_arm_operands (opc:arm_opcode_t) = (get_record opc).operands


let get_arm_opcode_name (opc:arm_opcode_t): string
  = (get_record opc).mnemonic


let get_arm_flags_set (opc: arm_opcode_t): arm_cc_flag_t list =
  (get_record opc).flags_set


let get_arm_flags_used (opc: arm_opcode_t): arm_cc_flag_t list =
  match (get_record opc).ccode with
  | Some c -> get_cond_flags_used c
  | _ -> []


let get_arm_opcode_condition (opc: arm_opcode_t): arm_opcode_cc_t option =
  (get_record opc).ccode


let is_opcode_conditional (opc: arm_opcode_t): bool =
  match get_arm_opcode_condition opc with
  | Some cc -> is_cond_conditional cc
  | _ -> false


let arm_opcode_to_string ?(width=12) (opc:arm_opcode_t) =
  let formatter = new string_formatter_t width in
  let default () = (get_record opc).ida_asm formatter in
  default ()


let get_operands_written (opc:arm_opcode_t) =
  List.filter (fun op -> op#is_write) (get_record opc).operands


let get_operands_read (opc:arm_opcode_t) =
  List.filter (fun op -> op#is_read) (get_record opc).operands

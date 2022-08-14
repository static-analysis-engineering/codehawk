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
  | ArithmeticShiftRight (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ASR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "ASR" c [rd; rn; rm])
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
      ida_asm = (fun f -> f#opscc ~thumbw:tw "MVN" c [rd;rm])
    }
  | BitwiseOr (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ORR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "ORR" c [rd; rn; rm])
    }
  | BitwiseOrNot (s, c, rd, rn, rm) -> {
      mnemonic = "ORN";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "ORN" c [rd; rn; rm])
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
      ida_asm = (fun f -> f#opscc "BX" c [ addr ])
    }
  | BranchLink (cc, addr) -> {
      mnemonic = "BL";
      operands = [addr];
      flags_set = [];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "BL" cc [ addr ])
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
      mnemonic = "FLDMX";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "FLDMX" c [rn; rl])
    }
  | FStoreMultipleIncrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "FSTMIAX";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "FSTMIAX" c [rn; rl])
    }
  | LoadCoprocessor (islong, c, coproc, crd, src, option) ->
     let mnemonic = if islong then "LDCL" else "LDC" in
     let preops =
       "p" ^ (string_of_int coproc) ^ ", " ^ "c" ^ (string_of_int crd) in
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
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LSL" c [rd; rn; rm])
    }
  | LogicalShiftRight (s, c, rd, rn, rm, tw) -> {
      mnemonic = "LSR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LSR" c [rd; rn; rm])
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
  | MoveRegisterCoprocessor (c, coproc, opc1, rt, crn, crm, opc2) ->
     let preops =
       "p" ^ (string_of_int coproc) ^ ", " ^ (string_of_int opc1) ^ ", " in
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
       "p" ^ (string_of_int coproc) ^ ", " ^ (string_of_int opc1) ^ ", " in
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
  | MoveTwoRegisterCoprocessor (c, coproc, opc, rt, rt2, crm) ->
     let preops =
       "p" ^ (string_of_int coproc) ^ ", " ^ (string_of_int opc) ^ ", " in
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
      ida_asm = (fun f -> f#opscc ~thumbw:tw "RSB" c [rd; rn; rm])
    }
  | ReverseSubtractCarry (s, c, rd, rn, rm) -> {
      mnemonic = "RSC";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C; APSR_V] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "RSC" c [rd; rn; rm])
    }
  | RotateRight (s, c, rd, rn, rm) -> {
      mnemonic = "ROR";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "ROR" c [rd; rn; rm])
    }
  | RotateRightExtend (s, c, rd, rm) -> {
      mnemonic = "RRX";
      operands = [rd; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "RRX" c [rd; rm])
    }
  | SelectBytes (c, rd, rn, rm) -> {
      mnemonic = "SEL";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SEL" c [rd; rn; rm])
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
  | SignedMultiplyAccumulateLong (s, c, rdlo, rdhi, rn, rm) -> {
      mnemonic = "SMLAL";
      operands = [rdlo; rdhi; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLAL" ~writeback:s c [rdlo; rdhi; rn; rm])
    }
  | SignedMultiplyLong (s, c, rdlo, rdhi, rn, rm) -> {
      mnemonic = "SMULL";
      operands = [rdlo; rdhi; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULL" c [rdlo; rdhi; rn; rm])
    }
  | SingleBitFieldExtract (c, rd, rn) -> {
      mnemonic = "SBFX";
      operands = [rd; rn];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SBFX" c [rd;rn])
    }
  | StoreMultipleDecrementBefore (wb, c, rn, rl, mem, tw) -> {
      mnemonic = "STMDB";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STMDB" c [rn; rl])
    }
  | StoreMultipleIncrementAfter (wb, c, rn, rl, mem, tw) -> {
      mnemonic = "STM";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STM" c [rn; rl])
    }
  | StoreMultipleIncrementBefore (wb, c, rn, rl, mem, tw) -> {
      mnemonic = "STMIB";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STMIB" c [rn; rl])
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
       ida_asm = (fun f -> f#opscc ~thumbw:tw mnemonic c [rd; rn; rm])
    }
  | SubtractCarry (s, c, rd, rn, rm, tw) -> {
      mnemonic = "SBC";
      operands = [rd; rn; rm];
      flags_set = if s then [APSR_N; APSR_Z; APSR_C; APSR_V] else [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "SBC" c [rd; rn; rm])
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
  | Test (c,rn,rm) -> {
      mnemonic = "TST";
      operands = [rn; rm];
      flags_set = [APSR_N; APSR_Z; APSR_C];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "TST" c [rn; rm])
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
  | UnsignedExtendHalfword (c, rd, rm) -> {
      mnemonic = "UXTH";
      operands = [rd; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UXTH" c [rd; rm])
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
  | UnsignedSaturatingSubtract8 (c, rd, rn, rm) -> {
      mnemonic = "UQSUB8";
      operands = [rd; rn; rm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UQSUB8" c [rd; rn; rm])
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
  | VectorBitwiseBitClear (c, dt, dst, imm) -> {
      mnemonic = "VBIC";
      operands = [dst; imm];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VBIC" c [dst; imm])
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
  | VectorBitwiseOr (c, dst, src1, src2) -> {
      mnemonic = "VORR";
      operands = [dst; src1; src2];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VORR" c [dst; src1; src2])
    }
  | VCompare (nan, c, dt, op1, op2) ->
     let mnemonic =
       "VCMP" ^ (if nan then "E" else "") in
     { mnemonic = mnemonic;
       operands = [op1; op2];
       flags_set = [];   (* floating point status word not yet supported *)
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~dt mnemonic c [op1; op2])
     }
  | VectorConvert (round, c, dstdt, srcdt, dst, src) ->
     let mnemonic =
       "VCVT" ^ (if round then "R" else "") in
     { mnemonic = mnemonic;
       operands = [dst; src];
       flags_set = [];
       ccode = Some c;
       ida_asm = (fun f -> f#opscc ~dt:dstdt ~dt2:srcdt mnemonic c [dst; src])
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
  | VectorMove (c, dt, ops) -> {
      mnemonic = "VMOV";
      operands = ops;
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VMOV" c ops)
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
       if dst#is_special_register then
         [APSR_N; APSR_Z; APSR_C; APSR_V]
       else
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
  | VectorNegate (c, dt, dst, src) -> {
      mnemonic = "VNEG";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VNEG" c [dst; src])
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
  | VStoreRegister (c, src, base, mem) -> {
      mnemonic = "VSTR";
      operands = [src; base; mem];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VSTR" c [src; mem])
    }
  | VectorStoreMultipleIncrementAfter (wb, c, rn, rl, mem) -> {
      mnemonic = "VSTM";
      operands = [rn; rl];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "VSTM" c [rn; rl])
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
  | VectorTranspose (c, dt, dst, src) -> {
      mnemonic = "VTRN";
      operands = [dst; src];
      flags_set = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~dt "VTRN" c [dst; src])
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
    let s = (fixed_length_string s width) ^ preops in
    let (_,result) =
      List.fold_left
        (fun (isfirst,a) op ->
          if isfirst then
            (false,s ^ " " ^ op#toString)
          else
            (false,a ^ ", " ^ op#toString)) (true,s) operands in
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
    self#ops ~preops ~postops mnemonic operands

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

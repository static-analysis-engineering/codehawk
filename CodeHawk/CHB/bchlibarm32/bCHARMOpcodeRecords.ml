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


class type ['a] opcode_formatter_int =
  object
    method ops: string -> arm_operand_int list -> 'a
    method opscc:
             ?thumbw: bool
             -> ?writeback: bool
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
    ida_asm: 'a opcode_formatter_int -> 'a
  }

let get_record (opc:arm_opcode_t): 'a opcode_record_t =
  match opc with
  | Add (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ADD";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "ADD" c [rd;rn;rm])
    }
  | AddCarry (s, c, rd, rn, rm, tw) -> {
      mnemonic = "ADC";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "ADC" c [rd;rn;rm])
    }
  | Adr (cc, rd, addr) -> {
      mnemonic = "ADR";
      operands = [ rd; addr ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "ADR" cc [ rd; addr ])
    }
  | ArithmeticShiftRight (s,c,rd,rn,rm,tw) -> {
      mnemonic = "ASR";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "ASR" c [rd;rn;rm])
    }
  | BitwiseAnd (setflags, cc, rd,rn, imm, tw) -> {
      mnemonic = "AND";
      operands = [ rd; rn; imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "AND" cc [ rd; rn; imm ])
    }
  | BitwiseBitClear (s,c,rd,rn,rm,tw) -> {
      mnemonic = "BIC";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "BIC" c [rd;rn;rm])
    }
  | BitwiseExclusiveOr (s,c,rd,rn,rm,tw) -> {
      mnemonic = "EOR";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "EOR" c [rd;rn;rm])
    }
  | BitwiseNot (s,c,rd,rm) -> {
      mnemonic = "MVN";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MVN" c [rd;rm])
    }
  | BitwiseOr (s,c,rd,rn,rm,tw) -> {
      mnemonic = "ORR";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "ORR" c [rd;rn;rm])
    }
  | BitwiseOrNot (s,c,rd,rn,rm) -> {
      mnemonic = "ORR";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "ORN" c [rd;rn;rm])
    }
  | Branch (cc, addr, tw) -> {
      mnemonic = "B";
      operands = [ addr ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "B" cc [ addr ])
    }
  | BranchExchange (c,addr) -> {
      mnemonic = "BX";
      operands = [ addr ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "BX" c [ addr ])
    }
  | BranchLink (cc, addr) -> {
      mnemonic = "BL";
      operands = [ addr ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "BL" cc [ addr ])
    }
  | BranchLinkExchange (c,addr) -> {
      mnemonic = "BLX";
      operands = [ addr ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "BLX" c [ addr ])
    }
  | ByteReverseWord (c,rd,rm) -> {
      mnemonic = "REV";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "REV" c [rd;rm])
    }
  | Compare (c,rn,rm,tw) -> {
      mnemonic = "CMP";
      operands = [rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "CMP" c [rn;rm])
    }
  | CompareBranchNonzero (op1, op2) -> {
      mnemonic = "CBNZ";
      operands = [op1; op2];
      ccode = None;
      ida_asm = (fun f -> f#ops "CBNZ" [op1; op2])
    }
  | CompareBranchZero (op1, op2) -> {
      mnemonic = "CBZ";
      operands = [op1; op2];
      ccode = None;
      ida_asm = (fun f -> f#ops "CBZ" [op1; op2])
    }
  | CompareNegative (cc,op1,op2) -> {
      mnemonic = "CMN";
      operands = [ op1; op2];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "CMN" cc [ op1; op2 ])
    }
  | CountLeadingZeros (c,rd,rm) -> {
      mnemonic = "CLZ";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "CLZ" c [rd;rm])
    }
  | DataMemoryBarrier (c, option) -> {
      mnemonic = "DMB";
      operands = [option];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "DMB" c [option])
    }
  | IfThen (c, xyz) ->
     let mnemonic = "IT" ^ xyz ^ " " ^ (get_cond_mnemonic_extension c) in
     { mnemonic = mnemonic;
       operands = [];
       ccode = None;
       ida_asm = (fun f -> f#ops mnemonic [])
     }
  | LoadMultipleDecrementAfter (wb,c,rn,rl,mem) -> { 
      mnemonic = "LDMDA";
      operands = [ rn; rl; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDMDA" c [ rn; rl ])
    }
  | LoadMultipleDecrementBefore (wb,c,rn,rl,mem) -> { 
      mnemonic = "LDMDB";
      operands = [ rn; rl; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDMDB" c [ rn; rl ])
    }
  | LoadMultipleIncrementAfter (wb,c,rn,rl,mem) -> { 
      mnemonic = "LDM";
      operands = [ rn; rl; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDM" c [ rn; rl ])
    }
  | LoadMultipleIncrementBefore (wb,c,rn,rl,mem) -> { 
      mnemonic = "LDMIB";
      operands = [ rn; rl; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDMIB" c [ rn; rl ])
    }
  | LoadRegister (c,rt,rn,mem,tw) -> {
      mnemonic = "LDR";
      operands = [ rt; rn; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDR" c [ rt; mem ])
    }
  | LoadRegisterByte (c,rt,rn,mem,tw) -> {
      mnemonic = "LDRB";
      operands = [ rt; rn; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDRB" c [ rt; mem ])
    }
  | LoadRegisterDual (c,rt,rt2,rn,rm,mem) -> {
      mnemonic = "LDRD";
      operands = [rt;rt2;rn;rm;mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDRD" c [rt;rt2;mem])
    }
  | LoadRegisterExclusive (c, rt, rn, mem) -> {
      mnemonic = "LDREX";
      operands = [rt; rn; mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "LDREX" c [rt;mem])
    }
  | LoadRegisterHalfword (c,rt,rn,rm,mem,tw) -> {
      mnemonic = "LDRH";
      operands = [rt;rn;rm;mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDRH" c [rt;mem])
    }
  | LoadRegisterSignedByte (c,rt,rn,rm,mem,tw) -> {
      mnemonic = "LDRSB";
      operands = [ rt; rn; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDRSB" c [ rt; mem ])
    }
  | LoadRegisterSignedHalfword (c,rt,rn,rm,mem,tw) -> {
      mnemonic = "LDRSH";
      operands = [ rt; rn; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LDRSH" c [ rt; mem ])
    }
  | LogicalShiftLeft (s,c,rd,rn,rm,tw) -> {
      mnemonic = "LSL";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LSL" c [rd;rn;rm])
    }
  | LogicalShiftRight (s,c,rd,rn,rm,tw) -> {
      mnemonic = "LSR";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "LSR" c [rd;rn;rm])
    }
  | Move (s, c, rd, rm, tw) -> {
      mnemonic = "MOV";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw ~writeback:s "MOV" c [rd;rm])
    }
  | MoveTop (c,rd,imm) -> {
      mnemonic = "MOVT";
      operands = [ rd; imm ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MOVT" c [ rd; imm ])
    }
  | MoveWide (c,rd,imm) -> {
      mnemonic = "MOVW";
      operands = [ rd; imm ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MOVW" c [ rd; imm ])
    }
  | Multiply (s,c,rd,rn,rm) -> {
      mnemonic = "MUL";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MUL" c [rd;rn;rm])
    }
  | MultiplyAccumulate (s,c,rd,rn,rm,ra) -> {
      mnemonic = "MLA";
      operands = [rd;rn;rm;ra];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "MLA" c [rd;rn;rm;ra])
    }
  | Pop (c,sp,rl,tw) -> {
      mnemonic = "POP";
      operands = [ sp; rl ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "POP" c [ rl ])
    }
  | Push (c,sp,rl,tw) -> {
      mnemonic = "PUSH";
      operands = [ sp; rl ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "PUSH" c [ rl ])
    }
  | ReverseSubtract (s,c,rd,rn,rm,tw) -> {
      mnemonic = "RSB";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "RSB" c [rd;rn;rm])
    }
  | ReverseSubtractCarry (setflags, cc, rd, rn, rm) -> {
      mnemonic = "RSC";
      operands = [ rd; rn; rm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "RSC" cc [ rd; rn; rm ])
    }
  | RotateRight (s, c, rd, rn, rm) -> {
      mnemonic = "ROR";
      operands = [ rd; rn; rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "ROR" c [rd; rn; rm])
    }
  | RotateRightExtend (s,c,rd,rm) -> {
      mnemonic = "RRX";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "RRX" c [rd;rm])
    }
  | SignedExtendByte (c,rd,rm) -> {
      mnemonic = "SXTB";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SXTB" c [rd;rm])
    }
  | SignedExtendHalfword (c,rd,rm) -> {
      mnemonic = "SXTH";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SXTH" c [rd;rm])
    }
  | SignedMultiplyAccumulateLong (s, c, rdlo, rdhi, rn, rm) -> {
      mnemonic = "SMLAL";
      operands = [rdlo; rdhi; rn; rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMLAL" ~writeback:s c [rdlo; rdhi; rn; rm])
    }
  | SignedMultiplyLong (s, c, rdlo, rdhi, rn, rm) -> {
      mnemonic = "SMULL";
      operands = [rdlo; rdhi; rn; rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SMULL" c [rdlo; rdhi; rn; rm])
    }
  | SingleBitFieldExtract (c,rd,rn) -> {
      mnemonic = "SBFX";
      operands = [rd;rn];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SBFX" c [rd;rn])
    }
  | StoreMultipleDecrementBefore (wb,c,rn,rl,mem,tw) -> {
      mnemonic = "STMDB";
      operands = [ rn; rl ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STMDB" c [ rn; rl ])
    }
  | StoreMultipleIncrementAfter (wb,c,rn,rl,mem,tw) -> { 
      mnemonic = "STM";
      operands = [ rn; rl ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STM" c [ rn; rl ])
    }
  | StoreMultipleIncrementBefore (wb,c,rn,rl,mem,tw) -> { 
      mnemonic = "STMIB";
      operands = [ rn; rl ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STMIB" c [ rn; rl ])
    }
  | StoreRegister (c,rt,rn,mem,tw) -> {
      mnemonic = "STR";
      operands = [ rt; rn; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STR" c [ rt; mem ])
    }
  | StoreRegisterByte (c,rt,rn,mem,tw) -> {
      mnemonic = "STRB";
      operands = [ rt; rn; mem ];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STRB" c [ rt; mem ])
    }
  | StoreRegisterDual (c,rt,rt2,rn,rm,mem) -> {
      mnemonic = "STRD";
      operands = [rt;rt2;rn;rm;mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "STRD" c [rt;rt2;mem])
    }
  | StoreRegisterExclusive (c, rd, rt, rn, mem) -> {
      mnemonic = "STREX";
      operands = [rd; rt; rn; mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "STREX" c [rd; rt; mem])
    }
  | StoreRegisterHalfword (c,rt,rn,rm,mem,tw) -> {
      mnemonic = "STRH";
      operands = [rt;rn;rm;mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "STRH" c [rt;mem])
    }
  | Subtract (s,c,rd,rn,rm,tw) -> {
      mnemonic = "SUB";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc ~thumbw:tw "SUB" c [rd;rn;rm])
    }
  | SubtractCarry (s,c,rd,rn,rm) -> {
      mnemonic = "SBC";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SBC" c [rd;rn;rm])
    }
  | SupervisorCall (cc,imm) -> {
      mnemonic = "SVC";
      operands = [ imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "SVC" cc [ imm ])
    }
  | Swap (c,rt,rt2,mem) -> {
      mnemonic = "SWP";
      operands = [rt; rt2; mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SWP" c [rt; rt2; mem])
    }
  | SwapByte (c,rt,rt2,mem) -> {
      mnemonic = "SWPB";
      operands = [rt; rt2; mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "SWPB" c [rt; rt2; mem])
    }
  | TableBranchByte (c, rn, rm, mem) -> {
      mnemonic = "TBB";
      operands = [rn; rm; mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "TBB" c [mem])
    }
  | TableBranchHalfword (c, rn, rm, mem) -> {
      mnemonic = "TBH";
      operands = [rn; rm; mem];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "TBH" c [mem])
    }
  | Test (c,rn,rm) -> {
      mnemonic = "TST";
      operands = [rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "TST" c [rn;rm])
    }
  | TestEquivalence (c,rn,rm) -> {
      mnemonic = "TEQ";
      operands = [rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "TEQ" c [rn;rm])
    }
  | UnsignedBitFieldExtract (c,rd,rn) -> {
      mnemonic = "UBFX";
      operands = [rd;rn];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UBFX" c [rd;rn])
    }
  | UnsignedExtendAddHalfword (c,rd,rn,rm) -> {
      mnemonic = "UXTAH";
      operands = [rd;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UXTAH" c [rd;rn;rm])
    }
  | UnsignedExtendByte (c,rd,rm) -> {
      mnemonic = "UXTB";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UXTB" c [rd;rm])
    }
  | UnsignedExtendHalfword (c,rd,rm) -> {
      mnemonic = "UXTH";
      operands = [rd;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UXTH" c [rd;rm])
    }
  | UnsignedMultiplyLong (s,c,rdlo,rdhi,rn,rm) -> {
      mnemonic = "UMULL";
      operands = [rdlo;rdhi;rn;rm];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UMULL" c [rdlo;rdhi;rn;rm])
    }
  | NoOperation c -> {
      mnemonic = "nop";
      operands = [];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "NOP" c [])
    }
  | PermanentlyUndefined (c, op) -> {
      mnemonic = "UDF";
      operands = [op];
      ccode = Some c;
      ida_asm = (fun f -> f#opscc "UDF" c [op])
    }
  | OpInvalid | NotCode _ -> {
      mnemonic = "invalid";
      operands = [];
      ccode = None;
      ida_asm = (fun f -> f#no_ops "invalid")
    }
  | NotRecognized (name, dw) -> {
      mnemonic = "unknown";
      operands = [];
      ccode = None;
      ida_asm = (fun f -> f#no_ops ("unknown " ^ name ^ ": " ^ dw#to_hex_string))
    }

class string_formatter_t (width:int): [string] opcode_formatter_int =
object (self)

  method ops (s:string) (operands:arm_operand_int list) =
    let s = fixed_length_string s width in
    let (_,result) =
      List.fold_left
        (fun (isfirst,a) op ->
          if isfirst then
            (false,s ^ " " ^ op#toString)
          else
            (false,a ^ ", " ^ op#toString)) (true,s) operands in
    result

  method opscc
           ?(thumbw: bool=false)
           ?(writeback: bool=false)
           (s:string)
           (cc:arm_opcode_cc_t)
           (operands:arm_operand_int list) =
    let wmod = if thumbw then ".W" else "" in
    let wbmod = if writeback then "S" else "" in
    let mnemonic = s ^ wbmod ^ (get_cond_mnemonic_extension cc) ^ wmod in
    self#ops mnemonic operands

  method no_ops (s:string) = s
end
                           
let get_arm_operands (opc:arm_opcode_t) = (get_record opc).operands

let get_arm_opcode_name (opc:arm_opcode_t) = (get_record opc).mnemonic

let arm_opcode_to_string ?(width=8) (opc:arm_opcode_t) =
  let formatter = new string_formatter_t width in
  let default () = (get_record opc).ida_asm formatter in
  default ()

let get_operands_written (opc:arm_opcode_t) =
  List.filter (fun op -> op#is_write) (get_record opc).operands

let get_operands_read (opc:arm_opcode_t) =
  List.filter (fun op -> op#is_read) (get_record opc).operands

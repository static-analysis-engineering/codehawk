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
  | ACCUnconditional ->
     raise
       (BCH_failure
          (LBLOCK [ STR "Unexpected value for mnemonic extension" ]))

class type ['a] opcode_formatter_int =
  object
    method ops: string -> arm_operand_int list -> 'a
    method opscc: string -> arm_opcode_cc_t -> arm_operand_int list -> 'a
    method no_ops: string -> 'a
  end

type 'a opcode_record_t = {
    mnemonic: string;
    operands: arm_operand_int list;
    ccode: arm_opcode_cc_t option;
    ida_asm: 'a
  }

let get_record (opc:arm_opcode_t) =
  match opc with
  | Add (setflags, cc, rd, rn, imm) -> {
      mnemonic = "ADD";
      operands = [ rd; rn; imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "ADD" cc [ rd; rn; imm ])
    }
  | Adr (cc, rd, addr) -> {
      mnemonic = "ADR";
      operands = [ rd; addr ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "ADR" cc [ rd; addr ])
    }
  | BitwiseNot (setflags, cc, rd, imm) -> {
      mnemonic = "MVN";
      operands = [ rd; imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "MVN" cc [ rd; imm ])
    }
  | BitwiseOr (setflags, cc, rd, rn, imm) -> {
      mnemonic = "ORR";
      operands = [ rd; rn; imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "ORR" cc [ rd; rn; imm ])
    }
  | Branch (cc, addr) -> {
      mnemonic = "B";
      operands = [ addr ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "B" cc [ addr ])
    }
  | BranchExchange (cc, addr) -> {
      mnemonic = "BX";
      operands = [ addr ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "BX" cc [ addr ])
    }
  | BranchLink (cc, addr) -> {
      mnemonic = "BL";
      operands = [ addr ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "BL" cc [ addr ])
    }
  | BranchLinkExchange (cc, addr) -> {
      mnemonic = "BLX";
      operands = [ addr ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "BLX" cc [ addr ])
    }
  | Compare (cc,op1,op2) -> {
      mnemonic = "CMP";
      operands = [ op1; op2];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "CMP" cc [ op1; op2 ])
    }
  | LoadRegister (cc, dst, src) -> {
      mnemonic = "LDR";
      operands = [ dst; src ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "LDR" cc [ dst; src ])
    }
  | LoadRegisterByte (cc, dst, src) -> {
      mnemonic = "LDRB";
      operands = [ dst; src ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "LDRB" cc [ dst; src ])
    }
  | Mov (setflags, cc, rd, imm) -> {
      mnemonic = "MOV";
      operands = [ rd; imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "MOV" cc [ rd; imm ])
    }
  | MoveTop (setflags, cc, rd, imm) -> {
      mnemonic = "MOVT";
      operands = [ rd; imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "MOVT" cc [ rd; imm ])
    }
  | MoveWide (setflags, cc, rd, imm) -> {
      mnemonic = "MOVW";
      operands = [ rd; imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "MOVW" cc [ rd; imm ])
    }
  | Pop (cc, rl) -> {
      mnemonic = "POP";
      operands = [ rl ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "POP" cc [ rl ])
    }
  | Push (cc, rl) -> {
      mnemonic = "PUSH";
      operands = [ rl ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "PUSH" cc [ rl ])
    }
  | ReverseSubtract (setflags, cc, rd, rn, rm) -> {
      mnemonic = "RSB";
      operands = [ rd; rn; rm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "RSB" cc [ rd; rn; rm ])
    }
  | StoreRegister (cc, src, dst) -> {
      mnemonic = "STR";
      operands = [ src; dst ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "STR" cc [ src; dst ])
    }
  | StoreRegisterByte (cc, src, dst) -> {
      mnemonic = "STRB";
      operands = [ src; dst ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "STRB" cc [ src; dst ])
    }                                  
  | Subtract (setflags, cc, rd, rn, imm) -> {
      mnemonic = "SUB";
      operands = [ rd; rn; imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "SUB" cc [ rd; rn; imm ])
    }
  | SupervisorCall (cc,imm) -> {
      mnemonic = "SVC";
      operands = [ imm ];
      ccode = Some cc;
      ida_asm = (fun f -> f#opscc "SVC" cc [ imm ])
    }
  | OpInvalid -> {
      mnemonic = "invalid";
      operands = [];
      ccode = None;
      ida_asm = (fun f -> f#no_ops "invalid")
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

  method opscc (s:string) (cc:arm_opcode_cc_t) (operands:arm_operand_int list) =
    let mnemonic = s ^ (get_cond_mnemonic_extension cc) in
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

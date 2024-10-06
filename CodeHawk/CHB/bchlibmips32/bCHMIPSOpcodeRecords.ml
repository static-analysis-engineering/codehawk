(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes

(* bchlibmips32 *)
open BCHMIPSTypes
   

let mips_fp_format_to_string f =
  match f with
  | FPSingle -> "s"
  | FPDouble -> "d"
  | FPFixedWord -> "w"
  | FPFixedLong -> "l"
  | FPPair -> "p"

let mips_fp_predicate_to_string p =
  match p with
  | 0 -> "f"
  | 1 -> "un"
  | 2 -> "eq"
  | 3 -> "ueq"
  | 4 -> "olt"
  | 5 -> "ult"
  | 6 -> "ole"
  | 7 -> "ule"
  | _ ->
     raise (BCH_failure
              (LBLOCK [STR "FP predicate code "; INT p; STR " not recognized"]))
   

class type ['a]  opcode_formatter_int =
object
  method ops: string -> mips_operand_int list -> 'a
  method cc_ops: string -> int -> mips_operand_int list -> 'a
  method int_ops: string -> mips_operand_int list -> int list -> 'a
  method pre_int_ops: string -> int list -> mips_operand_int list -> 'a
  method no_ops: string -> 'a
end 


type 'a opcode_record_t = {
    mnemonic: string;
    operands: mips_operand_int list;
    delay_slot: bool;
    ida_asm: 'a
  }


let get_record (opc:mips_opcode_t) =
  match opc with
  | BranchLEZero (src, target) -> {
      mnemonic = "blez";
      operands = [src; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "blez" [src; target])
    }
  | BranchLEZeroLikely (src, target) -> {
      mnemonic = "blezl";
      operands = [src; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "blezl" [src; target])
    }
  | BranchLTZero (src, target) -> {
      mnemonic = "bltz";
      operands = [src; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "bltz" [src; target])
    }
  | BranchLTZeroLikely (src,target) -> {
      mnemonic   = "bltzl";
      operands   = [src; target];
      delay_slot  = true;
      ida_asm  = (fun f -> f#ops "bltzl" [src; target])
    }
  | BranchGEZero (src, target) ->  {
      mnemonic = "bgez";
      operands = [src; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "bgez" [src; target])
    }
  | BranchGEZeroLikely (src,target) ->  {
      mnemonic   = "bgezl";
      operands   = [src; target];
      delay_slot = true;
      ida_asm    = (fun f -> f#ops "bgezl" [src; target])
    }
  | BranchGTZero (src, target) ->  {
      mnemonic = "bgtz";
      operands = [src; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "bgtz" [src; target])
    }
  | BranchGTZeroLikely  (src, target) -> {
      mnemonic = "bgtzl";
      operands = [src; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "bgtzl" [src; target])
    }
  | BranchLTZeroLink (src, target) -> {
      mnemonic =  "bltzal";
      operands = [src; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "bltzal" [src; target])
    }
  | BranchGEZeroLink (src, target) -> {
      mnemonic = "bgezal";
      operands = [src; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "bgezal" [src; target])
    }

  (* ---------------------------------------------------------------------------
   * Format: B offset
   * Description: 
   * B offset is the assembly idiom used to denote an unconditional branch. The 
   * actual instruction is interpreted by the hardware as BEQ r0, r0, offset.
   * ---------------------------------------------------------------------------
   * An 18-bit signed offset (the 16-bit offset field shifted left 2 bits) is 
   * added to the address of the instruction following the branch (not the 
   * branch itself), in the branch delay slot, to form a PC-relative effective 
   * target address.
   * ---------------------------------------------------------------------------
   * Operation
   *   I   : target_offset <- sign-extend(offset) * 4
   *   I+1 : PC <- PC + target_offset
   * --------------------------------------------------------------------------- *)
  | Branch target -> {
      mnemonic   = "b";
      operands   = [target];
      delay_slot = true;
      ida_asm    = (fun f -> f#ops "b" [target])
    }

  (* ---------------------------------------------------------------------------
   * Format: BAL offset
   * Description: procedure call
   * Pre-Release 6: BAL offset is the assembly idiom used to denote an 
   * unconditional branch. The actual instruction is interpreted by the hardware 
   * as BGEZAL r0, offset.
   * Release 6 keeps the BAL special case of BGEZAL, but removes all other 
   * instances of BGEZAL. BGEZAL with rs any register other than GPR[0] is 
   * required to signal a Reserved Instruction exception.
   * ---------------------------------------------------------------------------
   * Place the return address link in GPR 31. The return link is the address of 
   * the second instruction following the branch, where execution continues 
   * after a procedure call.
   * An 18-bit signed offset (the 16-bit offset field shifted left 2-bits) is 
   * added to the address of the instruction following the branch (not the branch 
   * itself), in the branch delay slot, to form a PC-relative effective target 
   * address.
   * ---------------------------------------------------------------------------
   * Operation
   *   I   : target_offset <- sign-extend(offset) || 00
   *         GPR[31] <- PC + 8
   *   I+1 : PC <- PC + target_offset
   * --------------------------------------------------------------------------- *)
  | BranchLink target -> {
      mnemonic   = "bal";
      operands   = [target];
      delay_slot = true;
      ida_asm    = (fun f -> f#ops "bal" [target])
    }

  (* ---------------------------------------------------------------------------
   * Format: BEQ rs, rt, offset
   * Description: if GPR[rs] = GPR[rt] then branch  
   * ---------------------------------------------------------------------------
   * An 18-bit signed offset (the 16-bit offset field shifted left 2 bits) is 
   * added to the address of the instruction following the branch (not the 
   * branch itself), in the branch delay slot, to form a PC-relative effective 
   * target address.
   * If the contents of GPR rs and GPR rt are equal, branch to the effective 
   * target address after the instruction in the delay slot is executed.
   * ---------------------------------------------------------------------------
   * Operation
   *   I   : target_offset <- sign-extend(offset) * 4
   *         condition <- GPR[rs] = GPR[rt]
   *   I+1 : if condition then
   *           PC <- PC + target_offset
   * --------------------------------------------------------------------------- *)
  | BranchEqual (src1, src2, target) -> {
      mnemonic = "beq";
      operands = [src1; src2; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "beq" [src1; src2; target])
    }
  | BranchEqualLikely (src1, src2, target) -> {    (* TBD: change delay slot behavior *)
      mnemonic = "beql";
      operands = [src1; src2; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "beql" [src1; src2; target])
    }
  | BranchNotEqual (src1, src2, target) -> {
      mnemonic = "bne";
      operands = [src1; src2; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "bne" [src1; src2; target])
    }
  | BranchNotEqualLikely (src1, src2, target) -> {
      mnemonic = "bnel";
      operands = [src1; src2; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "bnel" [src1; src2; target])
    }
                                   
  (* ----------------------------------------------- I-type arithmetic/logic  *)
  | AddImmediate (dest, src, imm) -> {
      mnemonic = "addi";
      operands = [dest; src; imm];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "addi" [dest; src; imm])
    }
                                 
  (* ---------------------------------------------------------------------------
   * Format: ADDIU rt, rs, immediate
   * Description: GPR[rt] <- GPR[rs] + immediate
   * ---------------------------------------------------------------------------
   * The 16-bit signed immediate is added to the 32-bit value in GPR rs and the 
   * 32-bit arithmetic result is placed into GPR rt.
   * No Integer Overflow exception occurs under any circumstances.
   * ---------------------------------------------------------------------------
   * Operation
   *   temp <- GPR[rs] + sign_extend(immediate)
   *   GPR[rt] <- temp
   * ---------------------------------------------------------------------------
   * The term "unsigned" in the instruction name is a misnomer; this operation 
   * is 32-bit modulo arithmetic that does not trap on overflow. This instruction 
   * is appropriate for unsigned arithmetic, such as address arithmetic, or 
   * integer arith- metic environments that ignore overflow, such as C language
   * arithmetic.
   * --------------------------------------------------------------------------- *)
  | AddImmediateUnsigned (dest,src,imm) -> {
      mnemonic   = "addiu";
      operands   = [dest; src; imm];
      delay_slot = false;
      ida_asm    =  (fun f -> f#ops "addiu" [dest; src; imm])
    }

  (* ---------------------------------------------------------------------------
   * Format: SLTI rt, rs, immediate
   * Description: GPR[rt] <- (GPR[rs] < sign_extend(immediate) )
   * ---------------------------------------------------------------------------
   * Compare the contents of GPR rs and the 16-bit signed immediate as signed 
   * integers; record the Boolean result of the comparison in GPR rt. If GPR 
   * rs is less than immediate, the result is 1 (true); otherwise, it is 0 
   * (false). 
   * The arithmetic comparison does not cause an Integer Overflow exception.
   * ---------------------------------------------------------------------------
   * Operation
   *  if GPR[rs] < sign_extend(immediate) then
   *      GPR[rt] <- 1
   *  else
   *      GPR[rt] <- 0
   * --------------------------------------------------------------------------- *)       
  | SetLTImmediate (rt,rs,imm) -> {
      mnemonic   = "slti";
      operands   = [rt; rs; imm];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "slti" [rt; rs; imm])
    }

  (* ---------------------------------------------------------------------------
   * Format: SLTIU rt, rs, immediate
   * Description: GPR[rt] <- (GPR[rs] < sign_extend(immediate))
   * ---------------------------------------------------------------------------
   * Compare the contents of GPR rs and the sign-extended 16-bit immediate 
   * as unsigned integers; record the Boolean result of the comparison in 
   * GPR rt. If GPR rs is less than immediate, the result is 1 (true); 
   * otherwise, it is 0 (false).
   * Because the 16-bit immediate is sign-extended before comparison, the 
   * instruction can represent the smallest or largest unsigned numbers. 
   * The representable values are at the minimum [0, 32767] or maximum 
   * [max_unsigned-32767, max_unsigned] end of the unsigned range.
   * The arithmetic comparison does not cause an Integer Overflow exception.
   * ---------------------------------------------------------------------------
   * Operation
   *   if (0 || GPR[rs]) < (0 || sign_extend(immediate)) then 
   *      GPR[rt] <- 1
   *   else
   *      GPR[rt] <- 0
   * --------------------------------------------------------------------------- *)
  | SetLTImmediateUnsigned (dest,src,imm) -> {
      mnemonic   = "sltiu";
      operands   = [dest; src; imm];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "sltiu" [dest; src; imm])
    }

  (* ---------------------------------------------------------------------------
   * Format: ANDI rt, rs, immediate
   * Description: GPR[rt] <- GPR[rs] and zero_extend(immediate)
   * ---------------------------------------------------------------------------
   * The 16-bit immediate is zero-extended to the left and combined with the 
   * contents of GPR rs in a bitwise logical AND operation. The result is placed 
   * into GPR rt.
   * ---------------------------------------------------------------------------
   * Operation
   *   GPR[rt] <- GPR[rs] and zero_extend(immediate)
   * --------------------------------------------------------------------------- *)
  | AndImmediate (dest,src,imm) -> {
      mnemonic   = "andi";
      operands   = [dest; src; imm];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "andi" [dest; src; imm])
    }

  (* ---------------------------------------------------------------------------
   * Format: ORI rt, rs, immediate
   * Description: GPR[rt] <- GPR[rs] or zero_extend(immediate)
   * ---------------------------------------------------------------------------
   * The 16-bit immediate is zero-extended to the left and combined with the 
   * contents of GPR rs in a bitwise logical OR operation. The result is placed 
   * into GPR rt.
   * ---------------------------------------------------------------------------
   * Operation
   *   GPR[rt] <- GPR[rs] or zero_extend(immediate)
   * --------------------------------------------------------------------------- *)
  | OrImmediate (dest,src,imm) -> {
      mnemonic   = "ori";
      operands   = [dest; src; imm];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "ori" [dest; src; imm])
    }

  (* ---------------------------------------------------------------------------
   * Format: XORI rt, rs, immediate
   * Description: GPR[rt] <- GPR[rs] xor zero_extend(immediate)
   * ---------------------------------------------------------------------------
   * The 16-bit immediate is zero-extended to the left and combined with the 
   * contents of GPR rs in a bitwise logical exclusive OR operation. The result 
   * is placed into GPR rt.
   * ---------------------------------------------------------------------------
   * Operation
   *   GPR[rt] <- GPR[rs] xor zero_extend(immediate)
   * --------------------------------------------------------------------------- *)
  | XorImmediate (dest,src,imm) -> {
     mnemonic    = "xori";
     operands    = [dest; src; imm];
     delay_slot  = false;
     ida_asm     = (fun f -> f#ops "xori" [dest; src; imm])
    }

  (* --------------------------------------------------------- I-type: memory *)

  (* ---------------------------------------------------------------------------
   * Format: AUI rt, rs immediate
   * Description: GPR[rt] <- GPR[rs] + sign_extend(immediate << 16)
   * ---------------------------------------------------------------------------
   * The 16 bit immediate is shifted left 16 bits, sign-extended, and added to 
   * the register rs, storing the result in rt. 
   * In Release 6, LUI is an assembly idiom for AUI with rs=0.
   * ---------------------------------------------------------------------------
   * Operation
   *   GPR[rt] <- GPR[rs] + sign_extend(immediate << 16)
   * --------------------------------------------------------------------------- *)
  | AddUpperImmediate (dest, src, imm) -> {
      mnemonic   = "aui" ;
      operands   = [dest; src; imm];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "aui" [dest; src; imm])
    }

  (* ---------------------------------------------------------------------------
   * Format: LUI rt, immediate
   * Description: GPR[rt] <- immediate || 0[16]
   * ---------------------------------------------------------------------------
   * The 16-bit immediate is shifted left 16 bits and concatenated with 16 bits 
   * of low-order zeros. The 32-bit result is placed into GPR rt.
   * ---------------------------------------------------------------------------
   * Operation
   *   GPR[rt] <- immediate || 0[16]
   * ---------------------------------------------------------------------------
   * Programming Notes:
   *   In Release 6, LUI is an assembly idiom of AUI with rs=0.
   * --------------------------------------------------------------------------- *)
  | LoadUpperImmediate (dest,imm) -> {
      mnemonic   = "lui";
      operands   = [dest; imm];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "lui" [dest; imm])
    }

  (* ---------------------------------------------------------------------------
   * Format: LB rt, offset(base)
   * Description: GPR[rt]   memory[GPR[base] + offset]
   * ---------------------------------------------------------------------------
   * The contents of the 8-bit byte at the memory location specified by the
   * effective address are fetched, sign-extended, and placed in GPR rt. The 
   * 16-bit signed offset is added to the contents of GPR base to form the 
   * effective address.
   * ---------------------------------------------------------------------------
   * Operation
   *   vAddr <- sign_extend(offset) + GPR[base]
   *   memword <- LoadMemory (vAddr)
   *   byte <- vAddr[1..0] xor BigEndianCPU[2]
   *   GPR[rt] <- sign_extend(memword[7+8*byte..8*byte])
   * --------------------------------------------------------------------------- *)
   | LoadByte (dest,src) -> {
      mnemonic   = "lb";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "lb" [dest; src])
     }

  (* ---------------------------------------------------------------------------
   * Format: LH rt, offset(base)
   * Description: GPR[rt] <- memory[GPR[base] + offset]
   * ---------------------------------------------------------------------------
   * The contents of the 16-bit halfword at the memory location specified by the 
   * aligned effective address are fetched, sign-extended, and placed in GPR rt. 
   * The 16-bit signed offset is added to the contents of GPR base to form the 
   * effective address.
   * ---------------------------------------------------------------------------
   * Operation
   *   vAddr <- sign_extend(offset) + GPR[base]
   *   memword <- LoadMemory (vAddr)
   *   byte <- vAddr[1..0] xor BigEndianCPU[2]
   *   GPR[rt] <- sign_extend(memword[15+8*byte..8*byte])
   * --------------------------------------------------------------------------- *)
  | LoadHalfWord (dest,src) -> {
      mnemonic   = "lh";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "lh" [dest; src])
    }

  | LoadWordLeft (dest,src) -> {
      mnemonic   = "lwl";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    =  (fun f -> f#ops "lwl" [dest; src])
    }
  (* ------------------------------------------------------------------------
   * Format: LW rt, offset(base)
   * Description: GPR[rt] <- memory[GPR[base] + offset]
   * ------------------------------------------------------------------------
   * The contents of the 32-bit word at the memory location specified by the 
   * aligned effective address are fetched, sign-extended to the GPR register 
   * length if necessary, and placed in GPR rt. The 16-bit signed offset is 
   * added to the contents of GPR base to form the effective address.
   * ------------------------------------------------------------------------ *)
  | LoadWord (dest,src) -> {
      mnemonic   = "lw";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "lw" [dest; src])
    }
  (* ------------------------------------------------------------------------
   * Format: LL rt, offset(base)
   * Description: GPR[rt] <- memory[GPR[base] + offset]
   * ------------------------------------------------------------------------
   * Purpose: To load a word from memory for an atomic read-modify-write
   * The LL and SC instructions provide the primitives to implement atomic 
   * read-modify-write (RMW) operations for synchronizable memory locations.
   *
   * The contents of the 32-bit word at the memory location specified by the 
   * aligned effective address are fetched and written into GPR rt. The signed 
   * offset is added to the contents of GPR base to form an effective address.
   *
   * This begins a RMW sequence on the current processor. There can be only one 
   * active RMW sequence per processor. When an LL is executed it starts an 
   * active RMW sequence replacing any other sequence that was active. The RMW 
   * sequence is completed by a subsequent SC instruction that either completes
   * the RMW sequence atomically and succeeds, or does not and fails.
   *
   * Executing LL on one processor does not cause an action that, by itself, 
   * causes an SC for the same block to fail on another processor.
   *
   * An execution of LL does not have to be followed by execution of SC; a program 
   * is free to abandon the RMW sequence without attempting a write.
   * ------------------------------------------------------------------------ *)
  | LoadLinkedWord (dest,src) -> {
      mnemonic = "ll";
      operands = [dest; src];
      delay_slot = false;
      ida_asm =  (fun f -> f#ops "ll" [dest; src])
    }
  | LoadByteUnsigned (dest,src) -> {
      mnemonic   = "lbu";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "lbu"  [dest; src])
    }
  | LoadHalfWordUnsigned (dest,src) -> {
      mnemonic   = "lhu";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "lhu" [dest; src])
    }
  | LoadWordRight (dest,src) -> {
      mnemonic   = "lwr";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "lwr" [dest; src])
    }

  (* ------------------------------------------------------------------------
   * Format: SB rt, offset(base)
   * Description: memory[GPR[base] + offset] <- GPR[rt]
   * ------------------------------------------------------------------------
   * The least-significant 8-bit byte of GPR rt is stored in memory at the 
   * location specified by the effective address. The 16-bit signed offset 
   * is added to the contents of GPR base to form the effective address.
   * ------------------------------------------------------------------------ *)
  | StoreByte (dest,src) -> {
      mnemonic   = "sb";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "sb" [src; dest])
    }
  | StoreHalfWord (dest,src) ->  {
      mnemonic   = "sh";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "sh"  [src; dest])
    }
  | StoreWordLeft (dest,src) -> {
      mnemonic   = "swl";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "swl" [src; dest])
    }
  | StoreWordRight (dest,src) -> {
      mnemonic   = "swr";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "swr" [src; dest])
    }
  | StoreWord (dest,src) -> {
      mnemonic   = "sw";
      operands   = [dest; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "sw" [src; dest])
    }
  (* ------------------------------------------------------------------------
   * Format: SC rt, offset(base)
   * Description: if atomic_update then memory[GPR[base] + offset] <- GPR[rt], 
   *              GPR[rt] <- 1 else GPR[rt] <- 0
   * ------------------------------------------------------------------------
   * The LL and SC instructions provide primitives to implement atomic 
   * read-modify-write (RMW) operations on synchronizable memory locations.
   * In Release 5, the behavior of SC is modified when Config5LLB=1.
   *
   * The 32-bit word in GPR rt is conditionally stored in memory at the location 
   * specified by the aligned effective address. The signed offset is added to 
   * the contents of GPR base to form an effective address.
   *
   * The SC completes the RMW sequence begun by the preceding LL instruction 
   * executed on the processor. To complete the RMW sequence atomically, the 
   * following occur:
   * - The 32-bit word of GPR rt is stored to memory at the location specified 
   *   by the aligned effective address.
   * - A one, indicating success, is written into GPR rt.
   * Otherwise, memory is not modified and a 0, indicating failure, is written 
   * into GPR rt.
   * ------------------------------------------------------------------------ *)
  | StoreConditionalWord (dest, src) -> {
      mnemonic = "sc";
      operands = [dest; src];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "sc" [src; dest])
    }
  (* ------------------------------------------------------------------------
   * Format: LWC1 ft, offset(base)
   * Description: FPR[ft] <- memory[GPR[base] + offset]
   * ------------------------------------------------------------------------
   * The contents of the 32-bit word at the memory location specified by the 
   * aligned effective address are fetched and placed into the low word of 
   * FPR ft. If FPRs are 64 bits wide, bits 63..32 of FPR ft become 
   * UNPREDICTABLE. The 16-bit signed offset is added to the contents of GPR
   * base to form the effective address.
   * ------------------------------------------------------------------------ *)
  | LoadWordFP (dest, src) -> {
      mnemonic = "lwc1";
      operands = [dest; src];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "lwc1" [dest; src])
    }
  | LoadDoublewordToFP (dest, src) -> {
      mnemonic = "ldc1";
      operands = [dest; src];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "ldc1" [dest; src])
    }
  (* ------------------------------------------------------------------------
   * Format: SWC1 ft, offset(base)
   * Description: memory[GPR[base] + offset] <- FPR[ft]
   * ------------------------------------------------------------------------
   * The low 32-bit word from FPR ft is stored in memory at the location 
   * specified by the aligned effective address. The 16-bit signed offset is 
   * added to the contents of GPR base to form the effective address.
   * ------------------------------------------------------------------------ *)
  | StoreWordFromFP (dest, src) -> {
      mnemonic = "swc1";
      operands = [dest; src];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "swc1" [src; dest])
    }
  | StoreDoublewordFromFP (dest, src) -> {
      mnemonic = "sdc1";
      operands = [dest; src];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "sdc1" [src; dest])
    }

  (* ------------------------------------------------------------------------
   * Format: MFC2 rt, Impl, sel
   * Description: GPR[rt] <- CP2CPR[Impl]
   * ------------------------------------------------------------------------
   * The contents of the coprocessor 2 register denoted by the Impl field
   * are placed into general register rt. The interpretation of Impl is not
   * specified by the architecture
   * ------------------------------------------------------------------------
   * Operation
   *   data <- CP2CPR[Impl]
   *   GPR[rt] <- data
   * ------------------------------------------------------------------------ *)
  | MoveWordFromCoprocessor2 (rt, impl, sel) -> {
      mnemonic = "mfc2";
      operands = [rt];
      delay_slot = false;
      ida_asm = (fun f -> f#int_ops "mfc2" [rt] [impl; sel])
    }

  (* ------------------------------------------------------------------------
   * Format: MTC2 rt, Impl, sel
   * Description: CP2CPR[Impl] <- GPR[rt]
   * ------------------------------------------------------------------------
   * The low word in GPR rt is placed into the low word of a Coprocessor 2
   * general register denoted by the Impl field. The interpretation of the
   * Impl field is not specified by the architecture
   * ------------------------------------------------------------------------
   * Operation
   *   data <- GPR[rt]
   *   CP2CPR[Impl] <- data
   * ------------------------------------------------------------------------ *)
  | MoveWordToCoprocessor2 (rt, impl, sel) -> {
      mnemonic = "mtc2";
      operands = [rt];
      delay_slot = false;
      ida_asm = (fun f -> f#int_ops "mtc2" [rt] [impl; sel])
    }

  (* ------------------------------------------------------------------------
   * Format: MFHC2 rt, Impl, sel
   * Description: GPR[rt] <- CP2CPR[Impl](63..32)
   * ------------------------------------------------------------------------
   * The contents of high word of the coprocessor 2 register denoted by the
   * Impl field are placed into general register rt. The interpretation of
   * Impl is not specified by the architecture
   * ------------------------------------------------------------------------
   * Operation
   *   data <- CP2CPR[Impl](63..32)
   *   GPR[rt] <- data
   * ------------------------------------------------------------------------ *)
  | MoveWordFromHighHalfCoprocessor2 (rt, impl, sel) -> {
      mnemonic = "mfhc2";
      operands = [rt];
      delay_slot = false;
      ida_asm = (fun f -> f#int_ops "mfhc2" [rt] [impl; sel])
    }

  (* ------------------------------------------------------------------------
   * Format: PREF hint,offset(base)
   * Description: prefetch_memory(GPR[base] + offset)
   * ------------------------------------------------------------------------
   * PREF adds the 16-bit offset to the contents of GPR base to form an
   * effective byte address. The hint field supplies information about the
   * way that the data is expected to be used
   * ------------------------------------------------------------------------
   * Operation
   *   vAddr <- GPR[base] + sign_extend(offset)
   *   (pAddr, CCA) <- AddressTranslation(vAddr, DATA, LOAD)
   *   Prefetch(CCA, pAddr, vAddr, DATA, hint)
   * ------------------------------------------------------------------------ *)
  | Prefetch (op, hint) -> {
      mnemonic = "pref";
      operands = [op];
      delay_slot = false;
      ida_asm = (fun f -> f#pre_int_ops "pref" [hint] [op])
    }

  (* ----------------------------------------------------------------- J-type *)

  (* ------------------------------------------------------------------------
   * Format: J target
   * Description: To branch within the current 256 MB-aligned region.
   * ------------------------------------------------------------------------
   * This is a PC-region branch (not PC-relative); the effective target 
   * address is in the "current" 256 MB-aligned region. The low 28 bits of 
   * the target address is the instr_index field shifted left 2bits. The 
   * remaining upper bits are the corre- sponding bits of the address of 
   * the instruction in the delay slot (not the branch itself).
   * Jump to the effective target address. Execute the instruction that 
   * follows the jump, in the branch delay slot, before executing the jump 
   * itself.
   * ------------------------------------------------------------------------
   * Operation
   *   I
   *   I+1: I+1: PC <- PC[GPRLEN-1..28] || instr_index || 00
   * ------------------------------------------------------------------------ *)
  | Jump target -> {
      mnemonic = "j";
      operands = [target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "j" [target])
    }
  | JumpLink target -> {
      mnemonic   = "jal";
      operands   = [target];
      delay_slot = true;
      ida_asm    = (fun f -> f#ops "jal" [target])
    }
  (* --------------------------------------------------------- R-type: binary *)
  | ShiftLeftLogical (dest, src, samt) -> {
      mnemonic = "sll";
      operands = [dest; src; samt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "sll" [dest; src; samt])
    }
  | ShiftRightLogical (dest, src, samt) -> {
      mnemonic = "srl";
      operands = [dest; src; samt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "srl" [dest; src; samt])
    }
  | ShiftRightArithmetic (dest, src, samt) -> {
      mnemonic = "sra";
      operands = [dest; src; samt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "sra" [dest; src; samt])
    }
  (* ---------------------------------------------------------------------------
   * Format: SLLV rd, rt, rs
   * Description: GPR[rd] <-  GPR[rt] << GPR[rs]
   * ---------------------------------------------------------------------------
   * The contents of the low-order 32-bit word of GPR rt are shifted left, 
   * inserting zeros into the emptied bits. The resulting word is placed in GPR 
   * rd. The bit-shift amount is specified by the low-order 5 bits of GPR rs.
   * ---------------------------------------------------------------------------
   * Operation
   *   s <- GPR[rs][4..0] 
   *   temp <- GPR[rt][(31-s)..0] || 0[s] 
   *   GPR[rd] <- temp
   * --------------------------------------------------------------------------- *)
  | ShiftLeftLogicalVariable (rd, rt, rs) -> {
      mnemonic = "sllv";
      operands = [rd; rt; rs];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "sllv" [rd; rt; rs])
    }
  | ShiftRightLogicalVariable (rd, rt, rs) -> {
      mnemonic = "srlv";
      operands = [rd; rt; rs];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "srlv" [rd; rt; rs])
    }
  | ShiftRightArithmeticVariable (rd, rt, rs) -> {
      mnemonic = "srav";
      operands = [rd; rt; rs];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "srav" [rd; rt; rs])
    }
  | JumpRegister target -> {
      mnemonic = "jr";
      operands = [target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "jr" [target])
    }
  | JumpLinkRegister (returnaddr, target) -> {
      mnemonic = "jalr";
      operands = [returnaddr; target];
      delay_slot = true;
      ida_asm = (fun f -> f#ops "jalr" [returnaddr; target])
    }

  (* ---------------------------------------------------------------------------
   * Format: MFHI rd
   * Description: GPR[rd] <- HI
   * ---------------------------------------------------------------------------
   * The contents of special register HI are loaded into GPR rd.
   * ---------------------------------------------------------------------------
   * Operation
   *   GPR[rd] <- HI
   * --------------------------------------------------------------------------- *)
  | MoveFromHi (rd, hi) -> {
      mnemonic = "mfhi";
      operands = [rd; hi];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "mfhi" [rd])
    }

  (* ---------------------------------------------------------------------------
   * Format: MTHI rs
   * Description: HI <- GPR[rs]
   * ---------------------------------------------------------------------------
   * The contents of GPR rs are loaded into special register HI.
   * ---------------------------------------------------------------------------
   * Restrictions:
   * If an MTHI instruction is executed following one of these arithmetic 
   * instructions, but before an MFLO or MFHI instruction, the contents of LO 
   * are UNPREDICTABLE.
   * ---------------------------------------------------------------------------
   * Operation
   *   HI <- GPR[rs]
   * --------------------------------------------------------------------------- *)
  | MoveToHi (hi, rs) -> {
      mnemonic = "mthi";
      operands = [hi; rs];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "mthi" [rs])
    }
  | MoveFromLo (rd, lo) -> {
      mnemonic = "mflo";
      operands = [rd; lo];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "mflo" [rd])
    }
  | MoveToLo (lo, rs) -> {
      mnemonic = "mtlo";
      operands = [lo; rs];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "mtlo" [rs])
    }

  (* ---------------------------------------------------------------------------
   * Format: MOVN rd,rs,rt
   * Description: if GPR[rt] != 0 then GPR[rd] <- GPR[rs]
   * ---------------------------------------------------------------------------
   * If the value in GPR rt is not equal to zero, then the contents of GPR rs 
   * are placed into GPR rd.
   * --------------------------------------------------------------------------- *)
  | MoveConditionalNotZero (rd, rs, rt) -> {
      mnemonic = "movn";
      operands = [rd; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "movn" [rd; rs; rt])
    }

  (* ---------------------------------------------------------------------------
   * Format: MOVZ rd,rs,rt
   * Description: if GPR[rt] = 0 then GPR[rd] <- GPR[rs]
   * ---------------------------------------------------------------------------
   * If the value in GPR rt is equal to zero, then the contents of GPR rs 
   * are placed into GPR rd.
   * --------------------------------------------------------------------------- *)
  | MoveConditionalZero (rd, rs, rt) -> {
      mnemonic = "movz";
      operands = [rd; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "movz" [rd; rs; rt])
    }

  (* ---------------------------------------------------------------------------
   * Format: CLZ rd, rs
   * Description: GPR[rd] <- count_leading_zeros GPR[rs]
   * ---------------------------------------------------------------------------
   * Count the number of leading zeros in a word.
   * --------------------------------------------------------------------------- *)
  | CountLeadingZeros (rd, rs) -> {
      mnemonic = "clz";
      operands = [rd; rs];
      delay_slot = false;
      ida_asm = (fun f  -> f#ops "clz" [rd; rs])
    }

  (* ---------------------------------------------------------------------------
   * Format: MULT rs, rt
   * Description: (HI, LO) <- GPR[rs] x GPR[rt]
   * ---------------------------------------------------------------------------
   * The 32-bit word value in GPR rt is multiplied by the 32-bit value in GPR rs, 
   * treating both operands as signed values, to produce a 64-bit result. The 
   * low-order 32-bit word of the result is placed into special register LO, and 
   * the high- order 32-bit word is placed into special register HI.
   * No arithmetic exception occurs under any circumstances.
   * ---------------------------------------------------------------------------
   * Operation
   *   prod <- GPR[rs][31..0] x GPR[rt][31..0]
   *   LO <- prod[31..0]
   *   HI <- prod[63..32]
   * --------------------------------------------------------------------------- *)
  | MultiplyWord (hi, lo, rs, rt) -> {
      mnemonic = "mult";
      operands = [hi; lo; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "mult" [rs; rt])
    }
  (* ---------------------------------------------------------------------------
   * Format: MADD rs, rt
   * Description: (HI, LO) <- (HI, LO) + GPR[rs] x GPR[rt]
   * ---------------------------------------------------------------------------
   * The 32-bit word value in GPR rs is multiplied by the 32-bit word value in 
   * GPR rt, treating both operands as signed values, to produce a 64-bit result.
   * The product is added to the 64-bit concatenated values of HI and LO. The 
   * most sig- nificant 32 bits of the result are written into HI and the least 
   * significant 32 bits are written into LO. No arithmetic exception occurs 
   * under any circumstances.
   * ---------------------------------------------------------------------------
   * Operation
   *   temp <- (HI || LO) + (GPR[rs] x GPR[rt]) 
   * HI <- temp[63..32]
   * LO <- temp[31..0]
   * --------------------------------------------------------------------------- *)
  | MultiplyAddWord (hi, lo, rs, rt) -> {
      mnemonic = "madd";
      operands = [hi; lo; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "madd" [rs; rt])
    }

  (* ---------------------------------------------------------------------------
   * Format: MADDU rs, rt
   * Description: (HI, LO) <- (HI, LO) + GPR[rs] x GPR[rt]
   * ---------------------------------------------------------------------------
   * The 32-bit word value in GPR rs is multiplied by the 32-bit word value in
   * GPR rt, treating both operands as unsigned values, to produce a 64-bit result.
   * The product is added to the 64-bit concatenated values of HI and LO. The
   * most sig- nificant 32 bits of the result are written into HI and the least
   * significant 32 bits are written into LO. No arithmetic exception occurs
   * under any circumstances.
   * ---------------------------------------------------------------------------
   * Operation
   *   temp <- (HI || LO) + (GPR[rs] x GPR[rt])
   * HI <- temp[63..32]
   * LO <- temp[31..0]
   * --------------------------------------------------------------------------- *)
  | MultiplyAddUnsignedWord (hi, lo, rs, rt) -> {
      mnemonic = "maddu";
      operands = [hi; lo; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "maddu" [rs; rt])
    } 

  (* ---------------------------------------------------------------------------
   * Format: MULTU rs, rt
   * Description: (HI, LO) <- GPR[rs] x GPR[rt]
   * ---------------------------------------------------------------------------
   * The 32-bit word value in GPR rt is multiplied by the 32-bit value in GPR rs, 
   * treating both operands as unsigned val- ues, to produce a 64-bit result. The 
   * low-order 32-bit word of the result is placed into special register LO, and 
   * the high- order 32-bit word is placed into special register HI.
   * No arithmetic exception occurs under any circumstances.
   * ---------------------------------------------------------------------------
   * Operation
   *   prod <- (0 || GPR[rs][31..0]) x (0 || GPR[rt][31..0])
   *   LO <- prod[31..0]
   *   HI <- prod[63..32]
   * --------------------------------------------------------------------------- *)
  | MultiplyUnsignedWord (hi, lo, rs, rt) -> {
      mnemonic = "multu";
      operands = [hi; lo; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "multu" [rs; rt])
    }

  (* ---------------------------------------------------------------------------
   * Format: DIV rs, rt
   * Description: (HI, LO) <- GPR[rs] / GPR[rt]
   * ---------------------------------------------------------------------------
   * The 32-bit word value in GPR rs is divided by the 32-bit value in GPR rt, 
   * treating both operands as signed values. The 32-bit quotient is placed into 
   * special register LO and the 32-bit remainder isplaced into special register 
   * HI. No arithmetic exception occurs under any circumstances.
   * ---------------------------------------------------------------------------
   * Operation
   *   q <- GPR[rs][31..0] div GPR[rt][31..0]
   *   LO <- q
   *   r <- GPR[rs][31..0] mod GPR[rt][31..0]
   *   HI <- r
   * --------------------------------------------------------------------------- *)
  | DivideWord (hi, lo, rs, rt) -> {
      mnemonic = "div";
      operands = [hi; lo; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "div" [rs; rt])
    }
  | DivideUnsignedWord (hi, lo, rs, rt) -> {
      mnemonic = "divu";
      operands = [hi; lo; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "divu" [rs; rt])
    }
  | Add (dest, src1, src2) -> {
      mnemonic = "add";
      operands = [dest; src1; src2];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "add" [dest; src1; src2])
    }
  | AddUnsigned (dest, src1, src2) -> {
      mnemonic = "addu";
      operands = [dest; src1; src2];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "addu" [dest; src1; src2])
    }
  | Subtract (dest, src1, src2) -> {
      mnemonic = "sub";
      operands = [dest; src1; src2];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "sub" [dest; src1; src2])
    }
  | SubtractUnsigned (dest, src1, src2) -> {
      mnemonic = "subu";
      operands = [dest; src1; src2];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "subu" [dest; src1; src2])
    }
  | And (dest, src1, src2) -> {
      mnemonic = "and";
      operands = [dest; src1; src2];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "and" [dest; src1; src2])
    }
  | Or (dest, src1, src2) -> {
      mnemonic = "or";
      operands = [dest; src1; src2];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "or" [dest; src1; src2])
    }
  | Xor (dest, src1, src2) -> {
      mnemonic = "xor";
      operands = [dest; src1; src2];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "xor" [dest; src1; src2])
    }
  (* ---------------------------------------------------------------------------
   * Format: NOR rd, rs, rt
   * Description: GPR[rd] <- GPR[rs] nor GPR[rt]
   * ---------------------------------------------------------------------------
   * The contents of GPR rs are combined with the contents of GPR rt in a bitwise 
   * logical NOR operation. The result is placed into GPR rd.
   * ---------------------------------------------------------------------------
   * Operation
   *   GPR[rd] <- GPR[rs] nor GPR[rt]
   * --------------------------------------------------------------------------- *)
  | Nor (rd, rs, rt) -> {
      mnemonic = "nor";
      operands = [rd; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "nor" [rd; rs; rt])
    }
  (* ---------------------------------------------------------------------------
   * Format: SLT rd, rs, rt
   * Description: GPR[rd] <- (GPR[rs] < GPR[rt])
   * ---------------------------------------------------------------------------
   * Compare the contents of GPR rs and GPR rt as signed integers; record the 
   * Boolean result of the comparison in GPR rd. If GPR rs is less than GPR rt, 
   * the result is 1 (true); otherwise, it is 0 (false). 
   * The arithmetic comparison does not cause an Integer Overflow exception.
   * ---------------------------------------------------------------------------
   * Operation
   *  if GPR[rs] < GPR[rt] then
   *      GPR[rt] <- 1
   *  else
   *      GPR[rt] <- 0
   * --------------------------------------------------------------------------- *)       
  | SetLT (rd, rs, rt) -> {
      mnemonic = "slt";
      operands = [rd; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "slt" [rd; rs; rt])
    }

  (* ---------------------------------------------------------------------------
   * Format: SLTU rd, rs, rt
   * Description: GPR[rd] <- (GPR[rs] < GPR[rt])
   * ---------------------------------------------------------------------------
   * Compare the contents of GPR rs and GPR rt as unsigned integers; record the 
   * Boolean result of the comparison in GPR rd. If GPR rs is less than GPR rt, 
   * the result is 1 (true); otherwise, it is 0 (false). 
   * The arithmetic comparison does not cause an Integer Overflow exception.
   * ---------------------------------------------------------------------------
   * Operation
   *  if if (0 || GPR[rs]) < (0 || GPR[rt]) then
   *      GPR[rt] <- 1
   *  else
   *      GPR[rt] <- 0
   * --------------------------------------------------------------------------- *)       
  | SetLTUnsigned (rd, rs, rt) -> {
      mnemonic = "sltu";
      operands = [rd; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "sltu" [rd; rs; rt])
    }

  | Break _code ->
     { mnemonic   = "break";
       operands   = [];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops "break" [])
     }

  | Sync stype ->
     let m = "sync" ^ (if stype = 0 then "" else " " ^ (string_of_int stype)) in
     { mnemonic   = m;
       operands   = [];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops m [])
     }

  (* ---------------------------------------------------------------------------
   * Format: SYSCALL
   * ---------------------------------------------------------------------------
   * A system call exception occurs, immediately and unconditionally transferring
   * control to the exception handler. The code field is available for use as
   * software parameters, but is retrieved by the exception handler only by
   * loading the contents of the memory word containing the instructions.
   * ---------------------------------------------------------------------------
   * Operation
   *    SignalException(SystemCall)
   * --------------------------------------------------------------------------- *)
  | Syscall code ->
     let m = "syscall " ^ (string_of_int code) in
     { mnemonic   = m;
       operands   = [];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops m [])
     }

  (* ---------------------------------------------------------------------------
   * Format: TEQ rs, rt
   * Description: if GPR[rs] = GPR[rt] then Trap
   * ---------------------------------------------------------------------------
   * Compare the contents of GPR rs and GPR rt as signed integers. If GPR rs is 
   * equal to GPR rt, then take a Trap exception.
   * The contents of the code field are ignored by hardware and may be used to 
   * encode information for system software. To retrieve the information, system 
   * software may load the instruction word from memory. Alternatively, if CP0 
   * BadInstr is implemented, the code field may be obtained from BadInstr.
   * ---------------------------------------------------------------------------
   * Operation
   *   if GPR[rs] = GPR[rt] then
   *      SignalException(Trap)
   * --------------------------------------------------------------------------- *)
  | TrapIfEqual (_code, rs, rt) -> {
      mnemonic = "teq";
      operands = [rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "teq" [rs; rt])
    }

  (* ---------------------------------------------------------------------------
   * Format: TEQI rs, immediate
   * Description: if GPR[rs] = immediate then Trap
   * ---------------------------------------------------------------------------
   * Compare the contents of GPR rs and the 16-bit signed immediate as signed
   * integers; if GPR rs is equal to immediate then take a Trap exception.
   * ---------------------------------------------------------------------------
   * Operation
   *   if GPR[rs] = sign_extend(immediate) then
   *      SignalException(Trap)
   * --------------------------------------------------------------------------- *)
  | TrapIfEqualImmediate (rs, imm) -> {
      mnemonic = "teqi";
      operands = [rs; imm];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "teqi" [rs; imm])
    }

  (* ------------------------------------------------------------ R2Type  --- *)

  (* ---------------------------------------------------------------------------
   * Format: MUL rd, rs, rt
   * Description: GPR[rd] <- GPR[rs] x GPR[rt]
   * ---------------------------------------------------------------------------
   * The 32-bit word value in GPR rs is multiplied by the 32-bit value in GPR rt, 
   * treating both operands as signed values, to produce a 64-bit result. The least 
   * significant 32 bits of the product are written to GPR rd. The contents of HI 
   * and LO are UNPREDICTABLE after the operation. No arithmetic exception occurs 
   * under any circumstances.
   * ---------------------------------------------------------------------------
   * Operation
   *   temp <- GPR[rs] x GPR[rt]
   *   GPR[rd] <- temp[31..0]
   *   HI <- UNPREDICTABLE
   *   HI <- UNPREDICTABLE
   * --------------------------------------------------------------------------- *)
  | MultiplyWordToGPR (rd, rs, rt) -> {
      mnemonic = "mul";
      operands = [rd; rs; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "mul" [rd; rs; rt])
    }

  (* ------------------------------------------------------------ R3Type  --- *)

  (* ------------------------------------------------------------------------
   * Format: EXT rt, rs, pos, size
   * Description: GPR[rt] <- ExtractField(GPR[rs], msbd, lsb)
   * Purpose: To extract a bit field from rs and store it right-justified
   *  into rt
   * ------------------------------------------------------------------------
   * The bit field starting at bit pos and extending for size bits is
   * extracted from rs and stored zero-extended and right-justified in rt.
   * The assembly language arguments pos and size are converted by the
   * assembler to the instruction fields msbd (the most significant bit
   * of the destination field in rt), in instruction bits 15..11, and
   * lsb (least significant bit of the source field in rs), in instruction
   * bits 10..6 as follows:
   *    msbd <- size-1
   *   lsb <- pos
   * The values of pos and size must satisfy all of the following relations:
   *   0 <= pos < 32
   *   0 < size <= 32
   *   0 < pos+size <= 32
   * ------------------------------------------------------------------------
   * Operation
   *   if (lsb + msbd) > 31 then
   *     unpredictable
   *   endif
   *   temp <- 0[32-(msbd+1)] || GPR[rs][msbd+lsb..lsb]
   *   GPR[rt] <- temp
   * ------------------------------------------------------------------------ *)
  | ExtractBitField (dst, src, _pos, _size) -> {
      mnemonic = "ext";
      operands = [dst; src];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "ext" [dst; src])
    }

  (* ------------------------------------------------------------------------
   * Format: INS rt, rs, pos, size
   * Description: GPR[rt] <- InsertField(GPR[rs], msb, lsb)
   * Purpose: To merge a right-justified bit field from GPR rs into a
   *   specified field in GPR rt
   * ------------------------------------------------------------------------
   * The right-most size bits from GPR rs are merged into the value from
   * GPR rt starting a bit position pos. The result is placed back in GPR rt.
   * The assembly language arguments pos and size are converted by the
   * assembler to the instruction fields msb (the most significant bit of the
   * field), in instruction bits 15..11, and lsb (least significant bit of
   * the field), in instruction bits 10..6 as follows:
   *   msb <- pos+size-1
   *   lsb <- pos
   * The values of pos and size must satisfy all of the following relations:
   *   0 <= pos < 32
   *   0 < size <= 32
   *   0 < pos+size <= 32
   * ------------------------------------------------------------------------
   * Operation
   *   if (lsb > msb) then
   *     unpredictable
   *   endif
   *   GPR[rt] <- 0[31-(msb+1)] || GPR[rs][msb-lsb..0] || GPR[rt][lsb-1..0]
   * ------------------------------------------------------------------------ *)
  | InsertBitField (dst, src, _pos, _size) -> {
      mnemonic = "ins";
      operands = [dst; src];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "ins" [dst; src])
    }

  (* ------------------------------------------------------------------------
   * Format: RDHWR rt,rd
   * Description: GPR[rt] <- HWR[rd]
   * -----------------------------------------------------------------------
   * Read Hardware Register: to move the contents of a hardware register
   * to a general-purpose register if that operation is enabled by privileged
   * software
   * -----------------------------------------------------------------------
   * Operation
   *  case rd
   *   0: temp <- EBase_CPUNum
   *   1: temp <- SYNCI_StepSize()
   *   2: temp <- Count
   *   3: temp <- CountResolution
   *  29: temp <- UserLocal
   *  30: temp <- Implementation-Dependent-Value
   *  31: temp <- Implementation-Dependent-Value
   *  otherwise: SignalException(ReservedInstruction)
   *  endcase
   *  GPR[rt] <- temp
   * ----------------------------------------------------------------------- *)
  | ReadHardwareRegister (rt, rd) -> {
      mnemonic = "rdhwr";
      operands = [rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops ("rdhwr-" ^ (string_of_int rd)) [rt])
    }

  (* ------------------------------------------------------------------------
   * Format: SEB rd, rt
   * Description: GPR[rd] <- SignExtend(GPR[rt](7..0))
   * -----------------------------------------------------------------------
   * The least significant byte from rt is sign-extended and store in rd
   * -----------------------------------------------------------------------
   * Operation
   *  GPR[rd] <- sign_extend(GPR[rt](7..0))
   * ----------------------------------------------------------------------- *)
  | SignExtendByte (rd, rt) -> {
      mnemonic = "seb";
      operands = [rd; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "seb" [rd; rt])
    }

  (* ------------------------------------------------------------------------
   * Format: SEH rd, rt
   * Description: GPR[rd] <- SignExtend(GPR[rt](15..0))
   * -----------------------------------------------------------------------
   * The least significant halfword from rt is sign-extended and store in rd
   * -----------------------------------------------------------------------
   * Operation
   *  GPR[rd] <- sign_extend(GPR[rt](15..0))
   * ----------------------------------------------------------------------- *)
  | SignExtendHalfword (rd, rt) -> {
      mnemonic = "seh";
      operands = [rd; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "seh" [rd; rt])
    }

  (* ------------------------------------------------------------------------
   * Format: WSBH rd, rt
   * Description: GPR[rd] <- SwapBytesWithinHalfwords(GPR[rt])
   * -----------------------------------------------------------------------
   * Within each halfword of GPR rt the bytes are swapped and stored in GPR rd
   * -----------------------------------------------------------------------
   * Operation
   *  GPR[rd] <- GPR[r](23..16) || GPR[r](31..24) || GPR[r](7..0) || GPR[r](15..8)
   * ----------------------------------------------------------------------- *)
  | WordSwapBytesHalfwords (rd, rt) -> {
      mnemonic = "wsbh";
      operands = [rd; rt];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "wsbh" [rd; rt])
    }

  (* ----------------------------------------------------------- FPRType  --- *)

  (* ---------------------------------------------------------------------------
   * Format: ADD.S fd, fs, ft
   *         ADD.D fd, fs, ft
   *         ADD.PS fd, fs, ft
   * Description: FPR[fd] <- FPR[fs] + FPR[ft]
   * ---------------------------------------------------------------------------
   * The value in FPR ft is added to the value in FPR fs. The result is 
   * calculated to infinite precision, rounded by using to the current rounding 
   * mode in FCSR, and placed into FPR fd. The operands and result are values 
   * in format fmt. ADD.PS adds the upper and lower halves of FPR fs and FPR ft 
   * independently, and ORs together any generated exceptions.
   * The Cause bits are ORed into the Flag bits if no exception is taken.
   * ---------------------------------------------------------------------------
   * Operation
   *   StoreFPR (fd, fmt, ValueFPR(fs, fmt)  +(fmt) ValueFPR(ft, fmt))
   * --------------------------------------------------------------------------- *)
  | FPAddfmt (fmt,fd,fs,ft) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "add." ^ fmtstr in
     { mnemonic  = mnemonic;
       operands  = [fd; fs; ft];
       delay_slot = false;
       ida_asm   = (fun f -> f#ops mnemonic  [fd; fs; ft])
     }

  | FPSubfmt (fmt,fd,fs,ft) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "sub." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [fd; fs; ft];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [fd; fs; ft])
     }
     
  (* ---------------------------------------------------------------------------
   * Format: MUL.S fd, fs, ft
   *         MUL.D fd, fs, ft
   *         MUL.PS fd, fs, ft
   * Description: FPR[fd] <- FPR[fs] x FPR[ft]
   * ---------------------------------------------------------------------------
   * The value in FPR fs is multiplied by the value in FPR ft. The result is 
   * calculated to infinite precision, rounded accord- ing to the current rounding 
   * mode in FCSR, and placed into FPR fd. The operands and result are values in 
   * format fmt. MUL.PS multiplies the upper and lower halves of FPR fs and FPR 
   * ft independently, and ORs together any generated exceptional conditions.
   * ---------------------------------------------------------------------------
   * Operation
   *   StoreFPR (fd, fmt, ValueFPR(fs, fmt)  x(fmt) ValueFPR(ft, fmt))
   * --------------------------------------------------------------------------- *)
  | FPMulfmt (fmt,fd,fs,ft) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "mul." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [fd; fs; ft];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [fd; fs; ft])
     }
  | FPDivfmt (fmt, dst, src1, src2) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "div." ^ fmtstr in
     { mnemonic = mnemonic;
       operands = [dst; src1; src2];
       delay_slot = false;
       ida_asm = (fun f -> f#ops mnemonic [dst; src1; src2])
     }
  | FPSqrtfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "sqrt." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  (* ---------------------------------------------------------------------------
   * Format: ABS.S fd, fs
   *         ABS.D fd, fs
   *         ABS.PS fd, fs
   * Description: FPR[fd] <- abs(FPR[fs])
   * ---------------------------------------------------------------------------
   * The absolute value of the value in FPR fs is placed in FPR fd. The operand 
   * and result are values in format fmt. ABS.PS takes the absolute value of the 
   * two values in FPR fs independently, and ORs together any generated 
   * exceptions.
   * The Cause bits are ORed into the Flag bits if no exception is taken.
   * ---------------------------------------------------------------------------
   * Operation
   *   StoreFPR(fd, fmt, AbsoluteValue(ValueFPR(fs, fmt)))
   * --------------------------------------------------------------------------- *)
  | FPAbsfmt (fmt,fd,fs) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "abs." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [fd; fs];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [fd; fs])
     }
     
  (* ---------------------------------------------------------------------------
   * Format: MOV.S fd, fs
   *         MOV.D fd, fs
   *         MOV.PS fd, fs
   * Description: FPR[fd] <- FPR[fs]
   * ---------------------------------------------------------------------------
   * The value in FPR fs is placed into FPR fd. The source and destination are 
   * values in format fmt. In paired-single format, both the halves of the pair 
   * are copied to fd.
   * The move is non-arithmetic; it causes no IEEE 754 exceptions, and the 
   * FCSRCause and FCSRFlags fields are not modified.
   * ---------------------------------------------------------------------------
   * Operation
   *   StoreFPR(fd, fmt, ValueFPR(fs, fmt))
   * --------------------------------------------------------------------------- *)
  | FPMovfmt (fmt,fd,fs) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "mov." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [fd; fs];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [fd; fs])
     }
  | FPNegfmt (fmt,dst,src)  ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "neg." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPRoundLfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "round.l." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPTruncLfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "trunc.l." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPCeilLfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "ceil.l."  ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   =  [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPFloorLfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "floor.l." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPRoundWfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "round.w." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }

  | FPTruncWfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "trunc.w." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPCeilWfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "ceil.w." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }

  | FPFloorWfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "floor.w." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPRSqrtfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "rsqrt." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }

  | FPCVTSfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "cvt.s." ^ fmtstr  in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }

  | FPCVTDfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "cvt.d." ^ fmtstr  in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPCVTWfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "cvt.w." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPCVTLfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "cvt.l." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  | FPCVTSPfmt (fmt,dst,src) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let mnemonic = "cvt.sp." ^ fmtstr in
     { mnemonic   = mnemonic;
       operands   = [dst; src];
       delay_slot = false;
       ida_asm    = (fun f -> f#ops mnemonic [dst; src])
     }
  (* ---------------------------------------------------------- FPRIType  --- *)

  (* ---------------------------------------------------------------------------
   * Format: MFC0 rt, rd, sel
   * Description: GPR[rt] <- CPR[0,rd,sel]
   * ---------------------------------------------------------------------------
   * The contents of the coprocessor 0 register specified by the combination of
   * rd and sel are loaded into general register rt.
   * ---------------------------------------------------------------------------
   * Operation
   *   reg <- rd
   *   data <- CPR[0,reg,sel]
   *   GPR[rt] <- data
   * --------------------------------------------------------------------------- *)
  | MoveFromCoprocessor0 (rt, rd, sel) -> {
      mnemonic   = "mfc0";
      operands   = [rt; rd];
      delay_slot = false;
      ida_asm    = (fun f -> f#int_ops "mfc0" [rt; rd] [sel])
    }

  (* ---------------------------------------------------------------------------
   * Format: MTC0 rt, rd, sel
   * Description: CPR[0,rd,sel] <- GPR[rt]
   * ---------------------------------------------------------------------------
   * The contents of general register rt are loaded into the coprocessor 0
   * register specified by the combination of the rd and sel.
   * ---------------------------------------------------------------------------
   * Operation
   *   data <- GPR[rt]
   *   reg <- rd
   *   ??
   * --------------------------------------------------------------------------- *)
  | MoveToCoprocessor0 (rt,rd,sel) -> {
      mnemonic   = "mtc0";
      operands   = [rt; rd];
      delay_slot = false;
      ida_asm    = (fun f -> f#int_ops "mtc0" [rt; rd] [sel])
    }

  (* ---------------------------------------------------------------------------
   * Format: MFHC0 rt, rd, sel
   * Description: GPR[rt] <- CPR[0,rd,sel][63:32]
   * ---------------------------------------------------------------------------
   * The contents of the coprocessor 0 register specified by the combination of
   * rd and sel are loaded into general register rt.
   * ---------------------------------------------------------------------------
   * Operation
   *   reg <- rd
   *   data <- CPR[0,reg,sel]
   *   GPR[rt] <- data(63..32)
   * --------------------------------------------------------------------------- *)
  | MoveFromHighCoprocessor0 (rt, rd, sel) -> {
      mnemonic   = "mfhc0";
      operands   = [rt; rd];
      delay_slot = false;
      ida_asm    = (fun f -> f#int_ops "mfhc0" [rt; rd] [sel])
    }

  (* ---------------------------------------------------------------------------
   * Format: MTHC0 rt, rd, sel
   * Description: CPR[0,rd,sel][63:32] <- GPR[rt]
   * ---------------------------------------------------------------------------
   * The contents of general register rt are loaded into the Coprocessor 0
   * register specified by the combination of rd and sel.
   * ---------------------------------------------------------------------------
   * Operation
   *   data <- GPR[rt]
   *   reg <- rd
   *   CPR[0,reg,sel](63..32) <- data
   * --------------------------------------------------------------------------- *)
  | MoveToHighCoprocessor0 (rt, rd, sel) -> {
      mnemonic   = "mthc0";
      operands   = [rt; rd];
      delay_slot = false;
      ida_asm    = (fun f -> f#int_ops "mthc0" [rt; rd] [sel])
    }

  (* ---------------------------------------------------------------------------
   * Format: MFC1 rt, fs
   * Description: GPR[rt] <- FPR[fs]
   * ---------------------------------------------------------------------------
   * The contents of FPR fs are loaded into general register rt.
   * ---------------------------------------------------------------------------
   * Operation
   *   data <- ValueFPR(fs, UNINTERPRETED_WORD)
   *   GPR[rt] <- data
   * --------------------------------------------------------------------------- *)
  | MoveWordFromFP (rt,fs) -> {
      mnemonic   = "mfc1";
      operands   = [rt; fs];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "mfc1" [rt; fs])
    }

  (* ---------------------------------------------------------------------------
   * Format: MFHC1 rt, fs
   * Description: GPR[rt] <- FPR[fs](63..32)
   * ---------------------------------------------------------------------------
   * The contents of the high word of FPR fs are loaded into general register rt.
   * ---------------------------------------------------------------------------
   * Operation
   *   data <- ValueFPR(fs, UNINTERPRETED_WORD)(63..32)
   *   GPR[rt] <- data
   * --------------------------------------------------------------------------- *)
  | MoveWordFromHighHalfFP (rt,fs) -> {
      mnemonic   = "mfhc1";
      operands   = [rt; fs];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "mfhc1" [rt; fs])
    }

  (* ---------------------------------------------------------------------------
   * Format: MTHC1 rt, fs
   * Description: FPR[fs](63..32) <- GPR[rt]
   * ---------------------------------------------------------------------------
   * The word in GPR rt is placed into the high word of FPR fs.
   * ---------------------------------------------------------------------------
   * Operation
   *   newdata <- GPR[rt]
   *   olddata <- ValueFPR(fs, UNINTERPRETED_DOUBLEWORD)(31..0)
   *   StoreFPR(fs, UNINTERPRETED_DOUBLEWORD, newdata || olddata)
   * --------------------------------------------------------------------------- *)
  | MoveWordToHighHalfFP (rt,fs) -> {
      mnemonic   = "mthc1";
      operands   = [rt; fs];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "mthc1" [rt; fs])
    }

  (* ---------------------------------------------------------------------------
   * Format: MTC1 rt, fs
   * Description: FPR[fs] <- GPR[rt]
   * ---------------------------------------------------------------------------
   * The low word in GPR rt is placed into the low word of FPR fs.
   * ---------------------------------------------------------------------------
   * Operation
   *   data <- GPR[rt][31..0]
   *   StoreFPR(fs, UNINTERPRETED_WORD, data)
   * --------------------------------------------------------------------------- *)
  | MoveWordToFP (rt, fs) -> {
      mnemonic = "mtc1";
      operands = [rt; fs];
      delay_slot = false;
      ida_asm = (fun f -> f#ops "mtc1" [rt; fs])
    }

  (* ---------------------------------------------------------------------------
   * Format: CFC1 rt, fs
   * Description: GPR[rt] <- FP_Control[fs]
   * ---------------------------------------------------------------------------
   * Copy the 32-bit word from FP (coprocessor 1) control register fs into GPR rt.
   * --------------------------------------------------------------------------- *)
  | ControlWordFromFP (rt,fs) -> {
      mnemonic   = "cfc1";
      operands   = [rt; fs];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "cfc1" [rt; fs])
    }
  | ControlWordToFP (src,dst)  -> {
      mnemonic   = "ctc1";
      operands   = [src; dst];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "ctc1"  [src; dst])
    }

  (* -----------------------------------------------------------FPICCType --- *)

  (* ---------------------------------------------------------------------------
   * Format: BC1F offset (cc = 0 implied)
   *         BC1F cc, offset
   * Description: if FPConditionCode(cc) = 0 then branch
   * ---------------------------------------------------------------------------
   * An 18-bit signed offset (the 16-bit offset field shifted left 2 bits) is 
   * added to the address of the instruction following the branch (not the branch 
   * itself) in the branch delay slot to form a PC-relative effective target 
   * address. If the FP con- dition code bit cc is false (0), the program 
   * branches to the effective target address after the instruction in the delay 
   * slot is executed. An FP condition code is set by the FP compare instruction, 
   * C.cond fmt.
   * ---------------------------------------------------------------------------
   * Operation
   *   I  : condition <- FPConditionCode(cc) = 0
   *        target_offset <- sign-extend( offset * 4 )   (adapted)
   *   I+1: if condition then
   *          PC <- PC + target_offset
   *        endif
   * ------------------------------------------------------------------------ *)
  | BranchFPFalse (cc,offset) -> {
      mnemonic    = "bc1f";
      operands    = [offset];
      delay_slot  = true;
      ida_asm     = (fun f -> f#cc_ops "bc1f" cc [offset]);
    }

  | BranchFPTrue (cc,offset) -> {
      mnemonic    = "bc1t";
      operands    = [offset];
      delay_slot  = true;
      ida_asm     = (fun f -> f#cc_ops "bc1t" cc [offset]);
    }

  (* ------------------------------------------------------ FPCompareType --- *)
  | FPCompare (fmt, _cc, pred, _excn, src1, src2) ->
     let fmtstr = mips_fp_format_to_string fmt in
     let predstr = mips_fp_predicate_to_string pred in
     let mnemonic = "c."  ^ predstr ^ "." ^ fmtstr in
     { mnemonic = mnemonic;
       operands = [src1; src2];
       delay_slot = false;
       ida_asm = (fun f -> f#ops mnemonic [src1; src2])
     }

  (* ----------------------------------------------------------- FPCM type ---*)

  | MovF (cc, rd, rs) -> {    (* Move Conditional on Floating Point False *)
      mnemonic = "movf";
      operands = [rd; rs];
      delay_slot = false;
      ida_asm = (fun f -> f#cc_ops "movf" cc [rd; rs])
    }

  | MovT (cc, rd, rs) -> {    (* Move Conditional on Floating Point True *)
      mnemonic = "movt";
      operands = [rd; rs];
      delay_slot = false;
      ida_asm = (fun f -> f#cc_ops "movt" cc [rd; rs])
    }
      
  (* ---------------------------------------------------- Pseudo instructions *)

  | Move (dst,src) -> {
      mnemonic   = "move";
      operands   = [dst; src];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "move" [dst; src])
    }

  | LoadImmediate (dst,imm) -> {
      mnemonic   = "li";
      operands   = [dst; imm];
      delay_slot = false;
      ida_asm    = (fun f -> f#ops "li" [dst; imm])
    }
                                    
  | NoOperation  -> {
      mnemonic   = "nop";
      operands   = [];
      delay_slot = false;
      ida_asm    = (fun f -> f#no_ops "<nop>")
    }
  | Halt -> {
      mnemonic   = "hlt";
      operands   = [];
      delay_slot = true;
      ida_asm    = (fun f -> f#no_ops "<hlt>")
    }
  | OpcodeUnpredictable s -> {
      mnemonic = "UNPREDICTABLE";
      operands = [];
      delay_slot = false;
      ida_asm = (fun f -> f#no_ops ("UNPREDICTABLE: " ^ s))
    }
  | NotRecognized (name, dw) -> {
      mnemonic = "unknown";
      operands = [];
      delay_slot = false;
      ida_asm = (fun f -> f#no_ops ("unknown " ^ name ^ "; " ^ dw#to_hex_string))
    }
  | _  ->  {
      mnemonic   = "generic";
      operands   = [];
      delay_slot = false;
      ida_asm    = (fun f -> f#no_ops "generic")
    }


class string_formatter_t (width:int): [string] opcode_formatter_int =
object (self)
     
  method ops s operands =
    let s = fixed_length_string s width in
    let (_,result) = List.fold_left 
      (fun (isfirst,a) op -> if isfirst 
	then (false,s ^ " " ^ op#toString)
	else
	  (false, a ^ ", " ^ op#toString)) (true,s) operands in
    result

  method cc_ops s cc operands =
    if cc = 0 then
      self#ops s operands
    else
      let s = (fixed_length_string s (width+1)) ^ (string_of_int cc) in
      let ops =
        String.concat "" (List.map (fun op -> ", " ^ op#toString) operands) in
      s ^ ops

  method int_ops s operands intoperands =
    let s = fixed_length_string s width in
    let (_,result) =
      List.fold_left
        (fun (isfirst,a) op ->
          if isfirst then
            (false,s ^ " " ^ op#toString)
          else
            (false,a ^ ", " ^ op#toString)) (true,s) operands in
    List.fold_left
      (fun a op -> a ^ ", " ^ (string_of_int op)) result intoperands

  method pre_int_ops s intoperands operands =
    let s = fixed_length_string s width in
    let (_,result) =
      List.fold_left
        (fun (isfirst,a) i ->
          if isfirst then
            (false,s ^ " " ^ (string_of_int i))
          else
            (false,a ^ ", " ^ (string_of_int i))) (true,s) intoperands in
    List.fold_left
      (fun a op -> a ^ ", " ^ op#toString) result operands

  method no_ops s = s
end


let get_mips_operands (opc:mips_opcode_t) = (get_record opc).operands


let get_mips_opcode_name (opc:mips_opcode_t) = (get_record opc).mnemonic


let mips_opcode_to_string ?(width=8) (opc:mips_opcode_t) =
  let  string_formatter = new string_formatter_t width in
  let default () = (get_record opc).ida_asm string_formatter in
  default ()


let has_delay_slot (opc:mips_opcode_t) = (get_record opc).delay_slot


let get_operands_written (opc:mips_opcode_t) =
  List.filter (fun op -> op#is_write) (get_record opc).operands


let get_operands_read (opc:mips_opcode_t) =
  List.filter (fun op -> op#is_read) (get_record opc).operands

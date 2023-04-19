(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2023  Aarno Labs LLC

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
(** Documentation used:
    
    NXP. Book E: Enhanced PowerPC Architecture. Version 1.0, May 7, 2002

    NXP. EREF: A Programmer's Reference Manual for Freescale Power Architecture
    Processors. Supports e500 core family (e500v1, e500v2, e500mc, e5500,
    e6500) e200 core family. (EREF_RM) Rev.1 (EIS 2.1) 06/2014.

    NXP. Variable Length Encoding (VLE) Programming Environments Manual:
    A Supplement to the EREF (VLEPEM) Rev. 0, 07/2007.

    NXP. Variable-Length Encoding (VLE) Extension Programming Interface
    Manual (VLEPIM) Rev. 1, 2/2006.

    NXP. e200z759n3 Core Reference Manual (e200z759n3) Rev. 2, 1/2015.
 *)
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


type power_instruction_type_t = | PWR | VLE16 | VLE32

(** Special registers

    Condition Register (CR)
    -----------------------
    The Condition Register (CR) is a 32-bit registers with bits numbered
    32 (most-significant) to 63 (least-significant). The Condition Register
    reflects the result of certain operations, and provides a mechanism
    for testing (and branching).
    (BookE, pg 45)

    EREF, 4.5 Registers for Branch Operations, pg 4-40
    bits 32-63:
    <c0><c1><c2><c3><c4><c5><c6><c7>
    CR0 (<c0>) can be set as the implicit result of an integer instruction
    CR1 (<c1>) can be set as the implicit result of a floating point instruction.

    Branch Instruction (BI) Operand Settings for CR Fields (Table 4-13)
    CRn Bits    BI    Description
    ----------------------------------------------------------------------------
    CR0[0]     00000  Negative (LT) -- Set when the result is negative
                      Bit 32 of the result is equal to one
    CR0[1]     00001  Positive (GT) -- Set when the result is positive (and not zero).
                      Bit 32 of the result is equal to zero, and at least one of
                      bits 33-63 of the result is non-zero
    CR0[2]     00010  Zero (EQ) -- Set when the result is zero.
                      Bits 32-63 of the result are equal to zero.
    CR0[3]     00011  Summary overflow (SO). Copy of XER[SO] at the instruction's
                      completion.
    ----------------------------------------------------------------------------

    Count Register (CTR)
    Bits 32:63 can be used to hold a loop count that can be decremented during
    execution of branch instructions that contain an appropriately encoded BO
    field. If the value in bits 32:63 of the Count Register is 0 before being
    decremented, it is -1 afterward and bits 0:31 are left unchanged.
    The entire 64-bit Count Register can also be used to provide the branch
    target address for the Branch Conditional to Count Register instruction.
    (BookE, pg 48)

    Link Register (LR)
    The Link Register can be used to provide the branch target address for the
    Branch Conditional to Link Register instruction, and it holds the return
    address after Branch and Link instructions.
    (BookE, pg 48)

    Machine State Register (MSR)
    The Machine State Register is a 32-bit register, numbered 32 (msb) to 63
    (lsb). This register defines the state of the processor (i.e., enabling
    and disabling of interrupts and debugging exceptions, selection of address
    space for instruction and data storage access, and specifying whether the
    processor is in supervisor or user mode).
    (BookE, pg 39)

    Integer Exception Register (XER)
    The Integer Exception Register is a 64-bit register. Integer Exception
    Register bits are set based on the operation of an instruction considered
    as a whole, not on intermediate results.
    bit 32: Summary Overflow (SO)
    bit 33: Overflow (OV)
    bit 34: Carry (CA)
    (BookE, pg 54)

    Save/Restore Register 0 (SRR0)
    Save/Restore Register 0 (SRR0) is a 64-bit register with bits numbered
    0 (most-significant) to 63 (least-significant). The register is used to
    save machine state on non-critical interrupts, and to restore machine
    state when an rfi is executed. On a non-critical interrupt, SRR0 is set
    to the current or next instruction address. When rfi is executed,
    instruction execution continues at the the address in SRR0.
    (BookE, pg 144)

    Save/Restore Register 1 (SRR1)
    Save/Restore Register 1 (SRR1) is a 32-bit register with bits numbered
    32 (most-significant) through 63 (least-significant). The register is
    used to save machine state on non-critical interrupts, and to restore
    machine state when an rfi is executed. When a non-critical interrupt is
    taken, the contents of the MSR are placed in SRR1. When rfi is executed,
    the contents of SRR1 are placed into MSR.
    (BookE, pg 144)

    Critical Save/Restore Register 0 (CSRR0)
    Critical Save/Restore Register 0 (CSRR0) is a 64-bit register with bits
    numbered 0 (most-significant) through 63 (least-significant). The register
    is used to save machine state on critical interrupts, and to restore
    machine state when an rfci is executed.
    (BookE, pg 144)

    Critical Save/Restore Register 1 (CSRR1)
    Critical Save/Restore Register 1 (CSRR1) is a 32-bit register with bits
    numbered 32 (least-significant) through 63 (most-significant). The register
    is used to save machine state on critical interrupts, and to restore
    machine state when an rfci is executed.
    (BookE, pg 145)

    Data Exception Address Register (DEAR)
    The Data Exception Address Register (DEAR) is a 64-bit register with bits
    numbered 0 (most-significant) through 63 (least-significant). The DEAR
    contains the address that was referenced by a Load, Store, Cache Management
    instruction that caused an Alignment, DATA TLB Miss, or Data Storage
    interrupt.
    (BookE, pg 145)

    References:
    BookE: Book E: Enhanced PowerPC Architecture, Version 1.0, May 7 2002, NXP.
 *)
type power_special_reg_t =
  | PowerCR    (* Condition Register (contain CR0, CR1, CR2) *)
  | PowerCTR   (* Count Register *)
  | PowerMSR   (* Machine Status Register *)
  | PowerLR    (* Link Register *)
  | PowerXER   (* Integer Exception Register *)
  | PowerSRR0  (* Save/Restore Register 0 *)
  | PowerSRR1  (* Save/Restore Register 1 *)
  | PowerCSRR0 (* Critical Save/Restore Register 0 *)
  | PowerCSRR1 (* Critical Save/Restore Register 1 *)
  | PowerDSRR0 (* Debug Save/Restore Register 0 *)
  | PowerDSRR1 (* Debug Save/Restore Register 1 *)
  | PowerMCSRR0 (* Machine Check Save/Restore Register 0 *)
  | PowerMCSRR1 (* Machine Check Save/Restore Register 1 *)


type power_register_field_t =
  | PowerCR0   (* Condition Register, bits 32-35 *)
  | PowerCR1   (* Condition Register, bits 36-39 *)
  | PowerCR2   (* Condition Register, bits 40-43 *)
  | PowerCR3   (* Condition Register, bits 44-47 *)
  | PowerCR4   (* Condition Register, bits 48-51 *)
  | PowerCR5   (* Condition Register, bits 52-55 *)
  | PowerCR6   (* Condition Register, bits 56-59 *)
  | PowerCR7   (* Condition Register, bits 60-63 *)
  | PowerXERSO (* Integer Exception Register, summary overflow *)
  | PowerXEROV (* Integer Exception Register, overflow *)
  | PowerXERCA (* Integer Exception Register, carry *)


type power_operand_kind_t =
  | PowerGPReg of int
  | PowerSpecialReg of power_special_reg_t
  | PowerRegisterField of power_register_field_t
  | PowerConditionRegisterBit of int
  | PowerImmediate of immediate_int
  | PowerAbsolute of doubleword_int
  | PowerIndReg of int * numerical_t  (* GPR base reg index, offset *)
  | PowerIndexedIndReg of int * int  (* GPR base reg index, GPR index reg index *)


(** Operand modes:
    RD: read
    WR: write
    RW: read-write
    NT: not touched
 *)
type power_operand_mode_t = RD | WR | RW | NT


type power_branch_prediction_t = BPNone | BPPlus of int | BPMinus of int


class type power_operand_int =
  object ('a)

    (* accessors *)
    method get_kind: power_operand_kind_t
    method get_mode: power_operand_mode_t
    method get_gp_register: int
    method get_special_register: power_special_reg_t
    method get_register_field: power_register_field_t
    method get_absolute_address: doubleword_int

    (* converters *)
    method to_numerical: numerical_t
    method to_address: floc_int -> xpr_t
    method to_variable: floc_int -> variable_t
    method to_expr: floc_int -> xpr_t
    method to_lhs: floc_int -> variable_t * cmd_t list

    (* predicates *)
    method is_read: bool
    method is_write: bool
    method is_gp_register: bool
    method is_absolute_address: bool
    method is_register_field: bool
    method is_default_cr: bool

    (* printing *)
    method toString: string
    method toPretty: pretty_t

  end

type not_code_t = DataBlock of data_block_int


type power_opcode_t =
  (* EREF:6-12, VLEPEM:3-6 *)
  | Add of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register (CR0) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-17 *)
  | AddCarrying of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register (CR0) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)
      * power_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-18 *)
  | AddExtended of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)
      * power_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-23, VLEPEM:3-7 *)
  | AddImmediate of
      power_instruction_type_t
      * bool               (* s: shifted *)
      * bool               (* op2: 2-operand *)
      * bool               (* op16: 16-bit immediate *)
      * bool               (* rc: record condition *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source operand *)
      * power_operand_int  (* simm: signed immediate *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-24, VLEPEM:3-9 *)
  | AddImmediateCarrying of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source register *)
      * power_operand_int  (* simm: signed immediate *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* ca: carry field (XER-CA) *)

  (* EREF:6-26 *)
  | AddMinusOneExtended of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source register *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* ca: carry (XER-CA) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-31 *)
  | AddZeroExtended of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow exception *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source register *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* ca: carry (XER-CA) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-32, VLEPEM:3-10 *)
  | And of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-33, VLEPEM:3-10 *)
  | AndComplement of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-34,35, VLEPEM:3-10 *)
  | AndImmediate of
      power_instruction_type_t
      * bool               (* s: shifted *)
      * bool               (* op2: 2-operand *)
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* uimm: unsigned immediate *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* VLEPEM:3-14 *)
  | BitClearImmediate of
      power_instruction_type_t
      * power_operand_int  (* rx: dst/src register *)
      * power_operand_int  (* ui5: immediate *)

  (* VLEPEM:3-16 *)
  | BitGenerateImmediate of
      power_instruction_type_t
      * power_operand_int  (* rx: destination register *)
      * power_operand_int  (* ui5: immediate *)

  (* VLEPEM:3-18 *)
  | BitMaskGenerateImmediate of
      power_instruction_type_t
      * power_operand_int  (* rx: destination register *)
      * power_operand_int  (* ui5: immediate *)

  (* VLEPEM:3-19 *)
  | BitSetImmediate of
      power_instruction_type_t
      * power_operand_int  (* rx: destination register *)
      * power_operand_int  (* ui5: immediate *)

  (* VLEPEM:3-20 *)
  | BitTestImmediate of
      power_instruction_type_t
      * power_operand_int  (* rx: source register *)
      * power_operand_int  (* uimm: unsigned immediate *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-36, VLEPEM:3-12 *)
  | Branch of
      power_instruction_type_t
      * power_operand_int  (* tgt: target address *)

  (* EREF:6-37 *)
  | BranchConditional of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations (5 bits) *)
      * int                (* bi: bit in condition register (5 bits)  *)
      * power_operand_int  (* bd: branch destination *)

  (* EREF:6-41 *)
  | BranchConditionalLinkRegister of
      power_instruction_type_t
      * int                (* bo: bracnch operations (5 bits) *)
      * int                (* bi: bit in condition register (5 bits) *)
      * int                (* bh: branch usage hint (2 bits) *)
      * power_operand_int  (* lr: link register (LR) *)

  (* EREF:6-41 *)
  | BranchConditionalLinkRegisterLink of
      power_instruction_type_t
      * int                (* bo: branch operations (5 bits) *)
      * int                (* bi: bit in condition register (5 bits) *)
      * int                (* bh: branch usage hint (2 bits *)
      * power_operand_int  (* lr: link register (LR) *)

  | BranchCountRegister of
      power_instruction_type_t
      * power_operand_int  (* count register (CTR) *)

  | BranchCountRegisterLink of
      power_instruction_type_t
      * power_operand_int  (* count_register (CTR) *)

  (* EREF:6-36, VLEPEM:3-12 *)
  | BranchLink of
      power_instruction_type_t
      * power_operand_int  (* tgt: target address *)
      * power_operand_int  (* lr: link register (LR) *)

  (* EREF:B-13 (simplified), VLEPEM:3-17 *)
  | BranchLinkRegister of
      power_instruction_type_t
      * power_operand_int  (* link register (LR) *)

  (* EREF:B-14 (simplified), VLEPEM:3-17 *)
  | BranchLinkRegisterLink of
      power_instruction_type_t
      * power_operand_int  (* link register (LR) *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchDecrementNotZero of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * power_branch_prediction_t  (* bp: branch prediction *)
      * power_operand_int  (* bd: branch destination *)
      * power_operand_int  (* ctr: count register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchDecrementZero of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * power_branch_prediction_t  (* bp: branch prediction *)
      * power_operand_int  (* bd: branch destination *)
      * power_operand_int  (* ctr: count register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchEqual of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * power_branch_prediction_t  (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchEqualLinkRegister of
      power_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * power_branch_prediction_t (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchGreaterEqual of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * power_branch_prediction_t (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchGreaterEqualLinkRegister of
      power_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * power_branch_prediction_t (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchGreaterThan of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * power_branch_prediction_t (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchGreaterThanLinkRegister of
      power_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * power_branch_prediction_t (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics, VLEPEM:3-13) *)
  | CBranchLessEqual of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * power_branch_prediction_t  (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchLessEqualLinkRegister of
      power_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * power_branch_prediction_t (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchLessThan of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * power_branch_prediction_t  (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchLessThanLinkRegister of
      power_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * power_branch_prediction_t (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchNotEqual of
      power_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * power_branch_prediction_t  (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchNotEqualLinkRegister of
      power_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * power_branch_prediction_t (* bp: branch prediction *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* lr: link register *)

  (* EREF:B-3 (simplified *)
  | ClearLeftShiftLeftWordImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* mb: mask begin *)
      * power_operand_int  (* sh: shift *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* Simplified mnemonic, EREF:B-3, VLEPIM:Table A-23
     Full instruction: RotateLeftWordImmediateAndMask *)
  | ClearLeftWordImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* rA: destination register *)
      * power_operand_int  (* rS: source register *)
      * power_operand_int  (* mb: mask begin *)

  (* Simplified mnemonic, EREF:B-3, VLEPIM:Table A-23
     Full instruction: RotateLeftWordImmediateAndMask *)
  | ClearRightWordImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* me: mask end *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-46, VLEPEM:3-21 *)
  | CompareImmediate of
      power_instruction_type_t
      * bool               (* op16: 16-bit immediate, VLE32 only *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* ra: register operand *)
      * power_operand_int  (* simm: signed immediate *)

  (* EREF:6-47, VLEPEM:3-27, VLEPIM:Table A-23 (simplified) *)
  | CompareLogical of
      power_instruction_type_t
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* ra: src register 1 *)
      * power_operand_int  (* rb: src register 2 *)

  (* EREF:6-48, VLEPEM:3-27 *)
  | CompareLogicalImmediate of
      power_instruction_type_t
      * bool               (* op16: 16 bit immediate, VLE32 only *)
      * power_operand_int  (* cr: condition register field *)
      * power_operand_int  (* ra: register operand *)
      * power_operand_int  (* uimm: unsigned immediate *)

  (* EREF:6-44 (simplified, L=0) *)
  | CompareWord of
      power_instruction_type_t
      * power_operand_int  (* cr: condition register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)

  (* EREF:6-242. EREF:B-25 (simplified), VLEPEM:3-56 *)
  | ComplementRegister of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rb: source register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-55, EREF:B-21 (simplified) *)
  | ConditionRegisterNot of
      power_instruction_type_t
      * power_operand_int  (* crd: condition register destination bit *)
      * power_operand_int  (* cra: condition register source bit *)

  (* VLEPEM:3-32 *)
  | ConditionRegisterOr of
      power_instruction_type_t
      * power_operand_int  (* crd: condition register destination bit *)
      * power_operand_int  (* cra: condition register source 1 bit *)
      * power_operand_int  (* crb: condition register source 2 bit *)

  (* EREF:6-50 *)
  | CountLeadingZerosWord of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* cr0 *)

  (* EREF:6-88 *)
  | DivideWord of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-95 *)
  | DivideWordUnsigned of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* eo: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-197
     This instruction shares the same opcode with MemoryBarrier (mbar); it is
     to be preferred in server environments.
   *)
  | EnforceInOrderExecutionIO of
      power_instruction_type_t
      * power_operand_int  (* mo: memory ordering *)

  (* EREF:6-104, VLEPEM:3-35 *)
  | ExtendSignByte of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-105, VLEPEM:3-35 *)
  | ExtendSignHalfword of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* VLEPEM:3-36 *)
  | ExtendZeroByte of
      power_instruction_type_t
      * power_operand_int  (* rx: src/dst register *)

  (* VLEPEM:3-36 *)
  | ExtendZeroHalfword of
      power_instruction_type_t
      * power_operand_int  (* rx: src/dst register *)

  (* Simplified mnemonic: EREF:B-3, VLEPIM:Table A-23
     Full mnemonic: RotateLeftWordImmediateMaskInsert *)
  | ExtractRightJustifyWordImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* n: shift *)
      * power_operand_int  (* b: begin *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* Simplified mnemonic: EREF:B-3, VLEPIM:Table A-23
     Full mnemonic: RotateLeftWordImmediateMaskInsert *)
  | InsertRightWordImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* sh: shift *)
      * power_operand_int  (* mb: mask begin *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-141, VLEPEM:3-38 *)
  | InstructionSynchronize of
      power_instruction_type_t

  (* EREF:6-140 *)
  | IntegerSelect of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* crb: condition register bit *)

  (* EREF:6-140, EREF:B-26 *)
  | IntegerSelectEqual of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-140, EREF:B-26 *)
  | IntegerSelectGreaterThan of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-140, EREF:B-26 *)
  | IntegerSelectLessThan of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-146,147, VLEPEM:3-39 *)
  | LoadByteZero of
      power_instruction_type_t
      * bool               (* u: update *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-148,149, VLEPEM:3-39 *)
  | LoadByteZeroIndexed of
      power_instruction_type_t
      * bool               (* u: update *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* rb: index register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-178,179, VLEPEM:3-41 *)
  | LoadHalfwordZero of
      power_instruction_type_t
      * bool               (* u: update *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:B-24 (simplified), VLEPEM:3-42 *)
  | LoadImmediate of
      power_instruction_type_t
      * bool               (* sg: signed *)
      * bool               (* sh: shifted *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* imm: signed/unsigned immediate *)

  (* e200z759n3:79 *)
  | LoadMultipleVolatileGPRWord of
      power_instruction_type_t
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)

  (* e200z759n3:81 *)
  | LoadMultipleVolatileSPRWord of
      power_instruction_type_t
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)
      * power_operand_int  (* CR *)
      * power_operand_int  (* LR *)
      * power_operand_int  (* CTR *)
      * power_operand_int  (* XER *)

  (* e200z759n3:82 *)
  | LoadMultipleVolatileSRRWord of
      power_instruction_type_t
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)
      * power_operand_int  (* SRR0 *)
      * power_operand_int  (* SRR1 *)

  (* EREF:6-182, VLEPEM:3-43 *)
  | LoadMultipleWord of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register, count *)
      * power_operand_int  (* ra: memory base register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-193,194, VLEPEM:3-44 *)
  | LoadWordZero of
      power_instruction_type_t
      * bool               (* u: update *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: memory base register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-195,196, VLEPEM:3-44 *)
  | LoadWordZeroIndexed of
      power_instruction_type_t
      * bool               (* update *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* rb: index register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-197
     This instruction shares the same opcode with EnforceInOrderExecutionIO
     (eieio); mbar is preferred in embedded systems.
   *)
  | MemoryBarrier of
      power_instruction_type_t
      * power_operand_int  (* mo: memory ordering *)

  (* EREF:6-199, VLEPEM:3-45 *)
  | MoveConditionRegisterField of
      power_instruction_type_t
      * power_operand_int  (* crfd: destination condition register field *)
      * power_operand_int  (* crs: source condition register field *)

  (* VLEPEM:3-46 *)
  | MoveFromAlternateRegister of
      power_instruction_type_t
      * power_operand_int  (* rx: destination register *)
      * power_operand_int  (* ary: source register *)

  (* EREF:6-202 *)
  | MoveFromConditionRegister of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* cr: condition register *)

  (* VLEPEM:3-47 *)
  | MoveFromCountRegister of
      power_instruction_type_t
      * power_operand_int  (* rx: destination register *)
      * power_operand_int  (* ctr: count register *)

  (* VLEPIM:A-18 *)
  | MoveFromExceptionRegister of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* xer: integer exception register *)

  (* VLEPEM:3-48 *)
  | MoveFromLinkRegister of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* lr: link register *)

  (* EREF:6-205 *)
  | MoveFromMachineStateRegister of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* msr: machine state register *)

  (* EREF:6-208 *)
  | MoveFromSpecialPurposeRegister of
      power_instruction_type_t
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* sprn: special purpose register index *)

  (* EREF:6-241, EREF:B-25 (simplified), VLEPEM:3-49 *)
  | MoveRegister of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* rs: source register *)

  (* VLEPEM:3-50 *)
  | MoveToAlternateRegister of
      power_instruction_type_t
      * power_operand_int  (* arx: destination register *)
      * power_operand_int  (* ry: source register *)

  (* EREF:B-25 (simplified) *)
  | MoveToConditionRegister of
      power_instruction_type_t
      * power_operand_int  (* cr: condition register *)
      * power_operand_int  (* rs: source register *)

  (* EREF:6-215 *)
  | MoveToConditionRegisterFields of
      power_instruction_type_t
      * power_operand_int  (* crm: cr field mask *)
      * power_operand_int  (* rs: source register *)

  (* EREF:B-23 (simplified), VLEPEM:3-51 *)
  | MoveToCountRegister of
      power_instruction_type_t
      * power_operand_int  (* ctr: count register *)
      * power_operand_int  (* rs: source register *)

  (*EREF:B-23 (simplified) *)
  | MoveToExceptionRegister of
      power_instruction_type_t
      * power_operand_int  (* xer: integer exception register *)
      * power_operand_int  (* rs: source register *)

  (* EREF:B-25 (simplified), VLEPEM:3-52 *)
  | MoveToLinkRegister of
      power_instruction_type_t
      * power_operand_int  (* lr: link register *)
      * power_operand_int  (* rs: soure register *)

  (* EREF:6-221 *)
  | MoveToMachineStateRegister of
      power_instruction_type_t
      * power_operand_int  (* msr: machine state register *)
      * power_operand_int  (* rs: source register *)

  (* EREF:6-226 *)
  | MoveToSpecialPurposeRegister of
      power_instruction_type_t
      * power_operand_int  (* sprn: special-purpose register index *)
      * power_operand_int  (* rs: source register *)

  (* EREF:6-234 *)
  | MultiplyHighWordUnsigned of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-236, VLEPEM:3-53 *)
  | MultiplyLowImmediate of
      power_instruction_type_t
      * bool               (* op2: two operands *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source register *)
      * power_operand_int  (* simm: signed immediate *)

  (* EREF:6-237, VLEPEM:3-54 *)
  | MultiplyLowWord of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-241 *)
  | Negate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source register *)
      * power_operand_int  (* cr: condition register *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-243, VLEPEM:3-57 *)
  | Or of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-246, VLEPEM:3-57 *)
  | OrImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* s: shifted *)
      * bool               (* op2: twp operands *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* uimm: unsigned immediate *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-254, e200z759n3:70 *)
  | ReturnFromDebugInterrupt of
      power_instruction_type_t
      * power_operand_int  (* msr: machine status register *)
      * power_operand_int  (* dsr0: debug save/restore register 0 *)
      * power_operand_int  (* dsr1: debug save/restore register 1 *)

  (* EREF:6-256, VLEPEM:3-59 *)
  | ReturnFromInterrupt of
      power_instruction_type_t
      * power_operand_int  (* machine status register (MSR) *)
      * power_operand_int  (* sr0: save/restore register 0 *)
      * power_operand_int  (* sr1: save/restore register 1 *)

  (* EREF:6-257, 200z759n3:74 *)
  | ReturnFromMachineCheckInterrupt of
      power_instruction_type_t
      * power_operand_int  (* msr: machine state register (MSR) *)
      * power_operand_int  (* mcsr0: machine check save/restore register 0 *)
      * power_operand_int  (* mcsr1: machine check save/restore register 1 *)

  (* EREF:B-3 (simplified), VLEPEM:3-60 *)
  | RotateLeftWord of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register *)

  (* EREF:6-265, VLEPEM:3-62 *)
  | RotateLeftWordImmediateAndMask of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* sh: shift amount *)
      * power_operand_int  (* mb: mask begin *)
      * power_operand_int  (* me: mask end *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-275, VLEPEM:3-64 *)
  | ShiftLeftWord of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* VLEPEM:3-64 *)
  | ShiftLeftWordImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* sh: shift amount *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-278 *)
  | ShiftRightAlgebraicWord of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-279, VLEPEM:3-65 *)
  | ShiftRightAlgebraicWordImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* sh: shift amount *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-281, VLEPEM:3-66 *)
  | ShiftRightWord of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* VLEPEM:3-66 *)
  | ShiftRightWordImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* sh: shift amount *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-282,287, VLEPEM:3-67 *)
  | StoreByte of
      power_instruction_type_t
      * bool               (* update *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-288,289, VLEPEM:3-67 *)
  | StoreByteIndexed of
      power_instruction_type_t
      * bool               (* update *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* rb: index register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-310, VLEPEM:3-68 *)
  | StoreHalfword of
      power_instruction_type_t
      * bool               (* update *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-317,318, VLEPEM:3-68 *)
  | StoreHalfwordIndexed of
      power_instruction_type_t
      * bool               (* update *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* rb: index register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-320, VLEPEM:3-69 *)
  | StoreMultipleWord of
      power_instruction_type_t
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)

  (* e200z759n3:80 *)
  | StoreMultipleVolatileGPRWord of
      power_instruction_type_t
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)

  (* e200z759n3:81 *)
  | StoreMultipleVolatileSPRWord of
      power_instruction_type_t
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)
      * power_operand_int  (* CR *)
      * power_operand_int  (* LR *)
      * power_operand_int  (* CTR *)
      * power_operand_int  (* XER *)

  (* e200z759n3:83 *)
  | StoreMultipleVolatileSRRWord of
      power_instruction_type_t
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)
      * power_operand_int  (* SRR0 *)
      * power_operand_int  (* SRR1 *)

  (* EREF:6-323,329, VLEPEM:3-70 *)
  | StoreWord of
      power_instruction_type_t
      * bool               (* update *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* mem: memory operand *)

  (* EREF:6-330,331, VLEPEM:3-70 *)
  | StoreWordIndexed of
      power_instruction_type_t
      * bool               (* update *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* ra: memory base address register *)
      * power_operand_int  (* rb: index register *)
      * power_operand_int  (* mem: memory operand *)

  (* VLEPEM:3-71 *)
  | Subtract of
      power_instruction_type_t
      * power_operand_int  (* rx: destination, source 1 register *)
      * power_operand_int  (* ry: source 2 register *)

  (* EREF:6-332, VLEPEM:3-72 *)
  | SubtractFrom of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: register to be subtracted *)
      * power_operand_int  (* rb: register to be subtracted from *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* so: summary overflow field (XER-SO) *)
      * power_operand_int  (* ov: overflow field (XER-OV) *)

  (* EREF:6-337 *)
  | SubtractFromCarrying of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* ca: carry field (XER-CA) *)
      * power_operand_int  (* so: summary overflow field (XER-SO) *)
      * power_operand_int  (* ov: overflow field (XER-OV) *)

  (* EREF:6-338 *)
  | SubtractFromExtended of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: detect overflow *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register field (CR0) *)
      * power_operand_int  (* ca: carry (XER-CA) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-343, VLEPEM:3-73 *)
  | SubtractFromImmediateCarrying of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source register *)
      * power_operand_int  (* simm: signed immediate *)
      * power_operand_int  (* cr: condition register (CR0) *)
      * power_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-349 *)
  | SubtractFromZeroExtended of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow exception *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source register *)
      * power_operand_int  (* cr: condition register (CR0) *)
      * power_operand_int  (* so: summary overflow (XER-SO) *)
      * power_operand_int  (* ov: overflow (XER-OV) *)
      * power_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:B-1 (simplified), VLEPEM:3-74 *)
  | SubtractImmediate of
      power_instruction_type_t
      * bool               (* rc: record condition *)
      * power_operand_int  (* rd: destination register *)
      * power_operand_int  (* ra: source register *)
      * power_operand_int  (* imm: immediate value *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-367 *)
  | TLBWriteEntry of
      power_instruction_type_t

  (* EREF:6-374 *)
  | WriteMSRExternalEnableImmediate of
      power_instruction_type_t
      * bool               (* enable *)
      * power_operand_int  (* msr: machine stat register *)

  (* EREF:6-375 *)
  | Xor of
      power_instruction_type_t
      * bool               (* record condition *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source 1 register *)
      * power_operand_int  (* rb: source 2 register *)
      * power_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-376, VLEPEM:3-75 *)
  | XorImmediate of
      power_instruction_type_t
      * bool               (* record condition *)
      * bool               (* shifted *)
      * power_operand_int  (* ra: destination register *)
      * power_operand_int  (* rs: source register *)
      * power_operand_int  (* uimm: unsigned immediate *)
      * power_operand_int  (* cr: condition register field *)

  | OpInvalid
  | NotCode of not_code_t option
  | NoOperation
  | OpcodeIllegal of int
  | OpcodeUnpredictable of string
  | OpcodeUndefined of string
  | NotRecognized of string * doubleword_int


class type power_dictionary_int =
  object

    method index_power_opkind: power_operand_kind_t -> int
    method index_power_operand: power_operand_int -> int
    method index_power_opcode: power_opcode_t -> int

    method write_xml_power_opcode:
             ?tag:string -> xml_element_int -> power_opcode_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


class type power_assembly_instruction_int =
  object

    (* setters *)
    method set_block_entry: unit
    method set_inlined_call: unit

    (* accessors *)
    method get_address: doubleword_int
    method get_opcode: power_opcode_t
    method get_instruction_bytes: string
    method get_bytes_as_hexstring: string

    (* predicates *)
    method is_block_entry: bool
    method is_not_code: bool
    method is_non_code_block: bool
    method is_vle: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString: string
    method toPretty: pretty_t

  end


type power_assembly_instruction_result =
  power_assembly_instruction_int traceresult


class type power_assembly_instructions_int =
  object

    (* setters *)
    method set_instruction:
             doubleword_int -> power_assembly_instruction_int -> unit
    method set_not_code: data_block_int list -> unit

    (* accessors *)
    method length: int

    (** [get_instruction va] returns the instruction located at virtual address
        [va]. If no instruction has been entered yet, a new instruction, with
        opcode [OpInvalid] is assigned and returned. If [va] is out-of-range
        an Error result is returned. *)
    method get_instruction: doubleword_int -> power_assembly_instruction_result

    (* method at_address: doubleword_int -> power_assembly_instruction_int *)

    (** [get_next_valid_instruction_address va] returns the least virtual
        address strictly larger than [va] with a valid assembly instruction.
        If no such address exists, or if [va] is out-of-range, Error is
        returned.*)
    method get_next_valid_instruction_address:
             doubleword_int -> doubleword_int traceresult

    method get_prev_valid_instruction_address:
             doubleword_int -> doubleword_int traceresult

    (* iterators *)
    method iteri: (int -> power_assembly_instruction_int -> unit) -> unit
    method itera:
             (doubleword_int -> power_assembly_instruction_int -> unit) -> unit

    (* predicates *)

    (** [is_code_address va] returns true if [va] is a virtual address within
        the code space and if the address holds a valid assembly instruction
        (i.e., it is the starting address of an assembly instruction). *)
    method is_code_address: doubleword_int -> bool

    (** [has_next_valid_instruction va] returns true if [va] is a virtual address
        within the code and there exists a virtual address with a valid
        instruction that is strictly larger than [va].*)
    method has_next_valid_instruction: doubleword_int -> bool

    method has_prev_valid_instruction: doubleword_int -> bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString:
             ?filter: (power_assembly_instruction_int -> bool) -> unit -> string
    method toPretty: pretty_t

  end


class type power_assembly_block_int =
  object

    (* accessors *)
    method get_faddr: doubleword_int
    method get_first_address: doubleword_int
    method get_last_address: doubleword_int
    method get_instruction: doubleword_int -> power_assembly_instruction_int

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool
    method is_returning: bool

    (* printing *)
    method toString: string
    method toPretty: pretty_t
  end


class type power_assembly_function_int =
  object

    (* accessors *)
    method get_address: doubleword_int
    method get_blocks: power_assembly_block_int list

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool

    (* printing *)
    method toPretty: pretty_t

  end


class type power_assembly_functions_int =
  object

    (* setters *)
    method add_function: power_assembly_function_int -> unit

    (* accessors *)
    method get_functions: power_assembly_function_int list
    method get_function_by_address: doubleword_int -> power_assembly_function_int

    (* predicates *)
    method has_function_by_address: doubleword_int -> bool
    method includes_instruction_address: doubleword_int -> bool

  end

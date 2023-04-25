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


type pwr_instruction_type_t = | PWR | VLE16 | VLE32

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


(* defined in bchlib/bCHLibTypes:

type pwr_special_reg_t =
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


type pwr_register_field_t =
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
 *)

type pwr_operand_kind_t =
  | PowerGPReg of int
  | PowerSpecialReg of pwr_special_reg_t
  | PowerRegisterField of pwr_register_field_t
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
type pwr_operand_mode_t = RD | WR | RW | NT


type pwr_branch_prediction_t = BPNone | BPPlus of int | BPMinus of int


class type pwr_operand_int =
  object ('a)

    (* accessors *)
    method get_kind: pwr_operand_kind_t
    method get_mode: pwr_operand_mode_t
    method get_gp_register: int
    method get_special_register: pwr_special_reg_t
    method get_register_field: pwr_register_field_t
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


type pwr_opcode_t =
  (* EREF:6-12, VLEPEM:3-6 *)
  | Add of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register (CR0) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-17 *)
  | AddCarrying of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register (CR0) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-18 *)
  | AddExtended of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-23, VLEPEM:3-7 *)
  | AddImmediate of
      pwr_instruction_type_t
      * bool               (* s: shifted *)
      * bool               (* op2: 2-operand *)
      * bool               (* op16: 16-bit immediate *)
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source operand *)
      * pwr_operand_int  (* simm: signed immediate *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-24, VLEPEM:3-9 *)
  | AddImmediateCarrying of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source register *)
      * pwr_operand_int  (* simm: signed immediate *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* ca: carry field (XER-CA) *)

  (* EREF:6-26 *)
  | AddMinusOneExtended of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-31 *)
  | AddZeroExtended of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow exception *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-32, VLEPEM:3-10 *)
  | And of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-33, VLEPEM:3-10 *)
  | AndComplement of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-34,35, VLEPEM:3-10 *)
  | AndImmediate of
      pwr_instruction_type_t
      * bool               (* s: shifted *)
      * bool               (* op2: 2-operand *)
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* uimm: unsigned immediate *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* VLEPEM:3-14 *)
  | BitClearImmediate of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: dst/src register *)
      * pwr_operand_int  (* ui5: immediate *)

  (* VLEPEM:3-16 *)
  | BitGenerateImmediate of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: destination register *)
      * pwr_operand_int  (* ui5: immediate *)

  (* VLEPEM:3-18 *)
  | BitMaskGenerateImmediate of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: destination register *)
      * pwr_operand_int  (* ui5: immediate *)

  (* VLEPEM:3-19 *)
  | BitSetImmediate of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: destination register *)
      * pwr_operand_int  (* ui5: immediate *)

  (* VLEPEM:3-20 *)
  | BitTestImmediate of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: source register *)
      * pwr_operand_int  (* uimm: unsigned immediate *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-36, VLEPEM:3-12 *)
  | Branch of
      pwr_instruction_type_t
      * pwr_operand_int  (* tgt: target address *)

  (* EREF:6-37 *)
  | BranchConditional of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations (5 bits) *)
      * int                (* bi: bit in condition register (5 bits)  *)
      * pwr_operand_int  (* bd: branch destination *)

  (* EREF:6-41 *)
  | BranchConditionalLinkRegister of
      pwr_instruction_type_t
      * int                (* bo: bracnch operations (5 bits) *)
      * int                (* bi: bit in condition register (5 bits) *)
      * int                (* bh: branch usage hint (2 bits) *)
      * pwr_operand_int  (* lr: link register (LR) *)

  (* EREF:6-41 *)
  | BranchConditionalLinkRegisterLink of
      pwr_instruction_type_t
      * int                (* bo: branch operations (5 bits) *)
      * int                (* bi: bit in condition register (5 bits) *)
      * int                (* bh: branch usage hint (2 bits *)
      * pwr_operand_int  (* lr: link register (LR) *)

  | BranchCountRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* count register (CTR) *)

  | BranchCountRegisterLink of
      pwr_instruction_type_t
      * pwr_operand_int  (* count_register (CTR) *)

  (* EREF:6-36, VLEPEM:3-12 *)
  | BranchLink of
      pwr_instruction_type_t
      * pwr_operand_int  (* tgt: target address *)
      * pwr_operand_int  (* lr: link register (LR) *)

  (* EREF:B-13 (simplified), VLEPEM:3-17 *)
  | BranchLinkRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* link register (LR) *)

  (* EREF:B-14 (simplified), VLEPEM:3-17 *)
  | BranchLinkRegisterLink of
      pwr_instruction_type_t
      * pwr_operand_int  (* link register (LR) *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchDecrementNotZero of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * pwr_branch_prediction_t  (* bp: branch prediction *)
      * pwr_operand_int  (* bd: branch destination *)
      * pwr_operand_int  (* ctr: count register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchDecrementZero of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * pwr_branch_prediction_t  (* bp: branch prediction *)
      * pwr_operand_int  (* bd: branch destination *)
      * pwr_operand_int  (* ctr: count register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchEqual of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * pwr_branch_prediction_t  (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchEqualLinkRegister of
      pwr_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * pwr_branch_prediction_t (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchGreaterEqual of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * pwr_branch_prediction_t (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchGreaterEqualLinkRegister of
      pwr_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * pwr_branch_prediction_t (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchGreaterThan of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * pwr_branch_prediction_t (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchGreaterThanLinkRegister of
      pwr_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * pwr_branch_prediction_t (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics, VLEPEM:3-13) *)
  | CBranchLessEqual of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * pwr_branch_prediction_t  (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchLessEqualLinkRegister of
      pwr_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * pwr_branch_prediction_t (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchLessThan of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * pwr_branch_prediction_t  (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchLessThanLinkRegister of
      pwr_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * pwr_branch_prediction_t (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* lr: link register *)

  (* EREF:6-37, EREF:B-4 (simplified mnemonics), VLEPEM:3-13 *)
  | CBranchNotEqual of
      pwr_instruction_type_t
      * bool               (* aa: absolute address *)
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * pwr_branch_prediction_t  (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* bd: branch destination *)

  (* EREF:6-41, EREF:B-3 (simplified) *)
  | CBranchNotEqualLinkRegister of
      pwr_instruction_type_t
      * int                (* bo: branch operations *)
      * int                (* bi: bit in condition register *)
      * int                (* bh: branch usage hint *)
      * pwr_branch_prediction_t (* bp: branch prediction *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* lr: link register *)

  (* EREF:B-3 (simplified *)
  | ClearLeftShiftLeftWordImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* mb: mask begin *)
      * pwr_operand_int  (* sh: shift *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* Simplified mnemonic, EREF:B-3, VLEPIM:Table A-23
     Full instruction: RotateLeftWordImmediateAndMask *)
  | ClearLeftWordImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* mb: mask begin *)

  (* Simplified mnemonic, EREF:B-3, VLEPIM:Table A-23
     Full instruction: RotateLeftWordImmediateAndMask *)
  | ClearRightWordImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* me: mask end *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-46, VLEPEM:3-21 *)
  | CompareImmediate of
      pwr_instruction_type_t
      * bool               (* op16: 16-bit immediate, VLE32 only *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* ra: register operand *)
      * pwr_operand_int  (* simm: signed immediate *)

  (* EREF:6-47, VLEPEM:3-27, VLEPIM:Table A-23 (simplified) *)
  | CompareLogical of
      pwr_instruction_type_t
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* ra: src register 1 *)
      * pwr_operand_int  (* rb: src register 2 *)

  (* EREF:6-48, VLEPEM:3-27 *)
  | CompareLogicalImmediate of
      pwr_instruction_type_t
      * bool               (* op16: 16 bit immediate, VLE32 only *)
      * pwr_operand_int  (* cr: condition register field *)
      * pwr_operand_int  (* ra: register operand *)
      * pwr_operand_int  (* uimm: unsigned immediate *)

  (* EREF:6-44 (simplified, L=0) *)
  | CompareWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* cr: condition register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)

  (* EREF:6-242. EREF:B-25 (simplified), VLEPEM:3-56 *)
  | ComplementRegister of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rb: source register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-55, EREF:B-21 (simplified) *)
  | ConditionRegisterNot of
      pwr_instruction_type_t
      * pwr_operand_int  (* crd: condition register destination bit *)
      * pwr_operand_int  (* cra: condition register source bit *)

  (* VLEPEM:3-32 *)
  | ConditionRegisterOr of
      pwr_instruction_type_t
      * pwr_operand_int  (* crd: condition register destination bit *)
      * pwr_operand_int  (* cra: condition register source 1 bit *)
      * pwr_operand_int  (* crb: condition register source 2 bit *)

  (* EREF:6-50 *)
  | CountLeadingZerosWord of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* cr0 *)

  (* EREF:6-88 *)
  | DivideWord of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-95 *)
  | DivideWordUnsigned of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* eo: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-197
     This instruction shares the same opcode with MemoryBarrier (mbar); it is
     to be preferred in server environments.
   *)
  | EnforceInOrderExecutionIO of
      pwr_instruction_type_t
      * pwr_operand_int  (* mo: memory ordering *)

  (* EREF:6-104, VLEPEM:3-35 *)
  | ExtendSignByte of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-105, VLEPEM:3-35 *)
  | ExtendSignHalfword of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* VLEPEM:3-36 *)
  | ExtendZeroByte of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: src/dst register *)

  (* VLEPEM:3-36 *)
  | ExtendZeroHalfword of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: src/dst register *)

  (* Simplified mnemonic: EREF:B-3, VLEPIM:Table A-23
     Full mnemonic: RotateLeftWordImmediateMaskInsert *)
  | ExtractRightJustifyWordImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* n: shift *)
      * pwr_operand_int  (* b: begin *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* Simplified mnemonic: EREF:B-3, VLEPIM:Table A-23
     Full mnemonic: RotateLeftWordImmediateMaskInsert *)
  | InsertRightWordImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* sh: shift *)
      * pwr_operand_int  (* mb: mask begin *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-141, VLEPEM:3-38 *)
  | InstructionSynchronize of
      pwr_instruction_type_t

  (* EREF:6-140 *)
  | IntegerSelect of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* crb: condition register bit *)

  (* EREF:6-140, EREF:B-26 *)
  | IntegerSelectEqual of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-140, EREF:B-26 *)
  | IntegerSelectGreaterThan of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-140, EREF:B-26 *)
  | IntegerSelectLessThan of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-146,147, VLEPEM:3-39 *)
  | LoadByteZero of
      pwr_instruction_type_t
      * bool               (* u: update *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-148,149, VLEPEM:3-39 *)
  | LoadByteZeroIndexed of
      pwr_instruction_type_t
      * bool               (* u: update *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* rb: index register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-178,179, VLEPEM:3-41 *)
  | LoadHalfwordZero of
      pwr_instruction_type_t
      * bool               (* u: update *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:B-24 (simplified), VLEPEM:3-42 *)
  | LoadImmediate of
      pwr_instruction_type_t
      * bool               (* sg: signed *)
      * bool               (* sh: shifted *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* imm: signed/unsigned immediate *)

  (* e200z759n3:79 *)
  | LoadMultipleVolatileGPRWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* e200z759n3:81 *)
  | LoadMultipleVolatileSPRWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)
      * pwr_operand_int  (* CR *)
      * pwr_operand_int  (* LR *)
      * pwr_operand_int  (* CTR *)
      * pwr_operand_int  (* XER *)

  (* e200z759n3:82 *)
  | LoadMultipleVolatileSRRWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)
      * pwr_operand_int  (* SRR0 *)
      * pwr_operand_int  (* SRR1 *)

  (* EREF:6-182, VLEPEM:3-43 *)
  | LoadMultipleWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register, count *)
      * pwr_operand_int  (* ra: memory base register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-193,194, VLEPEM:3-44 *)
  | LoadWordZero of
      pwr_instruction_type_t
      * bool               (* u: update *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: memory base register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-195,196, VLEPEM:3-44 *)
  | LoadWordZeroIndexed of
      pwr_instruction_type_t
      * bool               (* update *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* rb: index register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-197
     This instruction shares the same opcode with EnforceInOrderExecutionIO
     (eieio); mbar is preferred in embedded systems.
   *)
  | MemoryBarrier of
      pwr_instruction_type_t
      * pwr_operand_int  (* mo: memory ordering *)

  (* EREF:6-199, VLEPEM:3-45 *)
  | MoveConditionRegisterField of
      pwr_instruction_type_t
      * pwr_operand_int  (* crfd: destination condition register field *)
      * pwr_operand_int  (* crs: source condition register field *)

  (* VLEPEM:3-46 *)
  | MoveFromAlternateRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: destination register *)
      * pwr_operand_int  (* ary: source register *)

  (* EREF:6-202 *)
  | MoveFromConditionRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* cr: condition register *)

  (* VLEPEM:3-47 *)
  | MoveFromCountRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: destination register *)
      * pwr_operand_int  (* ctr: count register *)

  (* VLEPIM:A-18 *)
  | MoveFromExceptionRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* xer: integer exception register *)

  (* VLEPEM:3-48 *)
  | MoveFromLinkRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* lr: link register *)

  (* EREF:6-205 *)
  | MoveFromMachineStateRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* msr: machine state register *)

  (* EREF:6-208 *)
  | MoveFromSpecialPurposeRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* sprn: special purpose register index *)

  (* EREF:6-241, EREF:B-25 (simplified), VLEPEM:3-49 *)
  | MoveRegister of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* rs: source register *)

  (* VLEPEM:3-50 *)
  | MoveToAlternateRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* arx: destination register *)
      * pwr_operand_int  (* ry: source register *)

  (* EREF:B-25 (simplified) *)
  | MoveToConditionRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* cr: condition register *)
      * pwr_operand_int  (* rs: source register *)

  (* EREF:6-215 *)
  | MoveToConditionRegisterFields of
      pwr_instruction_type_t
      * pwr_operand_int  (* crm: cr field mask *)
      * pwr_operand_int  (* rs: source register *)

  (* EREF:B-23 (simplified), VLEPEM:3-51 *)
  | MoveToCountRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* ctr: count register *)
      * pwr_operand_int  (* rs: source register *)

  (*EREF:B-23 (simplified) *)
  | MoveToExceptionRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* xer: integer exception register *)
      * pwr_operand_int  (* rs: source register *)

  (* EREF:B-25 (simplified), VLEPEM:3-52 *)
  | MoveToLinkRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* lr: link register *)
      * pwr_operand_int  (* rs: soure register *)

  (* EREF:6-221 *)
  | MoveToMachineStateRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* msr: machine state register *)
      * pwr_operand_int  (* rs: source register *)

  (* EREF:6-226 *)
  | MoveToSpecialPurposeRegister of
      pwr_instruction_type_t
      * pwr_operand_int  (* sprn: special-purpose register index *)
      * pwr_operand_int  (* rs: source register *)

  (* EREF:6-234 *)
  | MultiplyHighWordUnsigned of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)

  (* EREF:6-236, VLEPEM:3-53 *)
  | MultiplyLowImmediate of
      pwr_instruction_type_t
      * bool               (* op2: two operands *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source register *)
      * pwr_operand_int  (* simm: signed immediate *)

  (* EREF:6-237, VLEPEM:3-54 *)
  | MultiplyLowWord of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-241 *)
  | Negate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source register *)
      * pwr_operand_int  (* cr: condition register *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-243, VLEPEM:3-57 *)
  | Or of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-246, VLEPEM:3-57 *)
  | OrImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* s: shifted *)
      * bool               (* op2: twp operands *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* uimm: unsigned immediate *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-254, e200z759n3:70 *)
  | ReturnFromDebugInterrupt of
      pwr_instruction_type_t
      * pwr_operand_int  (* msr: machine status register *)
      * pwr_operand_int  (* dsr0: debug save/restore register 0 *)
      * pwr_operand_int  (* dsr1: debug save/restore register 1 *)

  (* EREF:6-256, VLEPEM:3-59 *)
  | ReturnFromInterrupt of
      pwr_instruction_type_t
      * pwr_operand_int  (* machine status register (MSR) *)
      * pwr_operand_int  (* sr0: save/restore register 0 *)
      * pwr_operand_int  (* sr1: save/restore register 1 *)

  (* EREF:6-257, 200z759n3:74 *)
  | ReturnFromMachineCheckInterrupt of
      pwr_instruction_type_t
      * pwr_operand_int  (* msr: machine state register (MSR) *)
      * pwr_operand_int  (* mcsr0: machine check save/restore register 0 *)
      * pwr_operand_int  (* mcsr1: machine check save/restore register 1 *)

  (* EREF:B-3 (simplified), VLEPEM:3-60 *)
  | RotateLeftWord of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register *)

  (* EREF:6-265, VLEPEM:3-62 *)
  | RotateLeftWordImmediateAndMask of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* sh: shift amount *)
      * pwr_operand_int  (* mb: mask begin *)
      * pwr_operand_int  (* me: mask end *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-275, VLEPEM:3-64 *)
  | ShiftLeftWord of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* VLEPEM:3-64 *)
  | ShiftLeftWordImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* sh: shift amount *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-278 *)
  | ShiftRightAlgebraicWord of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-279, VLEPEM:3-65 *)
  | ShiftRightAlgebraicWordImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* sh: shift amount *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-281, VLEPEM:3-66 *)
  | ShiftRightWord of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* VLEPEM:3-66 *)
  | ShiftRightWordImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* sh: shift amount *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-282,287, VLEPEM:3-67 *)
  | StoreByte of
      pwr_instruction_type_t
      * bool               (* update *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-288,289, VLEPEM:3-67 *)
  | StoreByteIndexed of
      pwr_instruction_type_t
      * bool               (* update *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* rb: index register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-310, VLEPEM:3-68 *)
  | StoreHalfword of
      pwr_instruction_type_t
      * bool               (* update *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-317,318, VLEPEM:3-68 *)
  | StoreHalfwordIndexed of
      pwr_instruction_type_t
      * bool               (* update *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* rb: index register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-320, VLEPEM:3-69 *)
  | StoreMultipleWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* e200z759n3:80 *)
  | StoreMultipleVolatileGPRWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* e200z759n3:81 *)
  | StoreMultipleVolatileSPRWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)
      * pwr_operand_int  (* CR *)
      * pwr_operand_int  (* LR *)
      * pwr_operand_int  (* CTR *)
      * pwr_operand_int  (* XER *)

  (* e200z759n3:83 *)
  | StoreMultipleVolatileSRRWord of
      pwr_instruction_type_t
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)
      * pwr_operand_int  (* SRR0 *)
      * pwr_operand_int  (* SRR1 *)

  (* EREF:6-323,329, VLEPEM:3-70 *)
  | StoreWord of
      pwr_instruction_type_t
      * bool               (* update *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* EREF:6-330,331, VLEPEM:3-70 *)
  | StoreWordIndexed of
      pwr_instruction_type_t
      * bool               (* update *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* ra: memory base address register *)
      * pwr_operand_int  (* rb: index register *)
      * pwr_operand_int  (* mem: memory operand *)

  (* VLEPEM:3-71 *)
  | Subtract of
      pwr_instruction_type_t
      * pwr_operand_int  (* rx: destination, source 1 register *)
      * pwr_operand_int  (* ry: source 2 register *)

  (* EREF:6-332, VLEPEM:3-72 *)
  | SubtractFrom of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: register to be subtracted *)
      * pwr_operand_int  (* rb: register to be subtracted from *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* so: summary overflow field (XER-SO) *)
      * pwr_operand_int  (* ov: overflow field (XER-OV) *)

  (* EREF:6-337 *)
  | SubtractFromCarrying of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow detection *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* ca: carry field (XER-CA) *)
      * pwr_operand_int  (* so: summary overflow field (XER-SO) *)
      * pwr_operand_int  (* ov: overflow field (XER-OV) *)

  (* EREF:6-338 *)
  | SubtractFromExtended of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: detect overflow *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register field (CR0) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)

  (* EREF:6-343, VLEPEM:3-73 *)
  | SubtractFromImmediateCarrying of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source register *)
      * pwr_operand_int  (* simm: signed immediate *)
      * pwr_operand_int  (* cr: condition register (CR0) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:6-349 *)
  | SubtractFromZeroExtended of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* oe: overflow exception *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source register *)
      * pwr_operand_int  (* cr: condition register (CR0) *)
      * pwr_operand_int  (* so: summary overflow (XER-SO) *)
      * pwr_operand_int  (* ov: overflow (XER-OV) *)
      * pwr_operand_int  (* ca: carry (XER-CA) *)

  (* EREF:B-1 (simplified), VLEPEM:3-74 *)
  | SubtractImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* rd: destination register *)
      * pwr_operand_int  (* ra: source register *)
      * pwr_operand_int  (* imm: immediate value *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-367 *)
  | TLBWriteEntry of
      pwr_instruction_type_t

  (* EREF:6-374 *)
  | WriteMSRExternalEnableImmediate of
      pwr_instruction_type_t
      * bool               (* enable *)
      * pwr_operand_int  (* msr: machine stat register *)

  (* EREF:6-375 *)
  | Xor of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source 1 register *)
      * pwr_operand_int  (* rb: source 2 register *)
      * pwr_operand_int  (* cr: condition register (CR0) *)

  (* EREF:6-376, VLEPEM:3-75 *)
  | XorImmediate of
      pwr_instruction_type_t
      * bool               (* rc: record condition *)
      * bool               (* s: shifted *)
      * pwr_operand_int  (* ra: destination register *)
      * pwr_operand_int  (* rs: source register *)
      * pwr_operand_int  (* uimm: unsigned immediate *)
      * pwr_operand_int  (* cr: condition register field *)

  | OpInvalid
  | NotCode of not_code_t option
  | NoOperation
  | OpcodeIllegal of int
  | OpcodeUnpredictable of string
  | OpcodeUndefined of string
  | NotRecognized of string * doubleword_int


class type pwr_dictionary_int =
  object

    method index_pwr_opkind: pwr_operand_kind_t -> int
    method index_pwr_operand: pwr_operand_int -> int
    method index_pwr_branch_prediction: pwr_branch_prediction_t -> int
    method index_pwr_opcode: pwr_opcode_t -> int
    method index_pwr_bytestring: string -> int

    method write_xml_pwr_bytestring:
             ?tag:string -> xml_element_int -> string -> unit
    method write_xml_pwr_opcode:
             ?tag:string -> xml_element_int -> pwr_opcode_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


class type pwr_assembly_instruction_int =
  object

    (* setters *)
    method set_block_entry: unit
    method set_inlined_call: unit

    (* accessors *)
    method get_address: doubleword_int
    method get_opcode: pwr_opcode_t
    method get_instruction_bytes: string
    method get_bytes_as_hexstring: string

    (* predicates *)
    method is_block_entry: bool
    method is_not_code: bool
    method is_non_code_block: bool
    method is_valid_instruction: bool
    method is_vle: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString: string
    method toPretty: pretty_t

  end


type pwr_assembly_instruction_result =
  pwr_assembly_instruction_int traceresult


class type pwr_assembly_instructions_int =
  object

    (* setters *)
    method set_instruction:
             doubleword_int -> pwr_assembly_instruction_int -> unit
    method set_not_code: data_block_int list -> unit

    (* accessors *)
    method length: int

    (** [get_instruction va] returns the instruction located at virtual address
        [va]. If no instruction has been entered yet, a new instruction, with
        opcode [OpInvalid] is assigned and returned. If [va] is out-of-range
        an Error result is returned. *)
    method get_instruction: doubleword_int -> pwr_assembly_instruction_result

    (* method at_address: doubleword_int -> pwr_assembly_instruction_int *)

    (** [get_next_valid_instruction_address va] returns the least virtual
        address strictly larger than [va] with a valid assembly instruction.
        If no such address exists, or if [va] is out-of-range, Error is
        returned.*)
    method get_next_valid_instruction_address:
             doubleword_int -> doubleword_int traceresult

    method get_prev_valid_instruction_address:
             doubleword_int -> doubleword_int traceresult

    (** [get_code_addresses_rev low high] returns the list of virtual addresses
        bounded by [low] and [high] that hold valid instructions, in reverse
        order. [low] defaults to [0x0], [high] defaults to [0xffffffff] *)
    method get_code_addresses_rev:
             ?low:doubleword_int
             -> ?high:doubleword_int
             -> unit
             -> doubleword_int list

    (* iterators *)
    method iteri: (int -> pwr_assembly_instruction_int -> unit) -> unit
    method itera:
             (doubleword_int -> pwr_assembly_instruction_int -> unit) -> unit
    method get_num_instructions: int
    method get_num_unknown_instructions: int

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
             ?filter: (pwr_assembly_instruction_int -> bool) -> unit -> string
    method toPretty: pretty_t

  end


class type pwr_assembly_block_int =
  object

    (* accessors *)
    method location: location_int
    method context: context_t list
    method context_string: ctxt_iaddress_t
    method faddr: doubleword_int
    method first_address: doubleword_int
    method last_address: doubleword_int
    method successors: ctxt_iaddress_t list

    method get_instructions_rev:
             ?high:doubleword_int
             -> unit
             -> pwr_assembly_instruction_int list
    method get_instructions: pwr_assembly_instruction_int list
    method get_instruction: doubleword_int -> pwr_assembly_instruction_int

    method get_bytes_as_hexstring: string
    method get_instruction_count: int

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool
    method is_returning: bool

    (* iterators *)
    method itera:
             ?low:doubleword_int
             -> ?high:doubleword_int
             -> ?reverse:bool
             -> (ctxt_iaddress_t -> pwr_assembly_instruction_int -> unit)
             -> unit

    (* printing *)
    method toString: string
    method toPretty: pretty_t
  end


class type pwr_assembly_function_int =
  object

    (* accessors *)
    method faddr: doubleword_int
    method blocks: pwr_assembly_block_int list
    method cfg_edges: (ctxt_iaddress_t * ctxt_iaddress_t) list

    method get_block: ctxt_iaddress_t -> pwr_assembly_block_int
    method get_instruction: doubleword_int -> pwr_assembly_instruction_int
    method get_bytes_as_hexstring: string
    method get_function_md5: string
    method get_instruction_count: int
    method get_block_count: int
    method get_not_valid_instr_count: int

    (* iterators *)
    method iter: (pwr_assembly_block_int -> unit) -> unit
    method itera: (ctxt_iaddress_t -> pwr_assembly_block_int -> unit) -> unit
    method iteri:
             (doubleword_int
              -> ctxt_iaddress_t
              -> pwr_assembly_instruction_int
              -> unit)
             -> unit
    method populate_callgraph: callgraph_int -> unit

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool

    (* printing *)
    method toPretty: pretty_t

  end


class type pwr_assembly_functions_int =
  object

    (* reset *)
    method reset: unit

    (* setters *)
    method add_function: pwr_assembly_function_int -> unit
    method remove_function: doubleword_int -> unit

    (* accessors *)
    method get_callgraph: callgraph_int
    method functions: pwr_assembly_function_int list
    method get_function: dw_index_t -> pwr_assembly_function_int
    method get_function_by_address: doubleword_int -> pwr_assembly_function_int
    method get_function_coverage:
             int     (* coverage *)
             * int   (* overlap *)
             * int   (* multiplicity *)
    method get_num_functions: int

    (* iterators *)
    method iter: (pwr_assembly_function_int -> unit) -> unit
    method itera: (doubleword_int -> pwr_assembly_function_int -> unit) -> unit
    method bottom_up_itera:
             (doubleword_int -> pwr_assembly_function_int -> unit) -> unit
    method top_down_itera:
             (doubleword_int -> pwr_assembly_function_int -> unit) -> unit

    (* predicates *)
    method has_function_by_address: doubleword_int -> bool
    method includes_instruction_address: doubleword_int -> bool

    (* printing *)
    method dark_matter_to_string: string
    method duplicates_to_string: string

  end


class type pwr_code_pc_int =
  object

    (* accessors *)
    method get_next_instruction: ctxt_iaddress_t * pwr_assembly_instruction_int
    method block_successors: ctxt_iaddress_t list
    method get_block_successor: ctxt_iaddress_t
    method get_false_branch_successor: ctxt_iaddress_t
    method get_true_branch_successor: ctxt_iaddress_t
    method get_conditional_successor_info:
             (location_int
              * location_int
              * ctxt_iaddress_t
              * ctxt_iaddress_t
              * xpr_t)

    (* predicates *)
    method has_more_instructions: bool
    method has_conditional_successor: bool
  end


class type pwr_chif_system_int =
  object

    (* reset *)
    method reset: unit

    (* setters *)
    method add_pwr_procedure: procedure_int -> unit

    (* accessors *)
    method get_pwr_system: system_int
    method get_pwr_procedure_names: symbol_t list
    method get_pwr_procedure: doubleword_int -> procedure_int

    (* predicates *)
    method has_pwr_procedure: doubleword_int -> bool
  end


class type pwr_opcode_dictionary_int =
  object

    method index_sp_offset: int * interval_t -> int

    (** [index_instr instr floc] indexes the variable locations and
        invariant expressions associated with the arguments of [instr],
        made accessible via the function location [floc].*)
    method index_instr:
             pwr_assembly_instruction_int
             -> floc_int
             -> int

    method get_sp_offset: int -> (int * interval_t)

    method write_xml_sp_offset:
             ?tag:string
             -> xml_element_int
             -> int * interval_t
             -> unit
    method write_xml_instr:
             ?tag:string
             -> xml_element_int
             -> pwr_assembly_instruction_int
             -> floc_int
             -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t
  end


class type pwr_analysis_results_int =
  object
    method record_results: ?save:bool -> pwr_assembly_function_int -> unit
    method write_xml: xml_element_int -> unit
    method save: unit
  end

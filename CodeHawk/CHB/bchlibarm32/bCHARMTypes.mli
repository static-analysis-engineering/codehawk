(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2023 Aarno Labs, LLC

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
open BCHBCTypes
open BCHLibTypes


(** {b Principal type definitions for [bchlibarm32].} *)


(** {1 Operand components}*)

(** Change processor status*)
type cps_effect_t =
  | Interrupt_Enable
  | Interrupt_Disable
  | Interrupt_NoChange


type interrupt_flags_t =   (* in change processor status *)
  | IFlag_A
  | IFlag_I
  | IFlag_F
  | IFlag_AI
  | IFlag_AF
  | IFlag_IF
  | IFlag_AIF
  | IFlag_None


type shift_rotate_type_t =
  | SRType_LSL
  | SRType_LSR
  | SRType_ASR
  | SRType_ROR
  | SRType_RRX


type dmb_option_t =  (* data memory barrier option *)
  | FullSystemRW
  | FullSystemW
  | InnerShareableRW
  | InnerShareableW
  | NonShareableRW
  | NonShareableW
  | OuterShareableRW
  | OuterShareableW


type vfp_datatype_t =    (* Advanced SIMD extension A2.6.3 *)
  | VfpNone
  | VfpSize of int
  | VfpFloat of int
  | VfpInt of int
  | VfpPolynomial of int
  | VfpSignedInt of int
  | VfpUnsignedInt of int


type register_shift_rotate_t =
  | ARMImmSRT of shift_rotate_type_t * int    (* immediate shift amount *)
  | ARMRegSRT of shift_rotate_type_t * arm_reg_t (* shift amount in reg *)


type arm_memory_offset_t =
  | ARMImmOffset of int
  | ARMIndexOffset of arm_reg_t * int  (* additional offset *)
  | ARMShiftedIndexOffset of arm_reg_t * register_shift_rotate_t * int


type arm_simd_writeback_t =
  | SIMDNoWriteback
  | SIMDBytesTransferred of int
  | SIMDAddressOffsetRegister of arm_reg_t


type arm_simd_list_element_t =
  | SIMDReg of arm_extension_register_t
  | SIMDRegElement of arm_extension_register_element_t
  | SIMDRegRepElement of arm_extension_register_replicated_element_t


type arm_operand_kind_t =
  | ARMDMBOption of dmb_option_t
  | ARMCPSEffect of cps_effect_t
  | ARMInterruptFlags of interrupt_flags_t
  | ARMReg of arm_reg_t
  | ARMDoubleReg of arm_reg_t * arm_reg_t
  | ARMWritebackReg of
      bool  (* true if part of single memory access *)
      * arm_reg_t  (* base register *)
      * int option (* increment/decrement in bytes of base register value *)
  | ARMSpecialReg of arm_special_reg_t
  | ARMExtensionReg of arm_extension_register_t
  | ARMDoubleExtensionReg of arm_extension_register_t * arm_extension_register_t
  | ARMExtensionRegElement of arm_extension_register_element_t
  | ARMRegList of arm_reg_t list
  | ARMExtensionRegList of arm_extension_register_t list
  | ARMShiftedReg of arm_reg_t * register_shift_rotate_t
  | ARMRegBitSequence of arm_reg_t * int * int (* lsb, widthm1 *)
  | ARMImmediate of immediate_int
  | ARMFPConstant of float
  | ARMAbsolute of doubleword_int
  | ARMLiteralAddress of doubleword_int
  | ARMMemMultiple of
      arm_reg_t  (* register that holds the memory address *)
      * int   (* alignment, default is 0 *)
      * int   (* number of memory locations *)
      * int   (* size of memory location (4 or 8 bytes) *)
  | ARMOffsetAddress of
      arm_reg_t                  (* base register *)
      * int                      (* alignment of register value *)
      * arm_memory_offset_t      (* offset *)
      * bool                     (* isadd *)
      * bool                     (* iswback *)
      * bool                     (* isindex *)
      * int                      (* size, in bytes, of value addressed *)
  | ARMSIMDAddress of
      arm_reg_t                  (* base register *)
      * int                      (* alignment *)
      * arm_simd_writeback_t     (* writeback mode *)
  | ARMSIMDList of arm_simd_list_element_t list


type arm_operand_mode_t = RD | WR | RW


class type arm_operand_int =
  object ('a)

    (* accessors *)
    method get_kind: arm_operand_kind_t
    method get_mode: arm_operand_mode_t
    method get_size: int  (* operand size in bytes *)
    method get_register: arm_reg_t
    method get_extension_register: arm_extension_register_t
    method get_register_count: int
    method get_register_list: arm_reg_t list
    method get_register_op_list: 'a list
    method get_extension_register_op_list: 'a list
    method get_absolute_address: doubleword_int
    method get_literal_address: doubleword_int
    method get_pc_relative_address: doubleword_int -> int -> doubleword_int

    (* converters *)
    method to_numerical: numerical_t
    method to_register: register_t
    method to_multiple_register: register_t list
    method to_address: floc_int -> xpr_t
    method to_variable: floc_int -> variable_t
    method to_multiple_variable: floc_int -> variable_t list
    method to_expr: ?unsigned:bool -> floc_int -> xpr_t
    method to_multiple_expr: floc_int -> xpr_t list
    method to_lhs: floc_int -> variable_t * cmd_t list
    method to_multiple_lhs: floc_int -> variable_t list * cmd_t list
    method to_updated_offset_address: floc_int -> xpr_t
    method to_btype: btype_t

    (* predicate *)
    method is_read: bool
    method is_write: bool
    method is_immediate: bool
    method is_register: bool
    method is_pc_register: bool
    method is_double_register: bool
    method is_extension_register: bool
    method is_double_extension_register: bool
    method is_double_extension_register_list: bool
    method is_writeback_register: bool
    method is_special_register: bool
    method is_APSR_condition_flags: bool
    method is_register_list: bool
    method is_absolute_address: bool
    method is_literal_address: bool
    method is_pc_relative_address: bool
    method is_offset_address: bool
    method is_offset_address_writeback: bool
    method is_bit_sequence: bool

    method includes_pc: bool
    method includes_lr: bool

    (* i/o *)
    method toString: string
    method toPretty: pretty_t
  end


(** {1 Assembly opcodes}*)

type not_code_t = JumpTable of jumptable_int | DataBlock of data_block_int


(** Opcode condition codes *)
type arm_opcode_cc_t =
  | ACCEqual
  | ACCNotEqual
  | ACCCarrySet
  | ACCCarryClear
  | ACCNegative
  | ACCNonNegative
  | ACCOverflow
  | ACCNoOverflow
  | ACCUnsignedHigher
  | ACCNotUnsignedHigher
  | ACCSignedGE
  | ACCSignedLT
  | ACCSignedGT
  | ACCSignedLE
  | ACCAlways
  | ACCUnconditional


type arm_opc_encoding_type_t =
  | A1 | A2 | A3 | A4 | T1 | T2 | T3 | T4


type arm_opcode_encoding_t = {
    opc_encoding: arm_opc_encoding_type_t;
    opc_encoding_group: string option
  }


type arm_opcode_t =
  | Add of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * bool             (* T.W *)
  | AddCarry of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destionation *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * bool             (* T.W *)
  | Adr of
      arm_opcode_cc_t (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* imm: pc-relative address *)
  | AESInverseMixColumns of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* operand 1 *)
      * arm_operand_int  (* operand 2 *)
  | AESMixColumns of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* operand 1 *)
      * arm_operand_int  (* operand 2 *)
  | AESSingleRoundDecryption of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* operand 1 *)
      * arm_operand_int  (* operand 2 *)
  | AESSingleRoundEncryption of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* operand 1 *)
      * arm_operand_int  (* operand 2 *)
  | ArithmeticShiftRight of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: shift<0:7> *)
      * bool             (* T.W. *)
  | BitFieldClear of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * int              (* lsbit *)
      * int              (* width *)
      * int              (* msbit *)
  | BitFieldInsert of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source *)
      * int              (* lsbit *)
      * int              (* width *)
      * int              (* msbit *)
  | BitwiseAnd of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
      * bool             (* T.W. *)
  | BitwiseBitClear of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * bool             (* T.W. *)
  | BitwiseExclusiveOr of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * bool             (* T.W. *)
  | BitwiseNot of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm/imm: source *)
      * bool             (* T.W. *)
  | BitwiseOr of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
      * bool             (* T.W. *)
  | BitwiseOrNot of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
  | Branch of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
      * bool             (* T.W. *)
  | BranchExchange of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
  | BranchLink of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
  | BranchLinkExchange of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
  | Breakpoint of
      arm_operand_int    (* for debugger use *)
  | ByteReverseWord of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
      * bool             (* T.W *)
  | ByteReversePackedHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
      * bool             (* T.W. *)
  | ChangeProcessorState of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* cps effect *)
      * arm_operand_int  (* interrupt flags *)
      * int option       (* mode *)
      * bool             (* T.W *)
  | Compare of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * bool             (* T.W *)
  | CompareBranchNonzero of
      arm_operand_int    (* register *)
      * arm_operand_int  (* target address *)
  | CompareBranchZero of
      arm_operand_int    (* register *)
      * arm_operand_int  (* target address *)
  | CompareNegative of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* imm: source 2 *)
  | CountLeadingZeros of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
  | DataMemoryBarrier of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* dmb option *)
  | FLoadMultipleIncrementAfter of (* same VectorLoadMultipleIncrementAfter *)
      bool    (* writeback *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rl: register list *)
      * arm_operand_int  (* mem: multiple memory locations *)
  | FStoreMultipleIncrementAfter of (* same as VectorStoreMultipleIncrementAfter *)
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | IfThen of
      arm_opcode_cc_t    (* firstcond *)
      * string           (* <x><y><z> *)
  | LoadCoprocessor of
      bool               (* long *)
      * bool             (* ta2 *)
      * arm_opcode_cc_t  (* condition *)
      * int              (* coprocessor *)
      * int              (* CRd: coprocessor destination register *)
      * arm_operand_int  (* source location *)
      * int option       (* option *)
  | LoadMultipleDecrementAfter of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | LoadMultipleDecrementBefore of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | LoadMultipleIncrementAfter of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | LoadMultipleIncrementBefore of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | LoadRegister of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location*)
      * bool             (* T.W *)
  | LoadRegisterByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location*)
      * bool             (* T.W *)
  | LoadRegisterDual of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination 1 *)
      * arm_operand_int  (* rt2: destination 2 *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
      * arm_operand_int  (* mem2: second memory location *)
  | LoadRegisterExclusive of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
  | LoadRegisterHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
      * bool             (* T.W. *)
  | LoadRegisterSignedByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
      * bool             (* T.W. *)
  | LoadRegisterSignedHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
      * bool             (* T.W. *)
  | LogicalShiftLeft of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: shift<0:7> *)
      * bool             (* T.W *)
  | LogicalShiftRight of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: shift<0:7> *)
      * bool             (* T.W. *)
  | Move of
      bool (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rm/imm: source *)
      * bool            (* T.W *)
      * bool            (* Arm wide *)
  | MoveFromSpecialRegister of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* spec_reg: special register source *)
      * bool            (* privileged *)
  | MoveRegisterCoprocessor of
      arm_opcode_cc_t   (* condition *)
      * int             (* coprocessor *)
      * int             (* opc1 *)
      * arm_operand_int (* rt: destination register *)
      * int             (* CRn *)
      * int             (* CRm *)
      * int             (* opc2 *)
  | MoveToCoprocessor of
      arm_opcode_cc_t   (* condition *)
      * int             (* coprocessor *)
      * int             (* opc1 *)
      * arm_operand_int (* Rt *)
      * int             (* CRn *)
      * int             (* CRm *)
      * int             (* opc2 *)
  | MoveTop of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* imm: source *)
  | MoveToSpecialRegister of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* spec_reg: special register *)
      * arm_operand_int (* imm: constant *)
      * bool            (* privileged *)
  | MoveTwoRegisterCoprocessor of
      arm_opcode_cc_t   (* condition *)
      * int             (* coprocessor *)
      * int             (* opcode *)
      * arm_operand_int (* rt: destination 1 *)
      * arm_operand_int (* rt2: destination 2 *)
      * int             (* CRm *)
  | Multiply of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | MultiplyAccumulate of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * arm_operand_int  (* ra: accumulate *)
  | MultiplySubtract of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * arm_operand_int  (* ra: accumulate *)
  | Pop of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* stack pointer *)
      * arm_operand_int  (* register list *)
      * bool             (* T.W. *)
  | PreloadData of
      bool               (* preload for write *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* base register *)
      * arm_operand_int  (* address of memory referenced *)
  | Push of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* stack pointer *)
      * arm_operand_int  (* register list *)
      * bool             (* T.W. *)
  | ReverseBits of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
  | ReverseSubtract of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * bool             (* T.W. *)
  | ReverseSubtractCarry of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
  | RotateRight of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
      * bool             (* T.W. *)
  | RotateRightExtend of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
  | SaturatingAdd of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: first operand *)
      * arm_operand_int  (* rn: second operand *)
  | SaturatingDoubleAdd of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: first operand *)
      * arm_operand_int  (* rn: second operand *)
  | SaturatingDoubleSubtract of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: first operand *)
      * arm_operand_int  (* rn: second operand *)
  | SaturatingSubtract of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: first operand *)
      * arm_operand_int  (* rn: second operand *)
  | SelectBytes of
      arm_opcode_cc_t    (*condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: first operand *)
      * arm_operand_int  (* rm: second operand *)
  | SHA1FixedRotate of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vm: source *)
  | SHA1HashUpdateChoose of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vn: source 1 *)
      * arm_operand_int  (* vm: source 2 *)
  | SHA1HashUpdateMajority of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vn: source 1 *)
      * arm_operand_int  (* vm: source 2 *)
  | SHA1HashUpdateParity of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vn: source 1 *)
      * arm_operand_int  (* vm: source 2 *)
  | SHA1ScheduleUpdate0 of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vn: source 1 *)
      * arm_operand_int  (* vm: source 2 *)
  | SHA1ScheduleUpdate1 of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vn: source 1 *)
  | SHA256HashUpdatePart1 of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vn: source 1 *)
      * arm_operand_int  (* vm: source 2 *)
  | SHA256HashUpdatePart2 of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vn: source 1 *)
      * arm_operand_int  (* vm: source 2 *)
  | SHA256ScheduleUpdate0 of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vm: source *)
  | SHA256ScheduleUpdate1 of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* vd: destination *)
      * arm_operand_int  (* vn: source 1 *)
      * arm_operand_int  (* vm: source 2 *)
  | SignedBitFieldExtract of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source *)
  | SignedDivide of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: dividend *)
      * arm_operand_int  (* rn: divisor *)
  | SignedExtendByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
      * bool             (* T.W. *)
  | SignedExtendHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
      * bool             (* T.W. *)
  | SignedMostSignificantWordMultiply of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: first operand *)
      * arm_operand_int  (* rm: second operand *)
      * int              (* 0/1: multiplication is rounded *)
  | SignedMostSignificantWordMultiplyAccumulate of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: first operand *)
      * arm_operand_int  (* rm: second operand *)
      * arm_operand_int  (* ra: accumulation register *)
      * int              (* 0/1: multiplication is rounded *)
  | SignedMultiplyAccumulateBB of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * arm_operand_int  (* ra: accumulated value *)
  | SignedMultiplyAccumulateBT of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * arm_operand_int  (* ra: accumulated value *)
  | SignedMultiplyAccumulateTB of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * arm_operand_int  (* ra: accumulated value *)
  | SignedMultiplyAccumulateTT of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * arm_operand_int  (* ra: accumulated value *)
  | SignedMultiplyAccumulateLong of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rdlo *)
      * arm_operand_int  (* rdhi *)
      * arm_operand_int  (* rn *)
      * arm_operand_int  (* rm *)
  | SignedMultiplyAccumulateWordB of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * arm_operand_int  (* ra: accumulated value *)
  | SignedMultiplyAccumulateWordT of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
      * arm_operand_int  (* ra: accumulated value *)
  | SignedMultiplyHalfwordsBB of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | SignedMultiplyHalfwordsBT of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | SignedMultiplyHalfwordsTB of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | SignedMultiplyHalfwordsTT of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | SignedMultiplyLong of
      bool   (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rdlo: destination 1 *)
      * arm_operand_int (* rdhi: destination 2 *)
      * arm_operand_int (* rn: source 1 *)
      * arm_operand_int (* rm: source 2 *)
  | SignedMultiplyWordB of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rn: source 1 *)
      * arm_operand_int (* rm: source 2 (bottom half only) *)
  | SignedMultiplyWordT of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rn: source 1 *)
      * arm_operand_int (* rm: source 2 (top half only) *)
  | StoreCoprocessor of
      bool               (* long *)
      * bool             (* ta2 *)
      * arm_opcode_cc_t  (* condition *)
      * int              (* coprocessor *)
      * int              (* CRd: coprocessor source register *)
      * arm_operand_int  (* destination location *)
      * int option       (* option *)
  | StoreMultipleDecrementAfter of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | StoreMultipleDecrementBefore of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | StoreMultipleIncrementAfter of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
      * bool            (* T.W. *)
  | StoreMultipleIncrementBefore of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | StoreRegister of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
      * bool             (* T.W *)
  | StoreRegisterByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
      * bool             (* T.W. *)
  | StoreRegisterDual of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source 1 *)
      * arm_operand_int  (* rt2: source 2 *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immdiate *)
      * arm_operand_int  (* mem: memory location *)
      * arm_operand_int  (* mem2: second memory location *)
  | StoreRegisterExclusive of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: status *)
      * arm_operand_int  (* rt: source *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* mem: memory location *)
  | StoreRegisterHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory loction *)
      * bool             (* T.W. *)
  | Subtract of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
      * bool             (* T.W. *)
      * bool             (* Wide *)
  | SubtractCarry of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
      * bool             (* T.W *)
  | Swap of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt *)
      * arm_operand_int  (* rt2 *)
      * arm_operand_int  (* rn *)
      * arm_operand_int  (* mem *)
  | SwapByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt *)
      * arm_operand_int  (* rt2 *)
      * arm_operand_int  (* rn *)
      * arm_operand_int  (* mem *)
  | TableBranchByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn *)
      * arm_operand_int  (* rm *)
      * arm_operand_int  (* mem *)
  | TableBranchHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn *)
      * arm_operand_int  (* rm *)
      * arm_operand_int  (* mem *)
  | Test of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
      * bool             (* T.W. *)
  | TestEquivalence of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
  | UnsignedAdd8 of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: first operand *)
      * arm_operand_int  (* rm: second operand *)
  | UnsignedBitFieldExtract of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source *)
  | UnsignedDivide of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | UnsignedExtendAddByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | UnsignedExtendAddHalfword of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rn: source 1 *)
      * arm_operand_int (* rm: source 2 *)
  | UnsignedExtendByte of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
      * bool            (* T.W. *)
  | UnsignedExtendHalfword of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rm: source *)
      * bool            (* T.W. *)
  | UnsignedMultiplyAccumulateLong of
      bool   (* flags are set *)
      * arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* RdLo: destination *)
      * arm_operand_int (* RdHi: destination *)
      * arm_operand_int (* Rn: source 1 *)
      * arm_operand_int (* Rm: source 2 *)
  | UnsignedMultiplyLong of
      bool   (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rdlo: destination 1 *)
      * arm_operand_int (* rdhi: destination 2 *)
      * arm_operand_int (* rn: source 1 *)
      * arm_operand_int (* rm: source 2 *)
  | UnsignedSaturate of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* imm: source 1 *)
      * arm_operand_int (* rn: source 2 *)
  | UnsignedSaturatingSubtract8 of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rn: first operand *)
      * arm_operand_int (* rm: second operand *)
  | VectorAbsolute of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* datatype *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorAdd of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorAddLong of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorAddWide of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorBitwiseAnd of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorBitwiseBitClear of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* vd: destination *)
      * arm_operand_int (* vn: source 1 *)
      * arm_operand_int (* vm: source 2 *)
  | VectorBitwiseExclusiveOr of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorBitwiseNot of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorBitwiseOr of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorBitwiseOrNot of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorBitwiseSelect of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VCompare of
      bool   (* if true NaN operand causes invalid operation *)
      * arm_opcode_cc_t (* condition *)
      * vfp_datatype_t  (* element data type *)
      * arm_operand_int (* flagdestination: FPSCR *)
      * arm_operand_int (* operand 1 *)
      * arm_operand_int (* operand 2 *)
  | VectorConvert of
      bool   (* rounding specified *)
      * bool            (* involves fixed-point *)
      * arm_opcode_cc_t (* condition *)
      * vfp_datatype_t  (* destination data type *)
      * vfp_datatype_t  (* source data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
      * arm_operand_int (* number of fraction bits (fixed-point only) *)
  | VDivide of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorDuplicate of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* size *)
      * int             (* number of registers *)
      * int             (* number of elements *)
      * arm_operand_int (* floating-point destination register *)
      * arm_operand_int (* source register *)
  | VectorExtract of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
      * arm_operand_int (* imm *)
  | VectorFusedMultiplyAccumulate of
      arm_opcode_cc_t    (* condition *)
      * vfp_datatype_t   (* data type *)
      * arm_operand_int  (* destination *)
      * arm_operand_int  (* source 1 *)
      * arm_operand_int  (* source 2 *)
  | VectorLoadMultipleIncrementAfter of
      bool    (* writeback *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rl: register list *)
      * arm_operand_int  (* mem: multiple memory locations *)
  | VectorLoadOne of
      bool    (* writeback *)
      * arm_opcode_cc_t  (* condition *)
      * vfp_datatype_t   (* size *)
      * arm_operand_int  (* rl: register list *)
      * arm_operand_int  (* rn: base register *)
      * arm_operand_int  (* mem: multiple memory locations *)
      * arm_operand_int  (* rm: address offset applied after the access *)
  | VectorLoadFour of
      bool    (* writeback *)
      * arm_opcode_cc_t  (* condition *)
      * vfp_datatype_t   (* size *)
      * arm_operand_int  (* rl: register list *)
      * arm_operand_int  (* rn: base register *)
      * arm_operand_int  (* mem: multiple memory locations *)
      * arm_operand_int  (* rm: address offset applied after the access *)
  | VLoadRegister of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* floating-point destination register *)
      * arm_operand_int (* base register *)
      * arm_operand_int (* mem: memory location *)
  | VectorMoveDS of     (* VectorMove: one source, one destination *)
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorMoveDDSS of   (* VectorMove: two sources, two destinations *)
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination 1 *)
      * arm_operand_int (* destination 2 *)
      * arm_operand_int (* double-destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
      * arm_operand_int (* double-source *)
  | VectorMoveDSS of    (* VectorMove: two sources, one destination *)
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
      * arm_operand_int (* double-source *)
  | VectorMoveDDS of    (* VectorMove: two destinations, one source *)
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination 1 *)
      * arm_operand_int (* destination 2 *)
      * arm_operand_int (* double-destination *)
      * arm_operand_int (* source *)
  | VectorMoveLong of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* size *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorMoveNarrow of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* size *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VMoveRegisterStatus of   (* VMRS *)
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VMoveToSystemRegister of (* VMSR *)
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorMultiply of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorMultiplyAccumulate of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorMultiplyAccumulateLong of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorMultiplyLong of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorMultiplySubtract of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorNegate of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorNegateMultiply of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorNegateMultiplyAccumulate of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorNegateMultiplySubtract of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorPop of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* stack pointer *)
      * arm_operand_int (* list of extension register *)
      * arm_operand_int (* memory *)
  | VectorPush of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* stack pointer *)
      * arm_operand_int (* list of extension registers *)
      * arm_operand_int (* memory *)
  | VectorReverseDoublewords of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorReverseHalfwords of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorReverseWords of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorRoundingHalvingAdd of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorRoundingShiftRightAccumulate of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source register *)
      * arm_operand_int (* source immediate *)
  | VectorShiftLeft of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source register *)
      * arm_operand_int (* source immediate / source register *)
  | VectorShiftLeftInsert of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source register *)
      * arm_operand_int (* source immediate *)
  | VectorShiftRight of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source register *)
      * arm_operand_int (* source immediate *)
  | VectorShiftRightInsert of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source register *)
      * arm_operand_int (* source immediate *)
  | VectorShiftRightAccumulate of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source register *)
      * arm_operand_int (* source immediate *)
  | VectorShiftRightNarrow of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source register *)
      * arm_operand_int (* source immediate *)
  | VStoreRegister of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* floating-point source register *)
      * arm_operand_int (* base register *)
      * arm_operand_int (* mem: memory location *)
  | VectorStoreMultipleDecrementBefore of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | VectorStoreMultipleIncrementAfter of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
  | VectorStoreOne of
      bool    (* writeback *)
      * arm_opcode_cc_t  (* condition *)
      * vfp_datatype_t   (* size *)
      * arm_operand_int  (* rl: register list *)
      * arm_operand_int  (* rn: base register *)
      * arm_operand_int  (* mem: multiple memory locations *)
      * arm_operand_int  (* rm: address offset applied after the access *)
  | VectorStoreTwo of
      bool    (* writeback *)
      * arm_opcode_cc_t  (* condition *)
      * vfp_datatype_t   (* size *)
      * arm_operand_int  (* rl: register list *)
      * arm_operand_int  (* rn: base register *)
      * arm_operand_int  (* mem: multiple memory locations *)
      * arm_operand_int  (* rm: address offset applied after the access *)
  | VectorStoreFour of
      bool    (* writeback *)
      * arm_opcode_cc_t  (* condition *)
      * vfp_datatype_t   (* size *)
      * arm_operand_int  (* rl: register list *)
      * arm_operand_int  (* rn: base register *)
      * arm_operand_int  (* mem: multiple memory locations *)
      * arm_operand_int  (* rm: address offset applied after the access *)
  | VectorSubtract of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorTableLookup of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* extension register list *)
      * arm_operand_int (* index vector *)
  | VectorTranspose of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* size *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorZip of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* dst/src *)
      * arm_operand_int (* dst/src *)

  (* SupervisorType *)
  | SupervisorCall of arm_opcode_cc_t * arm_operand_int

  (* Misc *)
  | OpInvalid
  | PermanentlyUndefined of arm_opcode_cc_t * arm_operand_int
  | NoOperation of arm_opcode_cc_t (* condition *)
  | NotRecognized of string * doubleword_int
  | OpcodeUndefined of string
  | OpcodeUnpredictable of string
  | NotCode of not_code_t option


(** {1 Opcode Dictionary}*)

class type arm_dictionary_int =
  object

    method index_vfp_datatype: vfp_datatype_t -> int
    method index_register_shift_rotate: register_shift_rotate_t -> int
    method index_arm_memory_offset: arm_memory_offset_t -> int
    method index_arm_simd_writeback: arm_simd_writeback_t -> int
    method index_arm_simd_list_element: arm_simd_list_element_t -> int
    method index_arm_opkind: arm_operand_kind_t -> int
    method index_arm_operand: arm_operand_int -> int
    method index_arm_opcode: arm_opcode_t -> int
    method index_arm_bytestring: string -> int

    method retrieve_arm_opcode_key: int -> (string list * int list)

    method write_xml_arm_bytestring:
             ?tag:string -> xml_element_int -> string -> unit
    method write_xml_arm_opcode:
             ?tag:string -> xml_element_int -> arm_opcode_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

(** {1 Assembly code}*)

class type arm_assembly_instruction_int =
  object
    (* setters *)
    method set_block_entry: unit
    method set_inlined_call: unit
    method set_block_condition: unit
    method set_condition_covered_by: doubleword_int -> unit
    method set_aggregate_entry: unit
    method set_aggregate_exit: unit
    method set_aggregate_anchor: unit
    method set_in_aggregate: doubleword_int -> unit

    (* accessors *)
    method get_address: doubleword_int
    method get_opcode: arm_opcode_t
    method get_instruction_bytes: string
    method get_bytes_ashexstring: string
    method get_non_code_block: not_code_t
    method condition_covered_by: doubleword_int

    (* predicates *)
    method is_arm32: bool
    method is_block_entry: bool
    method is_inlined_call: bool
    method is_valid_instruction: bool
    method is_non_code_block: bool
    method is_not_code: bool
    method is_block_condition: bool  (* IT turned into conditional jump *)
    method is_condition_covered: bool  (* condition covered by IT cond. jump *)
    method is_in_aggregate: doubleword_int option
    method is_aggregate_entry: bool
    method is_aggregate_exit: bool
    method is_aggregate_anchor: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString: string
    method toPretty: pretty_t

  end


type arm_assembly_instruction_result = arm_assembly_instruction_int traceresult


type thumb_it_sequence_kind_t =
  (** in [inverse, dstop], [inverse] indicates whether the predicate itself
      or its inverse is to be assigned; [dstop] is the destination operand
      for the predicate assignment.

      The destination operand [dstop] is assumed to be a register.
   *)
  | ITPredicateAssignment of bool * arm_operand_int


class type thumb_it_sequence_int =
  object
    (* accessors *)
    method kind: thumb_it_sequence_kind_t
    method instrs: arm_assembly_instruction_int list
    method anchor: doubleword_int

    (* translation *)
    method toCHIF: cmd_t list

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString: string
    method toPretty: pretty_t
  end


class type arm_jumptable_int =
  object
    (* accessors *)
    method target_addrs: doubleword_int list
    method default_target: doubleword_int
    method indexed_targets: (doubleword_int * int list) list
    method start_address: doubleword_int
    method end_address: doubleword_int

    (* conversion *)
    method to_jumptable: jumptable_int

    (* translation *)
    method toCHIF: doubleword_int -> cmd_t list

    (* predicates *)
    method has_offset_table: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


type arm_aggregate_kind_t =
  | ARMJumptable of arm_jumptable_int
  | ThumbITSequence of thumb_it_sequence_int


class type arm_instruction_aggregate_int =
  object
    method kind: arm_aggregate_kind_t
    method instrs: arm_assembly_instruction_int list
    method addrs: doubleword_int list
    method anchor: arm_assembly_instruction_int
    method entry: arm_assembly_instruction_int
    method exitinstr: arm_assembly_instruction_int
    method jumptable: arm_jumptable_int
    method it_sequence: thumb_it_sequence_int

    (* translation *)
    method toCHIF: doubleword_int -> cmd_t list

    (* predicates *)
    method is_jumptable: bool
    method is_it_sequence: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toPretty: pretty_t
  end


(** Represents the number of callsites that, resp., support, contradict,
    and are neutral about on the predicate. *)
type callsite_result_t = int * int * int


class type arm_callsite_record_int =
  object
    (* accessors *)
    method callsite: doubleword_int
    method pre_instrs: arm_assembly_instruction_int list
    method post_instrs: arm_assembly_instruction_int list
    method postblock_instr: arm_assembly_instruction_int

    (* predicates *)
    method has_returnvalue_compare: bool
    method has_returnvalue_move: bool
    method has_returnvalue_compute: bool
    method has_returnvalue_clobber: bool
    method has_fnentry_successor: bool
    method has_nop_successor: bool

    method toPretty: pretty_t
  end


class type arm_callsites_record_int =
  object
    (* setters *)
    method add_callsite:
             doubleword_int
             -> arm_assembly_instruction_int list
             -> arm_assembly_instruction_int list
             -> arm_assembly_instruction_int
             -> unit

    (* accessors *)
    method target_address: doubleword_int
    method callsites: arm_callsite_record_int list

    (* predicates *)
    method is_returning: callsite_result_t
    method is_returnvalue_used: callsite_result_t
    method is_non_returning: callsite_result_t
    method is_returnvalue_clobbered: callsite_result_t

    method toPretty: pretty_t
  end


class type arm_callsites_records_int =
  object
    (* setters *)
    method add_callsite:
             doubleword_int
             -> doubleword_int
             -> arm_assembly_instruction_int list
             -> arm_assembly_instruction_int list
             -> arm_assembly_instruction_int
             -> unit

    (* accessors *)
    method get_non_returning_functions: doubleword_int list

    (* predicates *)
    method is_returning: doubleword_int -> callsite_result_t
    method is_returnvalue_used: doubleword_int -> callsite_result_t
    method is_non_returning: doubleword_int -> callsite_result_t
    method is_returnvalue_clobbered: doubleword_int -> callsite_result_t

    method summary_to_pretty: pretty_t
    method toPretty: pretty_t
  end


class type arm_assembly_instructions_int =
  object

    (* setters *)

    method set_instruction:
             doubleword_int -> arm_assembly_instruction_int -> unit

    (** [set_not_code lst] marks the addresses contained within the data blocks
        in [lst] as [NotCode]. Data blocks whose start or end address lie outside
        the declared code space are ignored (an error message is logged for these
        blocks).*)
    method set_not_code: data_block_int list -> unit

    (** [set_aggregate va agg] records the presence of aggregate semantic unit
        [agg] at virtual address [va], and marks the participating assembly
        instructions accordingly. If the aggregate is a jumptable, and the
        jumptable addresses or offsets are located within the code space, these
        locations are marked as [NotCode].*)
    method set_aggregate: doubleword_int -> arm_instruction_aggregate_int -> unit

    method collect_callsites: unit

    (* accessors *)

    (** Return the length of code space (in bytes).*)
    method length: int

    (** [get_instruction va] returns the instruction located at virtual address
        [va]. If no instruction has been entered yet, a new instruction, with
        opcode [OpInvalid] is assigned and returned. If [va] is out-of-range
        an Error result is returned. *)
    method get_instruction: doubleword_int -> arm_assembly_instruction_result

    (** [get_code_addresses_rev low high] returns the list of virtual addresses
        bounded by [low] and [high] that hold valid instructions.
        [low] defaults to [0x0], [high] defaults to [0xffffffff] *)
    method get_code_addresses:
             ?low:doubleword_int
             -> ?high:doubleword_int
             -> unit
             -> doubleword_int list

    method get_jumptables: (doubleword_int * arm_jumptable_int) list

    (** [get_next_valid_instruction_address va] returns the least virtual
        address strictly larger than [va] with a valid assembly instruction.
        If no such address exists, or if [va] is out-of-range, Error is
        returned.*)
    method get_next_valid_instruction_address:
             doubleword_int -> doubleword_int traceresult

    method get_prev_valid_instruction_address:
             doubleword_int -> doubleword_int traceresult

    method get_aggregate: doubleword_int -> arm_instruction_aggregate_int

    (** Return the number of valid instructions in the code space.*)
    method get_num_instructions: int

    (** Return the number of valid instructions in the code space with unknown
        opcode.*)
    method get_num_unknown_instructions: int

    (* iterators *)
    (* method iteri: (int -> arm_assembly_instruction_int -> unit) -> unit *)
    method itera: (doubleword_int -> arm_assembly_instruction_int -> unit) -> unit

    (* predicates *)

    (** [is_code_address va] returns true if [va] is a virtual address within
        the code space and if the address holds a valid assembly instruction
        (i.e., it is the starting address of an assembly instruction). *)
    method is_code_address: doubleword_int -> bool

    (** [has_next_valid_instruction va] returns true if [va] is a virtual address
        within the code and there exists a virtual address with a valid instruction
        that is strictly larger than [va].*)
    method has_next_valid_instruction: doubleword_int -> bool
    method has_aggregate: doubleword_int -> bool

    method has_prev_valid_instruction: doubleword_int -> bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString:
             ?datarefs:((string * arm_assembly_instruction_int list) list)
             -> ?filter:(arm_assembly_instruction_int -> bool)
             -> unit
             -> string

  end


class type arm_assembly_block_int =
  object

    (* accessors *)

    (** Return the address of the function to which this block belongs. If this
        block is part of an inlined function, the address of the address of the
        orginal function is returned (the inner function), not the address of
        the function in which the block is inlined.*)
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

    (** [get_instructions_rev high] returns the list of instructions in this
        block from the instruction at the first address to the instruction
        at address [high] or the last address, whichever is smaller, in reverse
        order. [high] defaults to the last address *)
    method get_instructions_rev:
             ?high:doubleword_int
             -> unit
             -> arm_assembly_instruction_int list

    (** Return the list of instructions contained in this basic block.*)
    method get_instructions: arm_assembly_instruction_int list

    (** Return the successors of this block, including blocks of the inlining
        function if this block is part of an inlined function.*)
    method get_successors: ctxt_iaddress_t list

    (** [get_instruction va] returns the instruction at address [va].

        Raises an exception if [va] is not within this block, or if [va] does
        not have a valid instruction.*)
    method get_instruction: doubleword_int -> arm_assembly_instruction_int

    (** Return the bytes that make up the instructions of this block as a string
        of hexadecimial characters.*)
    method get_bytes_as_hexstring: string

    (** Return the number of instructions in this basic block.*)
    method get_instruction_count: int

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool
    method has_conditional_return_instr: bool
    method is_returning: bool

    (* iterators *)
    method itera:
             ?low:doubleword_int
             -> ?high:doubleword_int
             -> ?reverse:bool
             -> (ctxt_iaddress_t -> arm_assembly_instruction_int -> unit)
             -> unit

    (* i/o *)
    method toString: string
    method toPretty: pretty_t

  end


class type arm_assembly_function_int =
  object

    (* accessors *)
    method get_address: doubleword_int
    method get_blocks: arm_assembly_block_int list
    method get_cfg_edges: (ctxt_iaddress_t * ctxt_iaddress_t) list
    method get_block: ctxt_iaddress_t -> arm_assembly_block_int
    method get_instruction: doubleword_int -> arm_assembly_instruction_int
    method get_jumptables: (doubleword_int * arm_jumptable_int) list
    method get_bytes_as_hexstring: string
    method get_function_md5: string
    method get_instruction_count: int
    method get_block_count: int
    method get_not_valid_instr_count: int

    (* iterators *)
    method iter: (arm_assembly_block_int -> unit) -> unit
    method itera: (ctxt_iaddress_t -> arm_assembly_block_int -> unit) -> unit
    method iteri:
             (doubleword_int
              -> ctxt_iaddress_t
              -> arm_assembly_instruction_int
              -> unit)
             -> unit
    method populate_callgraph: callgraph_int -> unit

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool
    method has_conditional_return: bool

    (* i/o *)
    method toPretty: pretty_t

  end


class type arm_assembly_functions_int =
  object

    (* reset *)
    method reset: unit

    (* setters *)
    method add_function: arm_assembly_function_int -> unit
    method add_functions_by_preamble: doubleword_int list
    method remove_function: doubleword_int -> unit

    method set_datablocks: unit
    method identify_datablocks: unit
    method identify_dataref_datablocks: unit

    (* accessors *)
    method get_callgraph: callgraph_int
    method get_functions: arm_assembly_function_int list
    method get_function: dw_index_t -> arm_assembly_function_int
    method get_function_by_address: doubleword_int -> arm_assembly_function_int
    method get_function_coverage:
             int     (* coverage *)
             * int   (* overlap *)
             * int   (* multiplicity *)
    method get_num_functions: int

    (** Returns a map of virtual addresses in a code section to lists of
        instructions that load the contents of the corresponding memory
        locations.*)
    method get_data_references:
             (string * arm_assembly_instruction_int list) list

    (* iterators *)
    method iter: (arm_assembly_function_int -> unit) -> unit
    method itera: (doubleword_int -> arm_assembly_function_int -> unit) -> unit
    method bottom_up_itera:
             (doubleword_int -> arm_assembly_function_int -> unit) -> unit
    method top_down_itera:
             (doubleword_int -> arm_assembly_function_int -> unit) -> unit

    (* predicates *)
    method has_function_by_address: doubleword_int -> bool
    method includes_instruction_address: doubleword_int -> bool

    (* i/o *)
    method dark_matter_to_string: string
    method duplicates_to_string: string

  end


(** {1 CHIF translation}*)

class type arm_code_pc_int =
  object

    (* accessors *)
    method get_next_instruction: ctxt_iaddress_t * arm_assembly_instruction_int
    method get_block_successors: ctxt_iaddress_t list
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


class type arm_chif_system_int =
  object

    (* reset *)
    method reset: unit

    (* setters *)
    method add_arm_procedure: procedure_int -> unit
    method add_arm_definitions_procedure: procedure_int -> unit

    (* accessors *)
    method get_arm_system: system_int
    method get_arm_procedure_names: symbol_t list
    method get_arm_procedure: doubleword_int -> procedure_int

    (* predicates *)
    method has_arm_procedure: doubleword_int -> bool
  end


(** {1 Analysis results}*)

class type arm_opcode_dictionary_int =
  object

    method index_sp_offset: int * interval_t -> int

    (** [index_instr instr floc] indexes the variable locations and
        invariant expressions associated with the arguments of [instr],
        made accessible via the function location [floc].*)
    method index_instr:
             arm_assembly_instruction_int
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
             -> arm_assembly_instruction_int
             -> floc_int
             -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t
  end


class type arm_fn_type_constraints_int =
  object

    method record_type_constraints: unit

  end


class type arm_analysis_results_int =
  object
    method record_results: ?save:bool -> arm_assembly_function_int -> unit
    method write_xml: xml_element_int -> unit
    method save: unit
  end


(** {1 Test support}*)

(** Support for servicing data to unit tests.

    Unit tests sometimes need access to data that is produced as part of the
    disassembly, function construction, or analysis, but that is not easily
    made available directly as part of the functions called by the unit test
    itself. This data structure allows a unit test to request a particular
    type of data, which will then be submitted in the course of the functions
    called and can afterwards be retrieved here by the unit test for inspection
    and comparison.
*)
class type testsupport_int =
  object

    (** {1 Instrx data}
        Instrx data submitted is identified by the address of the instruction.
        Submission is via doubleword, retrieval is via hex address.*)

    method request_instrx_data: unit
    method requested_instrx_data: bool
    method submit_instrx_data:
             doubleword_int -> variable_t list -> xpr_t list -> unit
    method retrieve_instrx_data:
             string -> (variable_t list * xpr_t list) traceresult

    (** {1 Instrx tags}
        Instrx tags submitted is identified by the address of the instruction.
        Submission is via doubleword, retrieval is via hex address.*)

    method request_instrx_tags: unit
    method requested_instrx_tags: bool
    method submit_instrx_tags: doubleword_int -> string list -> unit
    method retrieve_instrx_tags: string -> (string list) traceresult

    (** {1 CHIF condition exprs}
        CHIF condition expressions are submitted with the conditional
        jump instruction, the test setting instruction, and the
        expressions that are converted to CHIF. They are retrieved using
        the hex address of the conditional jump instruction.*)

    method request_chif_conditionxprs: unit
    method requested_chif_conditionxprs: bool
    method submit_chif_conditionxprs:
             arm_assembly_instruction_int
             -> arm_assembly_instruction_int
             -> xpr_t list
             -> unit
    method retrieve_chif_conditionxprs:
             string
             -> (arm_assembly_instruction_int
                 * arm_assembly_instruction_int
                 * xpr_t list) traceresult

    (** {1 ARM conditional exprs}
        ARM conditional expressions are the expressions constructed from a
        combination of a condition code and a test. They are submiited with
        the instruction that consumes the resulting predicate, the instruction
        that provides the test, and the (optional) expression generated. They
        are retrieved using the hex address of the instruction that consumes
        the predicate.*)

    method request_arm_conditional_expr: unit
    method requested_arm_conditional_expr: bool
    method submit_arm_conditional_expr:
             arm_assembly_instruction_int
             -> arm_assembly_instruction_int
             -> xpr_t option
             -> unit
    method retrieve_arm_conditional_expr:
             string
             -> (arm_assembly_instruction_int
                 * arm_assembly_instruction_int
                 * xpr_t option) traceresult

  end

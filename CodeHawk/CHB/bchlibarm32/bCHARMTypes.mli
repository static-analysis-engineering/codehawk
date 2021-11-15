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
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

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
  | ARMReg of arm_reg_t
  | ARMWritebackReg of
      bool  (* true if part of single memory access *)
      * arm_reg_t  (* base register *)
      * int option (* increment/decrement in bytes of base register value *)
  | ARMSpecialReg of arm_special_reg_t
  | ARMExtensionReg of arm_extension_register_t
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
      arm_reg_t
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
    method get_register_count: int
    method get_register_list: arm_reg_t list
    method get_register_op_list: 'a list
    method get_extension_register_op_list: 'a list
    method get_absolute_address: doubleword_int
    method get_literal_address: doubleword_int
    method get_pc_relative_address: doubleword_int -> int -> doubleword_int

    (* converters *)
    method to_numerical: numerical_t
    method to_address: floc_int -> xpr_t
    method to_variable: floc_int -> variable_t
    method to_multiple_variable: floc_int -> variable_t list
    method to_expr: floc_int -> xpr_t
    method to_multiple_expr: floc_int -> xpr_t list
    method to_lhs: floc_int -> variable_t * cmd_t list
    method to_multiple_lhs: floc_int -> variable_t list * cmd_t list
    method to_updated_offset_address: floc_int -> xpr_t

    (* predicate *)
    method is_read: bool
    method is_write: bool
    method is_immediate: bool
    method is_register: bool
    method is_writeback_register: bool
    method is_special_register: bool
    method is_register_list: bool
    method is_absolute_address: bool
    method is_pc_relative_address: bool
    method is_offset_address_writeback: bool

    method includes_pc: bool

    (* i/o *)
    method toString: string
    method toPretty: pretty_t
  end


type not_code_t = JumpTable of jumptable_int | DataBlock of data_block_int  


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
      arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* imm: source *)
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
  | RotateRightExtend of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
  | SelectBytes of
      arm_opcode_cc_t    (*condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: first operand *)
      * arm_operand_int  (* rm: second operand *)
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
  | SignedMultiplyAccumulateLong of
      bool  (* flags are set *)
      * arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rdlo *)
      * arm_operand_int  (* rdhi *)
      * arm_operand_int  (* rn *)
      * arm_operand_int  (* rm *)
  | SignedMultiplyLong of
      bool   (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rdlo: destination 1 *)
      * arm_operand_int (* rdhi: destination 2 *)
      * arm_operand_int (* rn: source 1 *)
      * arm_operand_int (* rm: source 2 *)
  | SingleBitFieldExtract of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source *)
  | StoreMultipleDecrementBefore of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
      * bool            (* T.W. *)
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
      * bool            (* T.W. *)
  | StoreRegister of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* mem: memory location *)
      * bool             (* T.W *)
  | StoreRegisterByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source *)
      * arm_operand_int  (* rn: base *)
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
      * arm_operand_int  (* mem *)
  | SwapByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt *)
      * arm_operand_int  (* rt2 *)
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
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
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
  | UnsignedSaturatingSubtract8 of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rn: first operand *)
      * arm_operand_int (* rm: second operand *)
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
  | VectorBitwiseBitClear of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* source / destination *)
      * arm_operand_int (* immediate *)
  | VectorBitwiseExclusiveOr of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VectorBitwiseOr of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)
  | VCompare of
      bool   (* if true NaN operand causes invalid operation *)
      * arm_opcode_cc_t (* condition *)
      * vfp_datatype_t  (* element data type *)
      * arm_operand_int (* operand 1 *)
      * arm_operand_int (* operand 2 *)
  | VectorConvert of
      bool   (* rounding specified *)
      * arm_opcode_cc_t (* condition *)
      * vfp_datatype_t  (* destination data type *)
      * vfp_datatype_t  (* source data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
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
  | VLoadRegister of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* floating-point destination register *)
      * arm_operand_int (* base register *)
      * arm_operand_int (* mem: memory location *)
  | VectorMove of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* element data type *)
      * arm_operand_int list (* destination(s) / source(s) *)
  | VectorMoveLong of
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
  | VectorNegate of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | VectorPush of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* stack pointer *)
      * arm_operand_int (* list of extension registers *)
      * arm_operand_int (* memory *)
  | VectorRoundingShiftRightAccumulate of
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
  | VStoreRegister of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* floating-point source register *)
      * arm_operand_int (* base register *)
      * arm_operand_int (* mem: memory location *)
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
  | VectorSubtract of
      arm_opcode_cc_t   (* condition *)
      * vfp_datatype_t  (* data type *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source 1 *)
      * arm_operand_int (* source 2 *)

  (* SupervisorType *)
  | SupervisorCall of arm_opcode_cc_t * arm_operand_int
  (* Misc *)
  | OpInvalid
  | PermanentlyUndefined of arm_opcode_cc_t * arm_operand_int
  | NoOperation of arm_opcode_cc_t (* condition *)
  | NotRecognized of string * doubleword_int
  | NotCode of not_code_t option


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
    (* method index_arm_instr_class: arm_instr_class_t -> int *)

    method write_xml_arm_bytestring:
             ?tag:string -> xml_element_int -> string -> unit
    method write_xml_arm_opcode:
             ?tag:string -> xml_element_int -> arm_opcode_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end


class type arm_assembly_instruction_int =
  object
    (* setters *)
    method set_block_entry: unit
    method set_inlined_call: unit
    method set_aggregate: arm_operand_int -> doubleword_int list -> unit
    method set_subsumed: unit

    (* accessors *)
    method get_address: doubleword_int
    method get_opcode: arm_opcode_t
    method get_instruction_bytes: string
    method get_bytes_ashexstring: string
    method get_non_code_block: not_code_t
    method get_aggregate_dst: arm_operand_int

    (* predicates *)
    method is_arm32: bool
    method is_block_entry: bool
    method is_inlined_call: bool
    method is_valid_instruction: bool
    method is_non_code_block: bool
    method is_not_code: bool
    method is_aggregate: bool
    method is_subsumed: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString: string
    method toPretty: pretty_t

  end


class type arm_assembly_instructions_int =
  object

    (* setters *)
    method set: int -> arm_assembly_instruction_int -> unit
    method set_not_code: data_block_int list -> unit
    method set_jumptables: jumptable_int list -> unit

    (* accessors *)
    method length: int
    method at_index: int -> arm_assembly_instruction_int
    method at_address: doubleword_int -> arm_assembly_instruction_int
    method get_code_addresses_rev:
             ?low:doubleword_int
             -> ?high:doubleword_int
             -> unit
             -> doubleword_int list
    method get_next_valid_instruction_address: doubleword_int -> doubleword_int
    method get_num_instructions: int
    method get_num_unknown_instructions: int

    (* iterators *)
    method iteri: (int -> arm_assembly_instruction_int -> unit) -> unit
    method itera: (doubleword_int ->arm_assembly_instruction_int -> unit) -> unit

    (* predicates *)
    method is_code_address: doubleword_int -> bool
    method has_next_valid_instruction: doubleword_int -> bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString:
             ?filter:(arm_assembly_instruction_int -> bool) -> unit -> string

  end


class type arm_assembly_block_int =
  object

    (* accessors *)
    method get_faddr: doubleword_int
    method get_first_address: doubleword_int
    method get_location: location_int
    method get_context: context_t list
    method get_context_string: ctxt_iaddress_t
    method get_last_address: doubleword_int
    method get_instructions_rev:
             ?high:doubleword_int
             -> unit
             -> arm_assembly_instruction_int list
    method get_instructions: arm_assembly_instruction_int list
    method get_successors: ctxt_iaddress_t list
    method get_instruction: doubleword_int -> arm_assembly_instruction_int
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
    method get_block: ctxt_iaddress_t -> arm_assembly_block_int
    method get_instruction: doubleword_int -> arm_assembly_instruction_int
    method get_bytes_as_hexstring: string
    method get_function_md5: string
    method get_instruction_count: int
    method get_block_count: int

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

    (* accessors *)
    method get_arm_system: system_int
    method get_arm_procedure_names: symbol_t list
    method get_arm_procedure: doubleword_int -> procedure_int

    (* predicates *)
    method has_arm_procedure: doubleword_int -> bool
  end


class type arm_opcode_dictionary_int =
  object

    method index_sp_offset: int * interval_t -> int
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


class type arm_analysis_results_int =
  object
    method record_results: ?save:bool -> arm_assembly_function_int -> unit
    method write_xml: xml_element_int -> unit
    method save: unit
  end

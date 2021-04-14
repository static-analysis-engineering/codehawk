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

type register_shift_rotate_t =
  | ARMImmSRT of shift_rotate_type_t * int    (* immediate shift amount *)
  | ARMRegSRT of shift_rotate_type_t * arm_reg_t (* shift amount in reg *)

type arm_memory_offset_t =
  | ARMImmOffset of int
  | ARMIndexOffset of arm_reg_t
  | ARMShiftedIndexOffset of arm_reg_t * register_shift_rotate_t

type arm_instr_class_t =
  | DataProcRegType of    (* 27:25 000 *)
      int   (* 31:28 - cond *)
      * int (* 24:21 - op *)
      * int (* 20    - opx *)
      * int (* 19:16 - Rn/Rd/RdHi *)
      * int (* 15:12 - Rd/RdLo *)
      * int (* 11:8  - Rs/shift *)
      * int (* 7       opy *)
      * int (* 6:5   - shift *)
      * int (* 4     - register/shifted register *)
      * int (* 3:0   - Rm *)
  | DataProcImmType of    (* 27:25 001 *)
      int   (* 31:28 - cond *)
      * int (* 24:21 - op *)
      * int (* 20    - opx *)
      * int (* 19:16 - Rn/field mask *)
      * int (* 15:12 - Rd/SBZ *)
      * int (* 11:8  - rotate *)
      * int (* 7:0   - immediate *)
  | LoadStoreImmType of   (* 27:25 010 *)
      int   (* 31:28 - cond *)
      * int (* 24    - P *)
      * int (* 23    - U *)
      * int (* 22    - opx *)
      * int (* 21    - W *)
      * int (* 20    - opy *)
      * int (* 19:16 - Rn *)
      * int (* 15:12 - Rd *)
      * int (* 11:0  - immediate *)
  | LoadStoreRegType of    (* 27:25 011, 4 0 *)
      int   (* 31:28 - cond *)
      * int (* 24    - P *)
      * int (* 23    - U *)
      * int (* 22    - opx *)
      * int (* 21    - W *)
      * int (* 20    - opy *)
      * int (* 19:16 - Rn *)
      * int (* 15:12 - Rd *)
      * int (* 11:7  - shiftimm *)
      * int (* 6:5   - shift *)
      * int (* 4     - opz *)
      * int (* 3:0   - Rm *)
  | MediaType of         (* 27:25 011, 4 1 *)
      int   (* 31:28 - cond *)
      * int (* 24:20 - op1 *)
      * int (* 19:16 - data1 *)
      * int (* 15:12 - Rd *)
      * int (* 11:8  - data2 *)
      * int (* 7:5   - op2 *)
      * int (* 3:0   - Rn *)
  | BlockDataType of     (* 27:25 100 *)
      int   (* 31:28 - cond *)
      * int (* 24    - P *)
      * int (* 23    - U *)
      * int (* 22    - opx *)
      * int (* 21    - W *)
      * int (* 20    - opy *)
      * int (* 19:16 - Rn *)
      * int (* 15    - opz *)
      * int (* 14:0  - register list *)
  | BranchLinkType of    (* 27:25 101 *)
      int   (* 31:28 - cond *)
      * int (* 24    - opx *)
      * int (* 23:0  - offset *)
  | SupervisorType of    (* 27:24 1111 *)
      int   (* 31:28 - cond *)
      * int (* 23:0  - svc index *)
  | LoadStoreCoprocType of (* 27:25 110 *)
      int   (* 31:28 - cond *)
      * int (* 24    - P *)
      * int (* 23    - U *)
      * int (* 22    - N *)
      * int (* 21    - W *)
      * int (* 20    - op *)
      * int (* 19:16 - Rn *)
      * int (* 15:12 - CRd *)
      * int (* 11:8  - cp_num *)
      * int (* 7:0   - immediate *)
  | CoprocessorType of   (* 27:24 11xx *)
      int   (* 31:28 - cond *)
      * int (* 25:24 - op *)
      * int (* 23:21 - op1 *)
      * int (* 20    - opx *)
      * int (* 19:16 - CRn *)
      * int (* 15:12 - CRd *)
      * int (* 11:8  - cp_num *)
      * int (* 7:5   - op2 *)
      * int (* 4     - opy *)
      * int (* 3:0   - CRm *)
  | UnconditionalType of  (* 31:28 1111 *)
      int   (* 27:20 - op1 *)
      * int (* 19:16 - Rn *)
      * int (* 15:5  - data *)
      * int (* 4     - op *)
      * int (* 3:0   - datax *)

type arm_operand_kind_t =
  | ARMReg of arm_reg_t
  | ARMRegList of arm_reg_t list
  | ARMShiftedReg of arm_reg_t * register_shift_rotate_t
  | ARMRegBitSequence of arm_reg_t * int * int (* lsb, widthm1 *)
  | ARMImmediate of immediate_int
  | ARMAbsolute of doubleword_int
  | ARMMemMultiple of arm_reg_t * int  (* number of locations *)
  | ARMOffsetAddress of
      arm_reg_t                  (* base register *)
      * arm_memory_offset_t      (* offset *)
      * bool                     (* isadd *)
      * bool                     (* iswback *)
      * bool                     (* isindex *)

type arm_operand_mode_t = RD | WR | RW

class type arm_operand_int =
  object ('a)

    (* accessors *)
    method get_kind: arm_operand_kind_t
    method get_mode: arm_operand_mode_t
    method get_register: arm_reg_t
    method get_register_count: int
    method get_register_list: arm_reg_t list
    method get_absolute_address: doubleword_int
    method get_pc_relative_address: doubleword_int -> doubleword_int

    (* converters *)
    method to_numerical: numerical_t
    method to_address: floc_int -> xpr_t
    method to_variable: floc_int -> variable_t
    method to_multiple_variable: floc_int -> variable_t list
    method to_expr: floc_int -> xpr_t
    method to_multiple_expr: floc_int -> xpr_t list
    method to_lhs: floc_int -> variable_t * cmd_t list

    (* predicate *)
    method is_read: bool
    method is_write: bool
    method is_immediate: bool
    method is_register: bool
    method is_register_list: bool
    method is_absolute_address: bool
    method is_pc_relative_address: bool

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
  | BitwiseAnd of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
  | BitwiseBitClear of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | BitwiseExclusiveOr of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
  | BitwiseNot of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm/imm: source *)
  | BitwiseOr of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
  | Branch of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
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
  | Compare of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
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
      * arm_operand_int  (* mem: memory location*)
      * bool             (* T.W *)
  | LoadRegisterByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* mem: memory location*)
      * bool             (* T.W *)
  | LoadRegisterDual of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination 1 *)
      * arm_operand_int  (* rt2: destination 2 *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
  | LoadRegisterHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
  | LoadRegisterSignedByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
  | LoadRegisterSignedHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: destination *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory location *)
  | LogicalShiftLeft of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: shift<0:7> *)
  | LogicalShiftRight of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: shift<0:7> *)
  | Move of
      bool (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rm/imm: source *)
      * bool            (* T.W *)
  | MoveTop of
      arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* imm: source *)
  | MoveWide of
      arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* imm: source *)
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
      * arm_operand_int  (* ra: accumulat *)
  | Pop of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* stack pointer *)
      * arm_operand_int  (* register list *)
  | Push of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* stack pointer *)
      * arm_operand_int  (* register list *)
  | ReverseSubtract of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm: source 2 *)
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
  | SignedExtendByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
  | SignedExtendHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rm: source *)
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
  | StoreMultipleIncrementAfter of
      bool    (* writeback *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rn: base *)
      * arm_operand_int (* rl: register list *)
      * arm_operand_int (* mem: multiple memory locations *)
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
      * arm_operand_int  (* mem: memory location *)
      * bool             (* T.W *)
  | StoreRegisterByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* mem: memory location *)
  | StoreRegisterDual of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source 1 *)
      * arm_operand_int  (* rt2: source 2 *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immdiate *)
      * arm_operand_int  (* mem: memory location *)
  | StoreRegisterHalfword of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rt: source *)
      * arm_operand_int  (* rn: base *)
      * arm_operand_int  (* rm/imm: index/immediate *)
      * arm_operand_int  (* mem: memory loction *)
  | Subtract of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
  | SubtractCarry of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
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
  | Test of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
  | TestEquivalence of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rn: source 1 *)
      * arm_operand_int  (* rm/imm: source 2 *)
  | UnsignedBitFieldExtract of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* rd: destination *)
      * arm_operand_int  (* rn: source *)
  | UnsignedExtendAddHalfword of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* rd: destination *)
      * arm_operand_int (* rn: source 1 *)
      * arm_operand_int (* rm: source 2 *)
  | UnsignedExtendByte of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | UnsignedExtendHalfword of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  | UnsignedMultiplyLong of
      bool   (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* rdlo: destination 1 *)
      * arm_operand_int (* rdhi: destination 2 *)
      * arm_operand_int (* rn: source 1 *)
      * arm_operand_int (* rm: source 2 *)

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

    method index_register_shift_rotate: register_shift_rotate_t -> int
    method index_arm_memory_offset: arm_memory_offset_t -> int
    method index_arm_opkind: arm_operand_kind_t -> int
    method index_arm_operand: arm_operand_int -> int
    method index_arm_opcode: arm_opcode_t -> int
    method index_arm_bytestring: string -> int
    method index_arm_instr_class: arm_instr_class_t -> int

    method write_xml_arm_bytestring: ?tag:string -> xml_element_int -> string -> unit
    method write_xml_arm_opcode: ?tag:string -> xml_element_int -> arm_opcode_t -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

class type arm_assembly_instruction_int =
  object
    (* setters *)
    method set_block_entry: unit
    method set_inlined_call: unit

    (* accessors *)
    method get_address: doubleword_int
    method get_opcode: arm_opcode_t
    method get_instruction_bytes: string
    method get_bytes_ashexstring: string
    method get_non_code_block: not_code_t

    (* predicates *)
    method is_block_entry: bool
    method is_inlined_call: bool
    method is_valid_instruction: bool
    method is_non_code_block: bool
    method is_not_code: bool

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

    (* accessors *)
    method length: int
    method at_index: int -> arm_assembly_instruction_int
    method at_address: doubleword_int -> arm_assembly_instruction_int
    method get_code_addresses_rev:
             ?low:doubleword_int -> ?high:doubleword_int -> unit -> doubleword_int list
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
    method toString: ?filter:(arm_assembly_instruction_int -> bool) -> unit -> string

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
    method get_instructions_rev: arm_assembly_instruction_int list
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
             (doubleword_int -> ctxt_iaddress_t -> arm_assembly_instruction_int -> unit)
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
    method get_function_coverage: int * int * int (* coverage, overlap, multiplicity *)
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
             (location_int * location_int * ctxt_iaddress_t * ctxt_iaddress_t * xpr_t)

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

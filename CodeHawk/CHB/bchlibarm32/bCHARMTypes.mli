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

type arm_reg_t =
  | AR0
  | AR1
  | AR2
  | AR3
  | AR4
  | AR5
  | AR6
  | AR7
  | AR8
  | AR9
  | AR10
  | AR11
  | AR12
  | ARSP
  | ARLR
  | ARPC

type shift_rotate_type_t =
  | SRType_LSL
  | SRType_LSR
  | SRType_ASR
  | SRType_ROR
  | SRType_RRX

type register_shift_t = shift_rotate_type_t * int

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
  | ARMShiftedReg of arm_reg_t * register_shift_t option
  | ARMRotatedReg of arm_reg_t * int
  | ARMImmediate of immediate_int
  | ARMAbsolute of doubleword_int
  | ARMOffsetAddress of
      arm_reg_t   (* base register *)
      * int       (* offset (nonnegative) *)
      * bool      (* isadd *)
      * bool      (* iswback *)
      * bool      (* isindex *)

type arm_operand_mode_t = RD | WR | RW

class type arm_operand_int =
  object ('a)

           (* accessors *)
    method get_kind: arm_operand_kind_t
    method get_mode: arm_operand_mode_t
    method get_register: arm_reg_t

    (* converters *)
    method to_numerical: numerical_t
    method to_address: floc_int -> xpr_t
    method to_variable: floc_int -> variable_t
    method to_expr: floc_int -> xpr_t
    method to_lhs: floc_int -> variable_t * cmd_t list

    (* predicate *)
    method is_read: bool
    method is_write: bool
    method is_register: bool
    method is_absolute_address: bool

    (* i/o *)
    method toString: string
    method toPretty: pretty_t
  end

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
  (* DataProcRegType *)
  (* DataProcImmType *)
  | Add of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd *)
      * arm_operand_int  (* rn *)
      * arm_operand_int (* imm *)
  | AddCarry of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd *)
      * arm_operand_int  (* rn *)
      * arm_operand_int (* imm *)      
  | Adr of
      arm_opcode_cc_t (* condition *)
      * arm_operand_int  (* destination register *)
      * arm_operand_int  (* targetaddress *)
  | BitwiseAnd of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* destination *)
      * arm_operand_int  (* source1 *)
      * arm_operand_int  (* source2 *)
  | BitwiseBitClear of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* destination *)
      * arm_operand_int  (* source1 *)
      * arm_operand_int  (* source2 *)
  | BitwiseNot of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* destination *)
      * arm_operand_int  (* source *)
  | BitwiseOr of
      bool (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* destination *)
      * arm_operand_int  (* source1 *)
      * arm_operand_int  (* source2 *)
  | BranchExchange of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
  | BranchLinkExchange of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
  | Compare of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* register *)
      * arm_operand_int  (* immediate *)
  | CountLeadingZeros of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* destination *)
      * arm_operand_int  (* source *)
  | Mov of
      bool (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* Rd *)
      * arm_operand_int (* imm/reg *)
  | MoveTop of
      bool (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* Rd *)
      * arm_operand_int (* imm/reg *)
  | MoveWide of
      bool (* flags are set *)
      * arm_opcode_cc_t (* condition *)
      * arm_operand_int (* destination (reg) *)
      * arm_operand_int (* source *)
  | Multiply of
      bool  (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* destination *)
      * arm_operand_int  (* source1 *)
      * arm_operand_int  (* source2 *)
  | Subtract of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* rd *)
      * arm_operand_int  (* rn *)
      * arm_operand_int  (* imm *)
  (* LoadStoreRegType *)
  | LoadRegister of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* destination (reg) *)
      * arm_operand_int  (* source (mem) *)
  | LoadRegisterByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* destination (reg) *)
      * arm_operand_int  (* source (mem) *)
  | ReverseSubtract of
      bool   (* flags are set *)
      * arm_opcode_cc_t  (* condition *)
      * arm_operand_int  (* destination *)
      * arm_operand_int  (* src1 *)
      * arm_operand_int  (* src2 *)
  | StoreRegister of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* source (reg) *)
      * arm_operand_int  (* destination (mem) *)
  | StoreRegisterByte of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* source (reg) *)
      * arm_operand_int  (* destination (mem) *)
  (* LoadStoreImmType *)
  | Pop of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int  (* register list *)
  | Push of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* register list *)
  (* MediaType *)
  | UnsignedExtendHalfword of
      arm_opcode_cc_t   (* condition *)
      * arm_operand_int (* destination *)
      * arm_operand_int (* source *)
  (* BlockDataType *)
  (* BranchLinkType *)
  | Branch of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
  | BranchLink of
      arm_opcode_cc_t    (* condition *)
      * arm_operand_int  (* target address *)
  (* SupervisorType *)
  | SupervisorCall of arm_opcode_cc_t * arm_operand_int
(* LoadStoreCoprocType *)
(* CoprocessorType *)
(* UnconditionalType *)
(* Misc *)
  | OpInvalid

class type arm_dictionary_int =
  object

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

    (* predicates *)
    method is_block_entry: bool
    method is_inlined_call: bool
    method is_valid_instruction: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString: string
    method toPretty: pretty_t

  end

class type arm_assembly_instructions_int =
  object

    (* setters *)
    method set: int -> arm_assembly_instruction_int -> unit

    (* accessors *)
    method length: int
    method at_index: int -> arm_assembly_instruction_int
    method at_address: doubleword_int -> arm_assembly_instruction_int
    method get_code_addresses_rev:
             ?low:doubleword_int -> ?high:doubleword_int -> unit -> doubleword_int list
    method get_num_instructions: int
    method get_num_unknown_instructions: int

    (* iterators *)
    method iteri: (int -> arm_assembly_instruction_int -> unit) -> unit
    method itera: (doubleword_int ->arm_assembly_instruction_int -> unit) -> unit

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
    method itera: (ctxt_iaddress_t -> arm_assembly_instruction_int -> unit) -> unit
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
    method inline_blocks: unit

    (* accessors *)
    method get_callgraph: callgraph_int
    method get_functions: arm_assembly_function_int list
    method get_function: dw_index_t -> arm_assembly_function_int
    method get_function_by_address: doubleword_int -> arm_assembly_function_int
    method get_function_coverage: int * int * int (* coverage, overlap, multiplicity *)
    method get_num_functions: int

    (* iterators *)
    method iter: (arm_assembly_functions_int -> unit) -> unit
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

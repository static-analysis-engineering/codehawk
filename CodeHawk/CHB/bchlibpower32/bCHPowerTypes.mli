(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022      Aarno Labs LLC

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

    NXP. Varibale-Length Encoding (VLE) Extension Programming Interface
    Manual (VLEPIM) Rev. 1, 2/2006.
 *)
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


type power_instruction_type_t = | PWR | VLE16 | VLE32

(** Special registers

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
 *)

type power_special_reg_t =
  | PowerCTR   (* Count Register *)
  | PowerLR    (* Link Register *)

type power_operand_kind_t =
  | PowerGPReg of int
  | PowerSpecialReg of power_special_reg_t
  | PowerImmediate of immediate_int
  | PowerAbsolute of doubleword_int
  | PowerIndReg of int * numerical_t    (* GPR index, offset *)


type power_operand_mode_t = RD | WR | RW


class type power_operand_int =
  object ('a)

    (* accessors *)
    method get_kind: power_operand_kind_t
    method get_mode: power_operand_mode_t
    method get_gp_register: int
    method get_special_register: power_special_reg_t
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

    (* printing *)
    method toString: string
    method toPretty: pretty_t

  end

type not_code_t = DataBlock of data_block_int


type power_opcode_t =
  | AddImmediate of
      power_instruction_type_t
      * bool (* shifted *)
      * bool (* record condition *)
      * power_operand_int  (* destination register *)
      * power_operand_int  (* source operand *)
      * power_operand_int  (* immediate *)
  | BitGenerateImmediate of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* immediate *)
  | BitMaskGenerateImmediate of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* immediate *)
  | BitSetImmediate of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* immediate *)
  | BranchCountRegister of
      power_instruction_type_t
      * power_operand_int  (* count register *)
  | BranchCountRegisterLink of
      power_instruction_type_t
      * power_operand_int  (* count_register *)
  | BranchLinkRegister of
      power_instruction_type_t
      * power_operand_int  (* link register *)
  | BranchLinkRegisterLink of
      power_instruction_type_t
      * power_operand_int  (* link register *)
  | CompareImmediate of
      power_instruction_type_t
      * power_operand_int  (* register operand *)
      * power_operand_int  (* immediate *)
  | CompareLogical of
      power_instruction_type_t
      * power_operand_int  (* register 1 *)
      * power_operand_int  (* register 2 *)
  | CompareLogicalImmediate of
      power_instruction_type_t
      * power_operand_int  (* register operand *)
      * power_operand_int  (* immediate *)
  | ExtendZeroHalfword of
      power_instruction_type_t
      * power_operand_int  (* src/dst *)
  | LoadHalfwordZero of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* effective address *)
  | LoadImmediate of
      power_instruction_type_t
      * bool (* shifted *)
      * power_operand_int  (* destination register *)
      * power_operand_int  (* source operand *)
  | LoadWordZero of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* effective address *)
  | MoveFromAlternateRegister of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* source register *)
  | MoveFromLinkRegister of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* link register *)
  | MoveToCountRegister of
      power_instruction_type_t
      * power_operand_int  (* count register *)
      * power_operand_int  (* source register *)
  | MoveToLinkRegister of
      power_instruction_type_t
      * power_operand_int  (* link register *)
      * power_operand_int  (* soure register *)
  | MoveRegister of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* source register *)
  | NotRegister of
      power_instruction_type_t
      * power_operand_int  (* src/dst register *)
  | ShiftLeftWordImmediate of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* source register *)
      * power_operand_int  (* imm: shift amount *)
  | ShiftRightAlgebraicWordImmediate of
      power_instruction_type_t
      * power_operand_int  (* destination register *)
      * power_operand_int  (* source register *)
      * power_operand_int  (* imm: shift amount *)
  | StoreHalfword of
      power_instruction_type_t
      * power_operand_int  (* source register *)
      * power_operand_int  (* effective address *)
  | StoreWord of
      power_instruction_type_t
      * power_operand_int  (* source register *)
      * power_operand_int  (* effective address *)
  | Subtract of
      power_instruction_type_t
      * power_operand_int  (* src/dst register *)
      * power_operand_int  (* source register *)
  | OpInvalid
  | NotCode of not_code_t option
  | NoOperation
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

                              (* accessors *)
    method get_address: doubleword_int
    method get_opcode: power_opcode_t
    method get_instruction_bytes: string
    method get_bytes_as_hexstring: string

    (* predicates *)
    method is_block_entry: bool
    method is_vle: bool

    (* i/o *)
    method write_xml: xml_element_int -> unit
    method toString: string
    method toPretty: pretty_t

  end


class type power_assembly_instructions_int =
  object

    (* setters *)
    method set: int -> power_assembly_instruction_int -> unit
    method set_not_code: data_block_int list -> unit

    (* accessors *)
    method length: int
    method at_index: int -> power_assembly_instruction_int
    method at_address: doubleword_int -> power_assembly_instruction_int

    (* predicates *)
    method is_code_address: doubleword_int -> bool
    
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
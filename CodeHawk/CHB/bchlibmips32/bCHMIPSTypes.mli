(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

type mips_fp_format_t =
  | FPSingle   (* 16 *)
  | FPDouble   (* 17 *)
  | FPFixedWord  (* 20 *)
  | FPFixedLong  (* 21 *)
  | FPPair (* 22 *)

type mips_instr_format_t =
  | RType of     (* SPECIAL:0 *)
      int (* opcode:6 (0) *)
      * int (* rs:5 *)
      * int (* rt:5 *)
      * int (* rd:5 *)
      * int (* shamt:5 *)
      * int (* funct:6 *) 
  | R2Type of    (*  SPECIAL2:28 *)
      int (* opcode:6 (28) *)
      * int (* rs:5 *)
      * int (* rt:5 *)
      * int (* rd:5 *)
      * int (* shamt:5 *)
      * int (* funct:6 *) 
  | IType of
      int (* opcode:6 *)
      * int (* rs:5 *)
      * int (* rt:5 *)
      * int (* immediate:16 *)
  | JType of
      int (* opcode:6 (2,3) *)
      * int (* address:26 *)
  | FPMCType of (* Floating Point Move Conditional *)
      int (* opcode:6 (SPECIAL:0) *)
      * int (* rs:5 *)
      * int (* cc:3 *)
      (* 1 bit: 0 *)
      * int (* tf:1 *)
      * int (* rd:5 *)
      (*  5 bits: 0 *)
      * int (* funct:6 *)
  | FPRMCType of (* Floating Point RegisterMove Conditional *)
      int (* opcode:6 (COP1:17) *)
      * int (* fmt:5 *)
      * int (* cc:3 *)
      (* 1 bit: 0 *)
      * int (* tf:1 *)
      * int (* fs:5 *)
      * int (* fd:5 *)
      * int (* funct:6 *)
  | FPRType of
      int (* opcode:6 (COP1:17) *)
      * int (* fmt:5 *)
      * int (* ft:5 *)
      * int (* fs:5 *)
      * int (* fd:5 *)
      * int (* funct:6 *)
  | FPRIType of   (* Floating Point Register Immediate *)
      int (* opcode:6 (COP1:17) *)
      * int (* sub:5 *)
      * int (* rt:5 *)
      * int (* fs:5 *)  (* with 11 bits 0 *)
  | FPCompareType of
      int (* opcode:6 (COP1:17) *)
      * int (* fmt:5 *)
      * int (* ft:5 *)
      * int (* fs:5 *)
      * int (* cc:3 *)
      (* 4 bits: 0011 *)
      * int (* cond:4 *)
 | FPICCType of  (* Floating Point Immediate with Condition Code *)
      int (* opcode:6 (COP1:17) *)
      * int (* sub:5  (BCC1:8) *)
      * int (* cc:3  *)
      * int (* nd:1 *)
      * int (* tf:1 *)
      * int (* offset:16 *)

(* ================================================================= Operand === *)

type mips_operand_kind_t =
  | MIPSReg of mips_reg_t
  | MIPSSpecialReg of mips_special_reg_t
  | MIPSFPReg of int
  | MIPSIndReg of mips_reg_t * numerical_t
  | MIPSAbsolute of doubleword_int
  | MIPSImmediate of immediate_int

type mips_operand_mode_t = RD | WR | RW

class type mips_operand_int =
  object ('a)

    (* accessors *)
    method get_kind: mips_operand_kind_t
    method get_mode: mips_operand_mode_t
    method get_register: mips_reg_t
    method get_absolute_address: doubleword_int

    (* converters *)
    method to_numerical: numerical_t
    method to_address: floc_int -> xpr_t
    method to_variable: floc_int -> variable_t
    method to_expr: floc_int -> xpr_t
    method to_lhs : floc_int -> variable_t * cmd_t list

    (* predicate *)
    method is_read : bool
    method is_write: bool
    method is_register: bool
    method is_absolute_address: bool

    (* printing *)
    method toString: string
    method toPretty: pretty_t

  end
         
type not_code_t = DataBlock of data_block_int

type mips_opcode_t =
  (* I-type: branch/function call *)
  | BranchLink of mips_operand_int
  | BranchLEZero of mips_operand_int * mips_operand_int
  | BranchLTZero of mips_operand_int * mips_operand_int
  | BranchGEZero of mips_operand_int * mips_operand_int
  | BranchGTZero of mips_operand_int * mips_operand_int
  | BranchLTZeroLink of mips_operand_int * mips_operand_int
  | BranchGEZeroLink of mips_operand_int * mips_operand_int
  | BranchEqual of mips_operand_int * mips_operand_int * mips_operand_int
  | BranchNotEqual of mips_operand_int * mips_operand_int * mips_operand_int
  | Branch of mips_operand_int
  (* I-type: arithmetic/logic *)
  | AddImmediate of mips_operand_int * mips_operand_int * mips_operand_int (* dest, src1, src2 *)
  | AddImmediateUnsigned of mips_operand_int * mips_operand_int * mips_operand_int
  | SetLTImmediate of mips_operand_int * mips_operand_int * mips_operand_int
  | SetLTImmediateUnsigned of mips_operand_int * mips_operand_int * mips_operand_int
  | AndImmediate of mips_operand_int * mips_operand_int * mips_operand_int
  | OrImmediate of mips_operand_int * mips_operand_int * mips_operand_int
  | XorImmediate of mips_operand_int * mips_operand_int * mips_operand_int
  (* I-type: memory *)
  | AddUpperImmediate of mips_operand_int * mips_operand_int * mips_operand_int (* dest,src,imm *)
  | LoadUpperImmediate of mips_operand_int * mips_operand_int (* dest, imm *)
  | LoadByte of mips_operand_int * mips_operand_int   (* dest, src *)
  | LoadHalfWord of mips_operand_int * mips_operand_int (* dest, src *)
  | LoadWordLeft of mips_operand_int * mips_operand_int (* dest, src *)
  | LoadWord of mips_operand_int * mips_operand_int (* dest, src *)
  | LoadLinkedWord of mips_operand_int * mips_operand_int (* dest, src *)
  | LoadByteUnsigned of mips_operand_int * mips_operand_int (* dest, src *)
  | LoadHalfWordUnsigned of mips_operand_int * mips_operand_int (* dest, src *)
  | LoadWordRight of mips_operand_int * mips_operand_int (* dest, src *)
  | StoreByte of mips_operand_int * mips_operand_int (* dest, src *)
  | StoreHalfWord of mips_operand_int * mips_operand_int (* dest, src *)
  | StoreWordLeft of mips_operand_int * mips_operand_int (* dest, src *)
  | StoreWord of mips_operand_int * mips_operand_int (* dest, src *)
  | StoreConditionalWord of mips_operand_int * mips_operand_int (* dest, src *)
  | StoreWordRight of mips_operand_int * mips_operand_int (* dest, src *)
  | LoadWordFP of mips_operand_int * mips_operand_int (* dest, src *)
  | LoadDoublewordToFP of mips_operand_int * mips_operand_int
  | StoreWordFromFP of mips_operand_int * mips_operand_int
  | StoreDoublewordFromFP of mips_operand_int * mips_operand_int
  (* J-type *)
  | Jump of mips_operand_int
  | JumpLink of mips_operand_int
  (* R-type *)
  | ShiftLeftLogical of mips_operand_int * mips_operand_int * mips_operand_int
  | ShiftRightLogical of mips_operand_int * mips_operand_int * mips_operand_int
  | ShiftRightArithmetic of mips_operand_int * mips_operand_int * mips_operand_int
  | ShiftLeftLogicalVariable of mips_operand_int * mips_operand_int * mips_operand_int
  | ShiftRightLogicalVariable of mips_operand_int * mips_operand_int * mips_operand_int
  | ShiftRightArithmeticVariable of mips_operand_int * mips_operand_int * mips_operand_int
  | JumpRegister of mips_operand_int
  | JumpLinkRegister of mips_operand_int * mips_operand_int (* returnaddr, target *)
  | MoveFromHi of mips_operand_int * mips_operand_int (* dest, HI *)
  | MoveToHi of mips_operand_int * mips_operand_int (* src, HI *)
  | MoveFromLo of mips_operand_int * mips_operand_int (* dest, LO *)
  | MoveToLo of mips_operand_int * mips_operand_int (* src, LO *)
  | MovN of mips_operand_int * mips_operand_int * mips_operand_int (* dst, src, test *)
  | MovZ of mips_operand_int * mips_operand_int * mips_operand_int (* dst, src, test *)
  | MultiplyWord of mips_operand_int * mips_operand_int * mips_operand_int * mips_operand_int
  | MultiplyUnsignedWord of mips_operand_int * mips_operand_int * mips_operand_int * mips_operand_int
  | DivideWord of mips_operand_int * mips_operand_int * mips_operand_int * mips_operand_int
  | DivideUnsignedWord of mips_operand_int * mips_operand_int * mips_operand_int * mips_operand_int
  | Add of mips_operand_int * mips_operand_int * mips_operand_int (* dest,src1,src2 *)
  | AddUnsigned of mips_operand_int * mips_operand_int * mips_operand_int (* dest,src1,src2 *)
  | Subtract of mips_operand_int * mips_operand_int * mips_operand_int
  | SubtractUnsigned of mips_operand_int * mips_operand_int * mips_operand_int
  | And of mips_operand_int * mips_operand_int * mips_operand_int
  | Or of mips_operand_int * mips_operand_int * mips_operand_int
  | Xor of mips_operand_int * mips_operand_int * mips_operand_int
  | Nor of mips_operand_int * mips_operand_int * mips_operand_int
  | SetLT of mips_operand_int * mips_operand_int * mips_operand_int
  | SetLTUnsigned of mips_operand_int * mips_operand_int * mips_operand_int
  | TrapIfEqual of int * mips_operand_int * mips_operand_int
  (* R2-type *)
  | MultiplyWordToGPR of mips_operand_int * mips_operand_int * mips_operand_int
  (* FPCM-type *)
  | MovF of int * mips_operand_int * mips_operand_int   (* cc, dst, src *)
  | MovT of int * mips_operand_int * mips_operand_int   (* cc, dst, src *)
  (* FPRType *)
  | FPAddfmt of mips_fp_format_t * mips_operand_int * mips_operand_int * mips_operand_int
  | FPSubfmt of mips_fp_format_t * mips_operand_int * mips_operand_int * mips_operand_int
  | FPMulfmt of mips_fp_format_t * mips_operand_int * mips_operand_int * mips_operand_int
  | FPDivfmt of mips_fp_format_t * mips_operand_int * mips_operand_int * mips_operand_int
  | FPSqrtfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPAbsfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPMovfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPNegfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPRoundLfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPTruncLfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPCeilLfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPFloorLfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPRoundWfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPTruncWfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPCeilWfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPFloorWfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPRSqrtfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPCVTSfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPCVTDfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPCVTWfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPCVTLfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  | FPCVTSPfmt of mips_fp_format_t * mips_operand_int * mips_operand_int
  (* FPRIType *)
  | MoveWordFromFP of mips_operand_int * mips_operand_int (* dst, src *)
  | MoveWordToFP of mips_operand_int * mips_operand_int (* src, dst *)
  | ControlWordFromFP of mips_operand_int * mips_operand_int (* dst, src *)
  | ControlWordToFP of mips_operand_int * mips_operand_int (* src, dst *)
  (* FPICCType  *)
  | BranchFPFalse of int * mips_operand_int
  | BranchFPTrue of int * mips_operand_int
  | BranchFPFalseLikely of int * mips_operand_int
  | BranchFPTrueLikely of int * mips_operand_int
  (* FPCompare *)
  | FPCompare of
      mips_fp_format_t
      * int (* cc *)
      * int (* cond *)
      * int (* exception *)
      * mips_operand_int (* fs *)
      * mips_operand_int (* ft *)

  (* Pseudo instructions *)
  | Move of mips_operand_int * mips_operand_int (*dst, src *)
  | LoadImmediate of mips_operand_int * mips_operand_int (* dst, imm *)
  | NoOperation
  | Return
  | Halt
  
  (* Misc *)
  | NotCode of not_code_t option  
  | OpInvalid
  

(* =================================================== MIPS opcode dictionary === *)

class type mips_dictionary_int =
  object

    method index_mips_opkind: mips_operand_kind_t -> int
    method index_mips_operand: mips_operand_int -> int
    method index_mips_opcode: mips_opcode_t -> int
    method index_mips_bytestring: string -> int
    method index_mips_opcode_text: string -> int
    method index_mips_instr_format: mips_instr_format_t -> int

    method write_xml_mips_bytestring: ?tag:string -> xml_element_int -> string -> unit
    method write_xml_mips_opcode: ?tag:string -> xml_element_int -> mips_opcode_t -> unit
    method write_xml_mips_opcode_text: ?tag:string -> xml_element_int -> string -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

  end

(* ===================================================== Assembly instruction === *)

class type mips_assembly_instruction_int =
object
  (* setters *)
  method set_block_entry: unit
  method set_delay_slot: unit
  method set_inlined_call: unit

  (* accessors *)
  method get_address: doubleword_int
  method get_opcode : mips_opcode_t
  method get_instruction_bytes: string
  method get_bytes_ashexstring: string

  (* predicates *)
  method is_block_entry : bool
  method is_delay_slot  : bool
  method is_inlined_call: bool

  (* printing *)
  method toString: string
  method toPretty: pretty_t

  (* xml *)
  method write_xml  : xml_element_int -> unit

end

(* ==================================================== Assembly instructions === *)

class type mips_assembly_instructions_int =
object

  (* setters *)
  method set: int -> mips_assembly_instruction_int -> unit
  method set_not_code: data_block_int list -> unit

  (* accessors *)
  method length: int
  method at_index  :            int -> mips_assembly_instruction_int
  method at_address: doubleword_int -> mips_assembly_instruction_int
  method get_code_addresses_rev:
           ?low:doubleword_int -> ?high:doubleword_int -> unit -> doubleword_int list
  method get_num_instructions: int
  method get_num_unknown_instructions: int

  (* iterators *)
  method iteri: (int -> mips_assembly_instruction_int -> unit) -> unit
  method itera: (doubleword_int -> mips_assembly_instruction_int -> unit) -> unit (* provide virtual address *)

  (* printing *)
  method toString: ?filter:(mips_assembly_instruction_int -> bool) -> unit -> string
  method toPretty: pretty_t

end

(* ======================================================= Assembly block === *)

class type mips_assembly_block_int =
  object

    (* accessors *)
    method get_faddr: doubleword_int
    method get_first_address: doubleword_int
    method get_location: location_int
    method get_context: context_t list
    method get_context_string: ctxt_iaddress_t
    method get_last_address: doubleword_int
    method get_instructions: mips_assembly_instruction_int list
    method get_instructions_rev: mips_assembly_instruction_int list
    method get_successors: ctxt_iaddress_t list
    method get_instruction: doubleword_int -> mips_assembly_instruction_int
    method get_bytes_as_hexstring: string
    method get_instruction_count: int
         
    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool
    method is_returning: bool

    (* iterators *)
    method itera:
             ?low:doubleword_int -> ?high:doubleword_int -> ?reverse:bool
             -> (ctxt_iaddress_t -> mips_assembly_instruction_int -> unit) -> unit

    (* printing *)
    method toString: string
    method toPretty: pretty_t
  end

(* ==================================================== Assembly function === *)

class type mips_assembly_function_int =
  object

    (* accessors *)
    method get_address: doubleword_int
    method get_blocks: mips_assembly_block_int list
    method get_block: ctxt_iaddress_t -> mips_assembly_block_int
    method get_instruction: doubleword_int -> mips_assembly_instruction_int
    method get_bytes_as_hexstring: string
    method get_function_md5: string
    method get_instruction_count: int
    method get_block_count: int

    (* iterators *)
    method iter: (mips_assembly_block_int -> unit) -> unit
    method itera: (ctxt_iaddress_t -> mips_assembly_block_int -> unit) -> unit
    method iteri:
             (doubleword_int -> ctxt_iaddress_t -> mips_assembly_instruction_int -> unit)
             -> unit

    method populate_callgraph: callgraph_int -> unit

    (* predicates *)
    method includes_instruction_address: doubleword_int -> bool

    (* printing *)
    method toPretty: pretty_t
  end

(* =================================================== Assembly functions === *)

class type mips_assembly_functions_int =
  object

    (* reset *)
    method reset: unit

    (* setters *)
    method add_function: mips_assembly_function_int -> unit
    method inline_blocks: unit

    (* accessors *)
    method get_callgraph: callgraph_int
    method get_functions: mips_assembly_function_int list
    method get_function: dw_index_t -> mips_assembly_function_int
    method get_function_by_address: doubleword_int -> mips_assembly_function_int
    method get_function_coverage: int * int * int (* coverage, overlap, multiplicity *)
    method get_num_functions: int

    (* iterators *)
    method iter: (mips_assembly_function_int -> unit) -> unit
    method itera: (doubleword_int -> mips_assembly_function_int -> unit) -> unit
    method bottom_up_itera: (doubleword_int -> mips_assembly_function_int -> unit) -> unit
    method top_down_itera: (doubleword_int -> mips_assembly_function_int -> unit) -> unit

    (* predicates *)
    method has_function_by_address: doubleword_int -> bool
    method includes_instruction_address: doubleword_int -> bool

    (* printing *)
    method dark_matter_to_string: string

  end

(* ================================================================== Code pc === *)

class type mips_code_pc_int =
object
  (* accessors *)
  method get_next_instruction      : ctxt_iaddress_t * mips_assembly_instruction_int
  method get_block_successors      : ctxt_iaddress_t list
  method get_block_successor       : ctxt_iaddress_t 
  method get_false_branch_successor: ctxt_iaddress_t
  method get_true_branch_successor : ctxt_iaddress_t
  method get_conditional_successor_info:
           (location_int * location_int * ctxt_iaddress_t * ctxt_iaddress_t * xpr_t)

  (* predicates *)
  method has_more_instructions: bool
  method has_conditional_successor: bool
end

         
(* =========================================================== CHIF System === *)

class type mips_chif_system_int =
  object

    (* reset *)
    method reset: unit
         
    (* setters *)
    method add_mips_procedure: procedure_int -> unit

    (* accessors *)
    method get_mips_system: system_int
    method get_mips_procedure_names: symbol_t list
    method get_mips_procedure: doubleword_int -> procedure_int

    (* predicates *)
    method has_mips_procedure: doubleword_int -> bool
  end

(* ========================================== MIPS instruction dictionary === *)

class type mips_opcode_dictionary_int =
  object

    method index_sp_offset: int * interval_t -> int
    method index_instr:
             mips_assembly_instruction_int
             -> floc_int
             -> block_restriction_t option
             -> int

    method get_sp_offset: int -> (int * interval_t)

    method write_xml_sp_offset: ?tag:string -> xml_element_int -> int * interval_t -> unit
    method write_xml_instr:
             ?tag:string
             -> xml_element_int
             -> mips_assembly_instruction_int
             -> floc_int
             -> block_restriction_t option
             -> unit

    method write_xml: xml_element_int -> unit
    method read_xml: xml_element_int -> unit

    method toPretty: pretty_t
  end

class type mips_analysis_results_int =
  object

    method record_results: ?save:bool -> mips_assembly_function_int -> unit
    method write_xml: xml_element_int -> unit
    method save: unit

  end


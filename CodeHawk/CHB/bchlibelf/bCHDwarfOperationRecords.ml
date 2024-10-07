(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs, LLC

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

(* chutil *)
open CHPrettyUtil

(* bchlibelf *)
open BCHDwarfTypes
open BCHDwarfUtils


class type ['a] dw_operation_formatter_int =
  object
    method ops: string -> dwarf_operand_t list -> 'a
    method no_op_int: string -> int -> 'a
    method ops_int: string -> int -> dwarf_operand_t list -> 'a
    method no_ops: string -> 'a
  end


type 'a dw_operation_record_t = {
    mnemonic: string;
    operands: dwarf_operand_t list;
    dw_asm: 'a dw_operation_formatter_int -> 'a
  }


let get_dw_op_record (dwop: dwarf_operation_t): 'a dw_operation_record_t =
  let no_op_rec s =
    let name = "DW_OP_" ^ s in
    {mnemonic = name; operands = []; dw_asm = (fun f -> f#no_ops name)} in
  match dwop with
  | DW_OP_addr op -> {
      mnemonic = "DW_OP_addr";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_addr" [op])
    }
  | DW_OP_deref -> no_op_rec "deref"
  | DW_OP_const1u op -> {
      mnemonic = "DW_OP_const1u";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_const1u" [op])
    }
  | DW_OP_const1s op -> {
      mnemonic = "DW_OP_const1s";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_const1s" [op])
    }
  | DW_OP_const2u op -> {
      mnemonic = "DW_OP_const2u";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_const2u" [op])
    }
  | DW_OP_const4u op -> {
      mnemonic = "DW_OP_const4u";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_const4u" [op])
    }
  | DW_OP_dup -> no_op_rec "dup"
  | DW_OP_drop -> no_op_rec "drop"
  | DW_OP_over -> no_op_rec "over"
  | DW_OP_swap -> no_op_rec "swap"
  | DW_OP_and -> no_op_rec "and"
  | DW_OP_minus -> no_op_rec "minus"
  | DW_OP_mul -> no_op_rec "mul"
  | DW_OP_or -> no_op_rec "or"
  | DW_OP_plus -> no_op_rec "plus"
  | DW_OP_plus_uconst op -> {
      mnemonic = "DW_OP_plus_uconst";
      operands = [op];
      dw_asm = (fun f -> f#ops "plus_uconst" [op])
    }
  | DW_OP_shl -> no_op_rec "shl"
  | DW_OP_shr -> no_op_rec "shr"
  | DW_OP_bra op -> {
      mnemonic = "DW_OP_bra";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_bra" [op])
    }
  | DW_OP_eq -> no_op_rec "eq"
  | DW_OP_ge -> no_op_rec "ge"
  | DW_OP_lt -> no_op_rec "lt"
  | DW_OP_ne -> no_op_rec "ne"
  | DW_OP_lit i -> {
      mnemonic = "DW_OP_lit";
      operands = [];
      dw_asm = (fun f -> f#no_op_int "DW_OP_lit" i)
    }
  | DW_OP_reg i -> {
      mnemonic = "DW_OP_reg";
      operands = [];
      dw_asm = (fun f -> f#no_op_int "DW_OP_reg" i)
    }
  | DW_OP_breg (i, op) -> {
      mnemonic = "DW_OP_breg";
      operands = [op];
      dw_asm = (fun f -> f#ops_int "DW_OP_breg" i [op])
    }
  | DW_OP_regx op -> {
      mnemonic = "DW_OP_regx";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_regx" [op])
    }
  | DW_OP_fbreg op -> {
      mnemonic = "DW_OP_fbreg";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_fbreg" [op])
    }
  | DW_OP_piece op -> {
      mnemonic = "DW_OP_piece";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_piece" [op])
    }
  | DW_OP_call_frame_cfa -> no_op_rec "call_frame_cfa"
  | DW_OP_stack_value -> no_op_rec "stack_value"
  | DW_OP_GNU_implicit_pointer (_name, dboffset, sloffset) -> {
      mnemonic = "DW_OP_GNU_implicit_pointer";
      operands = [dboffset; sloffset];
      dw_asm = (fun f -> f#ops "DW_OP_GNU_implicit_pointer" [dboffset; sloffset])
    }
  | DW_OP_GNU_entry_value (i, _x) -> {
      mnemonic = "DW_OP_GNU_entry_value";
      operands = [];
      dw_asm = (fun f -> f#no_op_int "DW_OP_GNU_entry_value" i)
    }
  | DW_OP_GNU_regval_type (_dw, op1, op2) -> {
     mnemonic = "DW_OP_GNU_regval_type";
     operands = [op1; op2];
     dw_asm = (fun f -> f#ops "DW_OP_GNU_regval_type" [op1; op2])
    }
  | DW_OP_GNU_convert (_dw, op) -> {
      mnemonic = "DW_OP_GNU_convert";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_GNU_convert" [op])
    }
  | DW_OP_GNU_parameter_ref (_dw, op) -> {
      mnemonic = "DW_OP_GNU_parameter";
      operands = [op];
      dw_asm = (fun f -> f#ops "DW_OP_GNU_parameter" [op])
    }
  | DW_OP_unknown i -> {
      mnemonic = "DW_OP_unknown";
      operands = [];
      dw_asm = (fun f -> f#no_op_int "DW_OP_unknown" i)
    }


class string_formatter_t (width:int): [string] dw_operation_formatter_int =
object

  method ops (s: string) (ops: dwarf_operand_t list) =
    let s = fixed_length_string s width in
    let ops = String.concat ", " (List.map dwarf_operand_to_string ops) in
    s ^ ops

  method no_op_int (s: string) (i: int) = s ^ (string_of_int i)

  method ops_int (s: string) (i: int) (ops: dwarf_operand_t list) =
    let s = fixed_length_string (s ^ (string_of_int i)) width in
    let ops = String.concat ", " (List.map dwarf_operand_to_string ops) in
    s ^ ops

  method no_ops (s: string) = s

end


let mk_string_formatter (width: int) = new string_formatter_t width

let dwarf_operand_list_to_string
      (width: int) (s: string) (ops: dwarf_operand_t list) =
  let formatter = mk_string_formatter width in
  formatter#ops s ops


let get_dw_op_name (op: dwarf_operation_t) = (get_dw_op_record op).mnemonic

let get_dw_op_operands (op: dwarf_operation_t) = (get_dw_op_record op).operands

let dwarf_operation_to_string (op: dwarf_operation_t): string =
  let default () = (get_dw_op_record op).dw_asm (mk_string_formatter 80) in
  default ()

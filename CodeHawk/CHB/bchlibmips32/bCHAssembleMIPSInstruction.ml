(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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
open CHNumerical

(* bchlib *)
open BCHDoubleword
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSOperand
open BCHMIPSTypes

module TR = CHTraceResult


(** Assembles a MIPS assembly instruction into a doubleword.*)


(* Assumes i can be converted to a 32 bit doubleword *)
let int2dw (i: int) = TR.tget_ok (int_to_doubleword i)


let ri (op: mips_operand_int): int = op#get_register_index
let rii (op: mips_operand_int): int = op#get_indirect_register_index

let assemble_mips_instruction
      ?(iaddr=wordzero) (opc: mips_opcode_t): doubleword_int =
  match opc with
  | AddUnsigned (rd, rs, rt) ->
     let v = ((ri rs) lsl 21) + ((ri rt) lsl 16) + ((ri rd) lsl 11) + 33 in
     int2dw v
  | StoreWord (mem, rs) ->
     let v =
       (43 lsl 26)
       + ((rii mem) lsl 21)
       + ((ri rs) lsl 16)
       + mem#get_indirect_offset#toInt in
     int2dw v
  | _ -> wordzero


let assemble_mips_move_instruction
      ?(bigendian=false) (rd: mips_reg_t) (rs: mips_reg_t): string =
  let dw: doubleword_int =
    assemble_mips_instruction
      (AddUnsigned (
           (mips_register_op rd WR),
           (mips_register_op rs RD),
           (mips_register_op MRzero RD))) in
  if bigendian then
    dw#to_fixed_length_hex_string
  else
    dw#to_fixed_length_hex_string_le


let assemble_mips_sw_stack_instruction
      ?(bigendian=false) (rs: mips_reg_t) (offset: int): string =
  let dw: doubleword_int =
    assemble_mips_instruction
      (StoreWord (
           mips_indirect_register_op MRsp (mkNumerical offset) WR,
           mips_register_op rs RD)) in
  if bigendian then
    dw#to_fixed_length_hex_string
  else
    dw#to_fixed_length_hex_string_le


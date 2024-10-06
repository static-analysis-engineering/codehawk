(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2024  Aarno Labs LLC

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

(* bchlib *)
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSTypes


(** Assembles a MIPS assembly instruction into a doubleword.*)


(** [assemble_mips_move_instruction ~big_endian dst src] returns a string
    that represents the bytes of the assembly instruction [move dst, src]
    in the requested (big or little endian) order.*)
val assemble_mips_move_instruction:
  ?bigendian:bool -> mips_reg_t -> mips_reg_t -> string


(** [assemble_mips_sw_stack_instruction ~big_endian src offset] returns a
    string that represents the bytes of the assemble instruction
    [sw src, offset($sp)] in the requested (big or little endian) order.*)
val assemble_mips_sw_stack_instruction:
  ?bigendian:bool -> mips_reg_t -> int -> string


(** [assemble_mips_instruction ~iaddr opc] assembles [opc] into a
    doubleword according (in bigendian representation), where [iaddr] 
    is the virtual address of the instruction (relevant only if the
    instruction is pc-relative.*)
val assemble_mips_instruction:
  ?iaddr:doubleword_int -> mips_opcode_t -> doubleword_int

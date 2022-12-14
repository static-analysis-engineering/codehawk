(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHXmlDocument

(* bchlib *)
open BCHLibTypes

(* bchlibmips32 *)
open BCHMIPSTypes


(** [get_mips_opcode_name opc] returns the mnemonic of [opc].*)
val get_mips_opcode_name: mips_opcode_t -> string


(** [get_mips_operands opc] returns the operands of [opc].*)
val get_mips_operands: mips_opcode_t -> mips_operand_int list


(** [mips_opcode_to_string ~width opc] returns a standard string representation
    of [opc] with [width] width of the mnemonic (default 8).*)
val mips_opcode_to_string: ?width:int -> mips_opcode_t -> string


(** Return true if the the opcode has a delay slot.*)
val has_delay_slot: mips_opcode_t -> bool


(** [get_operands_written opc] returns the list of operands that get written by
    [opc] (including those that get written and read).*)
val get_operands_written: mips_opcode_t -> mips_operand_int list


(** [get_operands_read opc] returns the list of operands that get read by [opc]
    (including those that get written and read).*)
val get_operands_read: mips_opcode_t -> mips_operand_int list
  

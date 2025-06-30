(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types


exception InconsistentInstruction of string


(** {1 Predicates on instructions}*)

val is_conditional_jump_instruction: opcode_t -> bool

val is_direct_jump_instruction: opcode_t -> bool

val is_jump_instruction: opcode_t -> bool

val is_call_instruction: opcode_t -> bool

val is_fall_through_instruction: opcode_t -> bool

(** {1 Opcode accessors}*)

val get_jump_operand: opcode_t -> operand_int

(** {1 Deconstructing operands} *)

(** [select_word_or_dword_reg opsize_override index] returns the 32-bit
    register associated with [index], or the 16-bit register associated
    with [index] if [opsize_override] is [true].

    Register correspondences:
    {t
       | index | 16-bit register | 32-bit register |
       |:-----:|:---------------:|:---------------:|
       | 0     | Ax              | Eax             |
       | 1     | Cx              | Ecx             |
       | 2     | Dx              | Edx             |
       | 3     | Bx              | Ebx             |
       | 4     | Sp              | Esp             |
       | 5     | Bp              | Ebp             |
       | 6     | Si              | Esi             |
       | 7     | Di              | Edi             |
    }

    raises InconsistentInstruction if [index] is outside the range
    0 - 7.
 *)
val select_word_or_dword_reg: bool -> int -> cpureg_t

val flags_used_by_condition: condition_code_t -> eflag_t list

val allflags: eflag_t list

val decompose_avx_lpp: int -> (int * int * int)
val decompose_avx_rxb: int -> (int * int)
val decompose_modrm: int -> (int * int * int)

val get_rm_byte_operand:
  ?addrsize_override:bool
  -> int
  -> int
  -> pushback_stream_int
  -> operand_mode_t
  -> operand_int

val get_rm_word_operand:
  int -> int -> pushback_stream_int -> operand_mode_t -> operand_int

val get_rm_operand:
  int
  -> int
  -> ?seg_override:segment_t option
  -> ?size:int
  -> ?floating_point:bool
  -> pushback_stream_int
  -> operand_mode_t
  -> operand_int

val get_rm_def_operand:
  bool
  -> ?seg_override:segment_t option
  -> int -> int
  -> pushback_stream_int
  -> operand_mode_t
  -> operand_int

val get_modrm_operands:
  ?seg_override:segment_t option
  -> ?addrsize_override:bool
  -> pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_byte_operands:
  pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_word_operands:
  pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_seg_operands:
  ?opsize_override:bool
  -> pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_quadword_operands:
  pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_double_quadword_operands:
  pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_mm_operands:
  pushback_stream_int
  -> int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_xmm_operands :
  pushback_stream_int
  -> int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_xmm_mm_operands:
  pushback_stream_int
  -> int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_xmm_reg_operands:
  pushback_stream_int
  -> int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_sized_operands:
  pushback_stream_int
  -> int
  -> operand_mode_t
  -> int
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_def_operands:
  bool
  -> ?seg_override:segment_t option
  -> ?addrsize_override:bool
  -> pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_cr_operands:
  pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)

val get_modrm_dr_operands:
  pushback_stream_int
  -> operand_mode_t
  -> operand_mode_t
  -> (operand_int * operand_int)


(** {1 String references} *)

val get_string_reference: floc_int -> xpr_t -> string option

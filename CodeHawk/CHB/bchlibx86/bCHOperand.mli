(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
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

(* chlib *)
open CHPretty
open CHNumerical
open CHLanguage

(* chutil *)
open CHXmlDocument

(* xprlib *)
open Xprt

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types


val asm_operand_kind_is_equal: asm_operand_kind_t -> asm_operand_kind_t -> bool
val operand_mode_to_string: operand_mode_t -> string

(* Operand data

   An operand may be the source of data that is passed to a function later. If this
   is the case is_function_argument is true and get_function_argument returns the
   address of the call instruction that uses the argument and the index number of 
   the argument (starting at 1).
*)

val dummy_operand : operand_int
val register_op: cpureg_t -> int -> operand_mode_t -> operand_int
val double_register_op: cpureg_t -> cpureg_t -> int -> operand_mode_t -> operand_int

val fpu_register_op: int -> operand_mode_t -> operand_int
val mm_register_op : int -> operand_mode_t -> operand_int
val xmm_register_op: int -> operand_mode_t -> operand_int
val seg_register_op: segment_t -> operand_mode_t -> operand_int
val control_register_op: int -> operand_mode_t -> operand_int
val debug_register_op: int -> operand_mode_t -> operand_int

val indirect_register_op: cpureg_t -> numerical_t -> int -> operand_mode_t -> operand_int

val scaled_register_op: cpureg_t option -> cpureg_t option -> int -> numerical_t -> int ->
  operand_mode_t -> operand_int

val ds_esi: ?seg:segment_t -> ?size:int -> operand_mode_t -> operand_int
val es_edi: ?seg:segment_t -> ?size:int -> operand_mode_t -> operand_int

val edx_eax_r: operand_mode_t -> operand_int
val dx_ax_r  : operand_mode_t -> operand_int

val esp_deref: ?with_offset:int -> operand_mode_t -> operand_int
val ebp_deref: operand_mode_t -> operand_int

val absolute_op: doubleword_int -> int -> operand_mode_t -> operand_int
val seg_absolute_op: segment_t -> doubleword_int -> int -> operand_mode_t -> operand_int
val immediate_op: immediate_int -> int -> operand_int

val seg_indirect_register_op:
  segment_t -> cpureg_t -> numerical_t -> int -> operand_mode_t -> operand_int

(* operand_int constants *)

val imm0_operand: operand_int
val imm1_operand: operand_int

val oflag_op: operand_mode_t -> operand_int
val cflag_op: operand_mode_t -> operand_int
val zflag_op: operand_mode_t -> operand_int
val sflag_op: operand_mode_t -> operand_int
val pflag_op: operand_mode_t -> operand_int
val dflag_op: operand_mode_t -> operand_int
val iflag_op: operand_mode_t -> operand_int

val eax_r: operand_mode_t -> operand_int
val ecx_r: operand_mode_t -> operand_int
val edx_r: operand_mode_t -> operand_int
val ebx_r: operand_mode_t -> operand_int
val esp_r: operand_mode_t -> operand_int
val ebp_r: operand_mode_t -> operand_int
val esi_r: operand_mode_t -> operand_int
val edi_r: operand_mode_t -> operand_int
val ax_r : operand_mode_t -> operand_int
val cx_r : operand_mode_t -> operand_int
val dx_r : operand_mode_t -> operand_int
val bx_r : operand_mode_t -> operand_int
val sp_r : operand_mode_t -> operand_int
val bp_r : operand_mode_t -> operand_int
val si_r : operand_mode_t -> operand_int
val di_r : operand_mode_t -> operand_int
val al_r : operand_mode_t -> operand_int
val ah_r : operand_mode_t -> operand_int
val cl_r : operand_mode_t -> operand_int
val ch_r : operand_mode_t -> operand_int
val dl_r : operand_mode_t -> operand_int
val dh_r : operand_mode_t -> operand_int
val bl_r : operand_mode_t -> operand_int
val bh_r : operand_mode_t -> operand_int 

(* 0 : eax  (ax)
   1 : ecx  (cx)
   2 : edx  (dx)
   3 : ebx  (bx)
   4 : esp  (sp)
   5 : ebp  (bp)
   6 : esi  (si)
   7 : edi  (di)
*)
val cpureg_r: ?opsize_override:bool -> int -> operand_mode_t -> operand_int


(* operands constructed from input directly *)

val read_immediate_signed_byte_operand      : pushback_stream_int -> operand_int
val read_immediate_unsigned_byte_operand    : pushback_stream_int -> operand_int
val read_immediate_signed_word_operand      : pushback_stream_int -> operand_int
val read_immediate_unsigned_word_operand    : pushback_stream_int -> operand_int
val read_immediate_signed_doubleword_operand: pushback_stream_int -> operand_int
val read_immediate_signed_operand    : int -> pushback_stream_int -> operand_int
val read_immediate_unsigned_operand  : int -> pushback_stream_int -> operand_int

val read_target8_operand : doubleword_int -> pushback_stream_int -> operand_int
val read_target32_operand: doubleword_int -> pushback_stream_int -> operand_int 

(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs, LLC

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

(* bchlibarm32 *)
open BCHARMTypes


(** [disassemble_thumb_instruction ch base bytes] tries to disassemble an
    instruction represented by [bytes], an integer with range [0, 65535] (16 bits).
    If the most significant 5 bits are equal to 29, 30, or 31, an additional two
    bytes are read from the stream and combined with the first 2 bytes to make
    a 4-byte Thumb-2 instruction to be disassembled. This function is the
    primary interface of this module.
 *)
val disassemble_thumb_instruction:
  pushback_stream_int -> doubleword_int -> int -> arm_opcode_t


(** [parse_thumb_opcode ch base iaddr bytes] tries to disassemble an
    instruction represented by [bytes], similar to
    [disassemble_thumb_instruction], with the addition of an argument that
    provides the virtual address of the instruction. This function is
    provided solely for unit tests to check pc-relative instructions. *)
val parse_thumb_opcode:
  pushback_stream_int -> doubleword_int -> doubleword_int -> int -> arm_opcode_t

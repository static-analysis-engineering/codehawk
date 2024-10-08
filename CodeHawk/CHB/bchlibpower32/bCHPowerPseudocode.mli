(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2024  Aarno Labs, LLC

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


(* 5 bit value with 1 added *)
val oim5: int -> int


(** Return index of primary GPR register *)
val rindex: int -> int


(** Return index of alternate GPR register *)
val arindex: int -> int


(** Return sign extension of 8-bit value *)
val d8_sign_extend: int -> int


(** Return SCI8 value used in 32-bit arithmetic instructions using F, SCL, UI8

    Format used by some 32-bit arithmetic, compare, and logical instructions. 
    The UI8 field is an 8-bit immediate value shifted left 0, 1, 2, or 3 byte
    positions according to the value of the SCL field. The remaining bits in
    the 32-bit word are filled with the value of the F field, and the resulting
    32-bit value is used as one operand of the instruction.

    Reference: VLEPEM, page 3-5.
 *)
val sci8: int -> int -> int -> int

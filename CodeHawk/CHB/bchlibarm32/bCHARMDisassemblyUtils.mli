(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2026  Aarno Labs, LLC

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

(* bchlibarm32 *)
open BCHARMTypes


val get_interrupt_flags: int -> interrupt_flags_t

val get_it_condition_list: int -> int -> (string * arm_opcode_cc_t) list

val get_inverse_cc: arm_opcode_cc_t -> arm_opcode_cc_t option

val has_inverse_cc: arm_opcode_cc_t -> bool

(** [get_string_reference floc x] returns a string if [x] is a numerical constant
    that is the virtual address of a constant string in an ELF read-only section.
    In addition it adds an entry to the string table kept by each [floc] that
    this string is referenced by the instruction at the [floc] location. *)
val get_string_reference: floc_int -> xpr_t -> string option

(** [get_elf_string_reference x] returns a string if [x] is a numerical constant
    that is the virtual address of a constant string in an ELF read-only section.

    This function is a simpler version of [get_string_reference] above in that
    it does not need a [floc] and thus can be used in a wider context, e.g., to
    discharge proof obligations. It assumes that the value to which it is applied
    has been strengthened with invariants and simplified before application, as
    this function has no access to invariants.*)
val get_elf_string_reference: xpr_t -> string option

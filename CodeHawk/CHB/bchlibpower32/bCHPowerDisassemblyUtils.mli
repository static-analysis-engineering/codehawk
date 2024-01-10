(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs, LLC

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

(* bchlibpower32 *)
open BCHPowerTypes


val get_string_reference: floc_int -> xpr_t -> string option


(** [is_unconditional_nia_target_branch instr] returns true if [instr]
    is a [bcl] instruction with [bo=20] and [tgt=NIA] (next instruction
    address).

    This instruction is idiomatic for certain compilers to create
    position independent code by loading the next instruction address
    ([NIA]) in the link register.*)
val is_unconditional_nia_target_branch:
  pwr_assembly_instruction_int -> bool


(** [opt_absolute_branch_target instr] returns an absolute instruction
    address [a] if [instr] represents a (conditional or unconditional)
    jump to address [a] where [a] is not the next instruction.

    Otherwise None is returned.

    Note: this function specifically filters out the [bcl] instruction
    with [bo=20] and [tgt=NIA], that is, an unconditional jump to the
    next instruction, which is idiomatic for some compilers for
    creating position-independent code (by loading the [NIA] in the
    link register). Since the target instruction is the same as the
    regular next instruction, it should not induce the creation of a
    new basic block at the target of the branch.
*)
val opt_absolute_branch_target:
  pwr_assembly_instruction_int -> doubleword_int option


(** [is_absolute_branch_target instr] returns true if [instr] represents
    a jump (conditional or unconditional) to an address that is not the
    next instruction address.*)
val is_absolute_branch_target: pwr_assembly_instruction_int -> bool


(** [opt_conditional_absolute_branch_target instr] returns an absolute
    instruction address [a] if [instr] represents a conditional jump to
    address [a].

    Otherwise None is returned.*)
val opt_conditional_absolute_branch_target:
  pwr_assembly_instruction_int -> doubleword_int option


(** [is_conditional_absolute_branch_target instr] returns true if [instr]
    represents a conditional jump.*)
val is_conditional_absolute_branch_target:
  pwr_assembly_instruction_int -> bool

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHLanguage

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

(* bchlibx86 *)
open BCHLibx86Types


(** [conditional_jump_expr jumpopc testopc jumploc testloc] returns the
    branch predicate established by the instruction [testopc] at location
    [testloc], used by the branch instruction [jumpopc] at location
    [jumploc], together with the variables that were frozed at the test
    location to create the predicate.

    If no predicate could be constructed from the combination of test
    instruction and branch instruction, None is returned for the predicate,
    and a message is logged about the missing predicate.

    If the predicate constructed simplifies to {false], None is returned
    and a message is logged that the condition is ignored.

    @raises [BCH_failure] if [jumpopc] is not a jump instruction (i.e.,
    [Jexz], [DirectLoop], or [Jcc]).
 *)
val conditional_jump_expr:
  jumpopc:opcode_t
  -> testopc:opcode_t
  -> jumploc:location_int
  -> testloc:location_int
  -> (variable_t list * xpr_t option)


(** [conditional_set_expr setopc testopc setloc testloc] returns the
    condition established by the combination of the instruction [testopc]
    at location [testloc], and the condition code of the set instruction
    [setopc] at location [setloc]. If no condition can be established
    [random_constant_expr] is returned.

    @raises [BCH_failure] if [setopc] is not a set instruction (i.e.,
    [Setcc]).
 *)
val conditional_set_expr:
  setopc:opcode_t
  -> testopc:opcode_t
  -> setloc:location_int
  -> testloc:location_int
  -> xpr_t

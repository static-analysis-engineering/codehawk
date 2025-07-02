(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2025 Aarno Labs LLC

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

(* bchlibarm32 *)
open BCHARMTypes


(** Returns the predicate condition and associated info for a condidional,
    in particular it returns a tuple consisting of:
    - a list of temporary variables created to preserve the (frozen) values at
      the test location (testloc) for the location of the conditional (condloc)
    - the predicate that expresses the joint condition of test and condition
      code (cc, e.g., EQ), and
    - a list of the operands used in the creation of the predicate.

    The arguments to the function are:
    - [condopc]: the opcode of the conditional instruction (e.g., Branch)
    - [testopc]: the opcode of the test instruction (e.g., Compare)
    - [condloc]: the location of conditional instruction
    - [testloc]: the location of the test instruction.
 *)
val arm_conditional_expr:
  condopc: arm_opcode_t
  -> testopc:arm_opcode_t
  -> condloc:location_int
  -> testloc:location_int
  -> (variable_t list * xpr_t option * arm_operand_int list)


(** Returns the predicate condition and associated info as above for a composite
    condtitional of the form
{v
    I1: <test1>            CMP    x, #0
    I2: <test2-cc1>        CMPEQ  y, z
    I3: <cond-cc2>         BGT
v}
    where the ultimate predicate condition depends is a composite of potentially
    three test - cc combinations:
    - if test1-cc1 is true, I2 is executed and the branch predicate is test2-cc2
    - if test2-cc1 is false I2 is not executed and branch predicate is test2-cc1
    leading to the composite expression
{v
     (test1-cc1 /\ test2-cc2) \/ ((not test1-cc1) /\ test1-cc2)
v}
    or, in the case of the example above:
{v
     (x = 0 /\ y > z) \/ (x != 0 /\ x > 0)
or
     (x = 0 /\ y > z) \/ (x > 0)
v}
    - [condopc]: the opcode of the conditional instruction (above: BGT)
    - [testopc] the opcode of the second test instruction (above: CMPEQ)
    - [testtestopc]: the opcode of the first test instruction (above: CMP)
    - [condloc]: the location of [condopc]
    - [testloc]: the location of [testopc]
    - [testtestloc]: the location of [testtestopc]
 *)
val arm_conditional_conditional_expr:
  condopc: arm_opcode_t
  -> testopc: arm_opcode_t
  -> testtestopc: arm_opcode_t
  -> condloc: location_int
  -> testloc: location_int
  -> testtestloc: location_int
  -> (variable_t list * xpr_t option * arm_operand_int list)

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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
   
(* bchlibarm *)
open BCHARMTypes


(** Generation of type constraints from assembly instructions.

    Type constraints are generated based on:
    - the structure of an instruction (e.g., the base address of a load
      instruction must be a pointer)
    - relationships with externally provided types, including:
      * arguments in calls to library functions with known function signature
        are matched with parameter types;
      * return values of calls to library functions with known function
        signatures are matched with the return type of the library function
    - values propagated by invariants in a function with a known function
      signature are matched with the registers to which those values are
      assigned.

    Information contained in type constraints can flow in two directions:
    (1) from known type signature information to registers to which parameter
        values are assigned, to resolve local variable types
    (2) from known function arguments and instruction inferred types to function
        signature parameters, to discover function signatures
 *)


val mk_arm_fn_type_constraints:
  type_constraint_store_int
  -> arm_assembly_function_int
  -> arm_fn_type_constraints_int

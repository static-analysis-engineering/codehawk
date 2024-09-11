(* =============================================================================
   CodeHawk C Analyzer
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

(* cchlib *)
open CCHBasicTypes

(* cchanalyze *)
open CCHAnalysisTypes


(** [check_upper_bound poq typ exp] returns true if [exp] with type [typ]
    satisfies the upper-bound property, as implied by the invariants provided
    by [poq].

    An address is guaranteed to satisfy the upper-bound requirement if
    - it is passed as an argument (that is, it is the responsibility of the
      caller when passing a pointer, that it is either null, or points within
      the bounds of a memory region, as the receiving function has no way of
      checking this), or
    - it has an external base address a zero offset, or
    - it is equal to a heap address that has been cast to the target type,
    - it is the return value from a function call (that is, it is the
      responsibility of the function returning the pointer, that the pointer
      is either null or points within the bounds of a memory region, as the
      receiving function function has no way of checking this), or
    - it is equal to a frozen field value, as primary proof obligations for
      upper bound are generated for each field assignment (that is, it is
      true by IH (Inductive Hypothesis)).

    The requirement for an upper bound is lifted to the function api if the
    pointer is euql to the initial value (+ offset) of a struct value pointed to
    by a parameter.

    Note: the IH for the result of pointer arithmetic is in general no strong
    enough to support the upper bound; however, all pointer arithmetic within
    a dereferencing operation has been strengthened, such that the result is
    actually dereferencable.
 *)
val check_upper_bound: po_query_int -> typ -> exp -> bool

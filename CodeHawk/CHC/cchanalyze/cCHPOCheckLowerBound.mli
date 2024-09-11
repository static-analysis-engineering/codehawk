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


(** [check_lower_bound poq typ exp] returns [true] if pointer expression [exp]
    satisfies the lower bound property, that is, if [exp] does not violate the
    lower bound of the buffer it is pointing to.

    An address is guaranteed to satisfy the lower-bound requirement if
    - it is passed as an argument to the function (that is, it is the
      responsibility of the caller passing the pointer, that it is either null,
      or points within the bounds of a memory region, as the receiving function
      has no way of checking this), or
    - it has an external base address and a non-negative offset, or
    - it is equal to a heap address, or
    - it is the return value from a function call (that is, it is the
      responsibility of the function returning the pointer, that it is either
      null, or points within the bounds of a memory region, as the receiving
      function has no way of checking this), or
    - it is equal to a frozen field value, as primary proof obligations for
      lower bound are generated for each assignment to a field, (that is, it
      is true by IH (inductive hypothesis)), or
    - the bas is the result of pointer arithmetic and the offset is non-negative
 *)
val check_lower_bound: po_query_int -> typ -> exp -> bool

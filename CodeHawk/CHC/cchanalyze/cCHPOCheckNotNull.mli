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


(** [check_not_null poq exp] returns true if the expression [exp] is guaranteed
    to be not null, as implied by the invariants supplied by [poq].

    An address is guaranteed to be not null if
    - it is explicitly checked non-null within the function, or
    - it is the result of pointer arithmetic (by IH (inductive hypothesis)), or
    - it is a nonzero offset from a base address

    The requirement for a non-null memory address is lifted to the function api
    if it is equal to the initial value of a struct value pointed to be a
    parameter (an assumption is automatically generated).

    The requirement for a non-null memory address is delegated to the postcondition
    of a function if it is the return value of that function (a postcondition
    request is emitted).
 *)
val check_not_null: po_query_int -> exp -> bool

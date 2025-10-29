(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2025  Aarno Labs LLC

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


(** [check_locally_initialized poq lval] returns true if the invariants supplied by
    [poq] imply the initialization of [lval] within the function.

    An lval is guaranteed to be locally initialized if
    - if it has been assigned within the function, or
    - if the expression is the dereferencing of the address of a variable, and the
      variable is initialized, or
    - if the lval contains an embedded null dereference; null dereference is
      checked for separately, or
    - if the lval can be shown to be distinct from the memory region pointed to
      by the vinfo (the targeted output parameter)
 *)
val check_locally_initialized: po_query_int -> varinfo -> lval -> bool

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


(** [check_valid_mem poq exp] returns [true] if expression [exp] is guaranteed to
    point to a memory region that is valid (i.e., has not been freed). Evidence
    of validity is saved separately. Similarly, if the condition cannot be
    proven valid, an attempt is made to construct diagnostics on what information
    is outstanding for a successful proof, which is also saved separately.

    The IH (Inductive Hypothesis) guarantees that any region pointed to by an
    argument is valid memory at function entry point (checked at the time of the
    call). Similarly, any region pointed to by a return value from a callee is
    valid memory at the pointer where the pointer value is received. For any
    other address locations received from outside, the proof obligation should
    be delegated.

    If the application does not contain any calls to free at all (indicated by
    global_free) the valid-mem obligation is vacuously valid.

    Any region pointed to can potentially be freed by any calls that are made
    after the address is received, which is the reason for checking the effect
    of any calls made since receiving the pointer value. *)
val check_valid_mem: po_query_int -> exp -> bool

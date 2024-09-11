(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
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

(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes


class controlled_resource_checker_t
        (_poq: po_query_int)
        (_resource: string)
        (_e: exp)
        (_invs: invariant_int list) =
object
  (* ----------------------------- safe ------------------------------------- *)
  method check_safe = false
  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_controlled_resource (poq:po_query_int) (resource:string) (e:exp)  =
  let invs = poq#get_invariants 3 in
  let _ = poq#set_diagnostic_invariants 3 in
  let checker = new controlled_resource_checker_t poq resource e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

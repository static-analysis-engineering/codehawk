(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHNumerical
open CHPretty
   
(* chutil *)
open CHPrettyUtil
   
(* xprlib *)
open Xprt
open XprToPretty
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHMemoryBase
open CCHPreTypes
   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)

          
class common_base_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list) =
object (self)
  (* ----------------------------- safe ------------------------------------- *)
  method check_safe = false
  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_common_base (poq:po_query_int) (e1:exp) (e2:exp) =
  let invs1 = poq#get_invariants 1 in
  let invs2 = poq#get_invariants 2 in
  let _ = poq#set_diagnostic_invariants 1 in
  let _ = poq#set_diagnostic_invariants 2 in
  let checker = new common_base_checker_t poq e1 e2 invs1 invs2 in
  checker#check_safe || checker#check_violation || checker#check_delegation
                         


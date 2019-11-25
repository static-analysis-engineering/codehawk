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
open CHLogger
open CHPrettyUtil
   
(* xprlib *)
open Xprt
open XprToPretty
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesUtil
open CCHTypesToPretty

(* cchpre *)
open CCHCheckImplication
open CCHCheckValid
open CCHPOPredicate
open CCHPreTypes
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)
        
class cast_checker_t
        (poq:po_query_int)
        (tfrom:typ)
        (tto:typ)
        (e:exp)
        (invs:invariant_int list) =
object (self)
  (* ----------------------------- safe ------------------------------------- *)
  method check_safe = false
  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_cast (poq:po_query_int) (tfrom:typ) (tto:typ) (e:exp)  =
  let invs = poq#get_invariants 3 in
  let _ = poq#set_diagnostic_invariants 3 in
  let checker = new cast_checker_t poq tfrom tto e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

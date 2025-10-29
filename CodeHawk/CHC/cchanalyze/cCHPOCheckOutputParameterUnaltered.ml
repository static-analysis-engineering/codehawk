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

(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes


let x2p = XprToPretty.xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let _x2s x = p2s (x2p x)
let _e2s e = p2s (CCHTypesToPretty.exp_to_pretty e)


let _fenv = CCHFileEnvironment.file_environment


class outputparameter_unaltered_checker_t
        (_poq: po_query_int)
        (vinfo: varinfo)
        (_invs: invariant_int list) =
object

  method private vinfo = vinfo

  method check_safe = false

  method check_violation = false

end


let check_outputparameter_unaltered (poq:po_query_int) (vinfo: varinfo) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new outputparameter_unaltered_checker_t poq vinfo invs in
  checker#check_safe || checker#check_violation

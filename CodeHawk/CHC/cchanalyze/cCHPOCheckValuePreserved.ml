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
open XprTypes
open XprToPretty

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil

(* cchpre *)
open CCHPreTypes
   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)          


class value_preserved_checker_t
        (poq:po_query_int)
        (e:exp)
        (invs:invariant_int list) =
object (self)
  (* ----------------------------- safe ------------------------------------- *)
  method check_safe =
    let values = poq#get_extended_values 1 e in
    let _ = poq#set_diagnostic_invariants 1 in
    List.fold_left (fun acc inv ->
        acc ||
          match inv#symbolic_expr with
          | Some (XVar v) when poq#env#is_initial_global_value v ->
             let deps = DLocal [ inv#index ] in
             let msg = "variable " ^  (e2s e) ^ " is equal to initial value" in
             begin
               poq#record_safe_result deps msg ;
               true
             end
          | _ -> false) false values
    
  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_value_preserved (poq:po_query_int) (e:exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new value_preserved_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

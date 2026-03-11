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

(* chlib *)
open CHNumerical

(* xprlib *)
(* open XprTypes *)

(* cchlib *)
(* open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty *)

(* cchpre *)
(* open CCHPOPredicate *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes

module ErrnoP = CCHErrnoWritePredicateSymbol

class errno_written_checker_t
  (poq: po_query_int)
  (locinv: location_invariant_int)
  (invs: invariant_int list) =
object (self)

  method private get_conditions (i: invariant_int): ErrnoP.t list option =
    match i#get_fact with
    | NonRelationalFact (_, FInitializedSet syms) -> 
      List.fold_left begin fun acc s ->
          match acc with
          | Some l ->
            Option.bind
             (ErrnoP.from_symbol s) 
             (fun (c : ErrnoP.t) -> Some (c :: l))
          | None -> None
      end (Some []) syms
    | _ -> None 

  method private check_condition_safe (wc: ErrnoP.t): dependencies_t option =
    match wc with
    | True -> 
      Some (DLocal [])

    | VarNull v -> 
      let v_invs = List.filter_map begin fun inv ->
        match inv#get_fact with
        | NonRelationalFact (vv, _) when vv#getName#getSeqNumber = v -> 
          Some(inv)
        | _ -> None
      end locinv#get_invariants in
      (* Do any of these prove v not null*)
      let find_proof (i: invariant_int) = 
        match i#const_value with
        | Some v when v#equal numerical_zero -> Some (DLocal [])
        | _ -> None
      in
      List.find_map find_proof v_invs

  method check_safe : bool = 
    let disjuncts = List.filter_map self#get_conditions invs in
    let check_all = 
        List.fold_left begin fun acc c -> 
          match acc with
          | Some (_) -> 
            Option.bind (self#check_condition_safe c) (fun _ -> Some (DLocal []))
          | _ -> None
          end (Some (DLocal []))
    in
    let check_alternatives = List.find_map check_all in
    let pf = check_alternatives disjuncts in
    match pf with
    | Some deps -> 
      poq#record_safe_result deps ":)"; true
    | _ -> false

end
let check_errno_written poq locinv = 
  let invs = poq#get_errno_write_invariants in
  let checker = new errno_written_checker_t poq locinv invs in
  checker#check_safe
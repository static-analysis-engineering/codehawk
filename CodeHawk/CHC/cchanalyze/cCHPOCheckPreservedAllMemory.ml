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
open CHLanguage
open CHPretty

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprToPretty
open Xsimplify

(* cchlib *)
open CCHBasicTypes
open CCHFileContract
open CCHLibTypes
open CCHTypesToPretty
open CCHUtilities
   
(* cchpre *)
open CCHFunctionSummary
open CCHPreTypes
open CCHProofObligation

(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class preserved_all_memory_checker_t  (poq:po_query_int) (callinvs:invariant_int list) =
object (self)

  val initsym = poq#env#get_p_entry_sym

  method get_calls (v:variable_t) =
    let initsym = poq#env#get_p_entry_sym in
    let match_indicator vv =
      if poq#env#is_augmentation_variable vv then
        let indicator = poq#env#get_indicator vv in
        v#getName#getSeqNumber = indicator
      else
        false in
    match callinvs with
    | [] ->
       begin
         poq#set_diagnostic "no call-record invariants found" ;
         None
       end
    | _ ->
       List.fold_left (fun acc inv ->
           match acc with
           | Some _ -> acc
           | _ ->
              match inv#get_fact with
              | NonRelationalFact (vv,FInitializedSet l) when v#equal vv || (match_indicator vv) ->
                 begin
                   match l with
                   | [] ->
                      begin
                        poq#set_diagnostic "call-record invariant has been corrupted" ;
                        None
                      end
                   | [ s ] when s#equal initsym -> Some []
                   | [ s ] ->
                      begin
                        poq#set_diagnostic
                          ("unexpected symbol in call-record invariant: " ^ s#getBaseName) ;
                        None
                      end
                   | l when List.exists (fun s -> s#equal initsym) l ->
                      Some (List.filter (fun s -> not (s#equal initsym)) l)
                   | _ -> None
                 end
              | _ -> None) None callinvs
             
  (* ----------------------------- safe ------------------------------------- *)

  method private call_preserves_validity sym =
    let sideeffects = poq#get_sym_sideeffects sym in
    let callee = poq#env#get_callsym_callee sym in
    if List.exists (fun (se,_) ->
           match se with
           | XPreservesAllMemory -> true
           | XFunctional -> true
           | _ -> false) sideeffects then
      let deps = DLocal [] in
      let msg = callee.vname ^ " preserves all memory" in
      Some (deps,msg)
    else
      begin
        poq#set_diagnostic
          ("memory may be freed by " ^ sym#getBaseName) ;
        None
      end

  method private validity_maintenance callvar =
    let calls = self#get_calls callvar in
    match calls with
    | Some [] ->
       let deps = DLocal []  in
       let msg = "no calls between receiving pointer and this location" in
       Some (deps,msg)
    | Some l ->
       let pres = List.map self#call_preserves_validity l in
       List.fold_left (fun acc call ->
           match acc with
           | None -> None
           | Some (deps,msg) ->
              match call with
              | Some (d,m) ->
                 let deps = join_dependencies deps d in
                 let msg = msg ^ "; " ^ m in
                 Some (deps,msg)
              | _ -> None) (List.hd pres) (List.tl pres)
    | None ->
       begin
         poq#set_diagnostic
           ("no call-record found for callvar: " ^ (p2s callvar#toPretty)) ;
         None
       end
         
  method check_safe =
    match self#validity_maintenance poq#env#get_fn_entry_call_var with
    | Some (deps,msg) ->
       begin
         poq#record_safe_result deps msg ;
         true
       end
    | _ -> false
    
  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_preserved_all_memory (poq:po_query_int) =
  let callinvs = poq#get_call_invariants in
  let _ = poq#set_diagnostic_call_invariants in
  let checker = new preserved_all_memory_checker_t poq callinvs in
  checker#check_safe || checker#check_violation || checker#check_delegation


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
open XprTypes
open XprToPretty
open Xsimplify
   
(* cchlib *)
open CCHBasicTypes
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil

(* cchpre *)
open CCHMemoryBase
open CCHPOPredicate
open CCHPreTypes
open CCHProofObligation
   
(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)

class stack_address_escape_checker_t
        (poq:po_query_int) (v:lval option) (e:exp) (invs:invariant_int list) =
object (self)

  method private memref_to_string memref =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))
    
  (* ----------------------------- safe ------------------------------------- *)

  method private var_implies_safe invindex v =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,_) = poq#get_postconditions v in
      let _ = poq#set_diagnostic ("return value from " ^ callee.vname) in
      List.fold_left (fun acc (pc,_) ->
          match acc with
          | Some _ -> acc
          | _ ->
             match pc with
             | XHeapAddress ReturnValue ->
                let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                let msg = "return value from "  ^ callee.vname ^ " is a heap address: "
                          ^ "allowed to leave local scope" in
                Some (deps,msg)
             | XGlobalAddress ReturnValue  ->
                let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                let msg = "return value from " ^ callee.vname ^ " is a global address: "
                          ^ "allowed to leave local scope" in
                Some (deps,msg)
             | _ -> None) None pcs
    else if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      let _ = poq#set_diagnostic_arg 2 (self#memref_to_string memref) in
      begin
        match memref#get_base with
        | CGlobalAddress _ ->
           let deps = DLocal [ invindex ] in
           let msg = "global address " ^  (self#memref_to_string memref)
                     ^ " is allowed to leave local scope" in
           Some (deps,msg)
        | CStringLiteral _ ->
           let deps = DLocal [ invindex ] in
           let msg = "string literal " ^ (self#memref_to_string memref)
                     ^ " is allowed to leave local scope" in
           Some (deps,msg)
        | CBaseVar v -> self#var_implies_safe invindex v
        | _ -> None
      end
    else
      None
      

  method private xpr_implies_safe invindex x =
    match x with
    | XVar v -> self#var_implies_safe invindex v
    | XOp (XPlus, [ xbase ; xinc ]) ->
       begin
         match self#xpr_implies_safe invindex xbase with
         | Some (deps,msg) ->
            let msg = msg ^ " (with offset: " ^ (x2s xinc) ^ ")" in
            Some (deps,msg)
         | _ -> None
       end
    | _ -> None

  method private inv_implies_safe inv =
    match (v,inv#expr) with
    | (None,Some x) when poq#is_api_expression x ->
       let deps = DLocal [ inv#index ] in
       let msg =
         "value: " ^ (x2s x)
         ^ " received from caller is returned to caller" in
       Some (deps,msg)
    | (None,Some (XVar v)) when poq#env#is_memory_address v ->
       let (memref,_) = poq#env#get_memory_address v in
       let _ = poq#set_diagnostic_arg 2 (self#memref_to_string memref) in
       begin
         match memref#get_base with
         | CBaseVar v when poq#is_api_expression (XVar v) ->
            let deps = DLocal [ inv#index ] in
            let msg =
              "address " ^ (x2s (XVar v))
              ^ " received from caller is returned to caller" in
            Some (deps,msg)
         | CBaseVar v -> self#var_implies_safe inv#index v
         | CStringLiteral _ ->
            let deps = DLocal [ inv#index ] in
            let msg = "string literal " ^ (self#memref_to_string memref)
                      ^ " is allowed to leave local scope" in
            Some (deps,msg)
         | _ -> None
       end
    | _ ->
       match inv#lower_bound_xpr with
       | Some x -> self#xpr_implies_safe inv#index x
       | _ ->
          match inv#lower_bound_xpr_alternatives with
          | None | Some [] -> None
          | Some (h::tl) ->
             begin
               match  self#xpr_implies_safe inv#index h  with
               | None -> None
               | Some r ->
                  List.fold_left (fun acc x ->
                      match acc with
                      | None -> None
                      | Some (deps,msg) ->
                         begin
                           match self#xpr_implies_safe inv#index x with
                           | Some (d,m) ->
                              let deps = join_dependencies deps d in
                              let msg = msg  ^  "; " ^  m in
                              Some (deps,msg)
                           | _ -> None
                         end) (Some r) tl
             end
            
  method check_safe =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_safe inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg ;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- violation -------------------------------------- *)

  method private xpr_implies_violation invindex x =
    match x with
    | XVar v when poq#env#is_function_return_value v ->
       let callee = poq#env#get_callvar_callee v in
       let (pcs,epcs) = poq#get_postconditions v in
       List.fold_left (fun acc (pc,_) ->
           match acc with
           | Some _ -> acc
           | _ ->
              match pc with
              | XStackAddress ReturnValue ->
                 let deps = DEnvC ([ invindex ],[ PostAssumption (callee.vid,pc) ]) in
                 let msg =
                   "return value from " ^ callee.vname ^ " is address of "
                   ^ " stack-allocated memory: it cannot leave scope" in
                 Some (deps,msg)
              | _ -> None) None (pcs @ epcs)
    | XVar v when poq#env#is_memory_address v ->
       let memref = poq#env#get_memory_reference v in
       let _ = poq#set_diagnostic_arg 2  (self#memref_to_string memref) in
       begin
         match memref#get_base with
         | CStackAddress _ ->
            let deps = DLocal [ invindex ] in
            let msg =
              "stack address " ^ (self#memref_to_string memref)
              ^ " should not leave scope" in
            Some (deps,msg)
         | CBaseVar v -> self#xpr_implies_violation invindex (XVar v)
         | _ -> None
       end
    | XOp (_, [ xbase ; xinc ]) -> self#xpr_implies_violation invindex xbase
    | _ -> None
                 

  method private inv_implies_existential_violation inv =
    match inv#lower_bound_xpr with
    | Some x -> self#xpr_implies_violation inv#index x
    | _ ->
       match inv#lower_bound_xpr_alternatives with
       | Some l ->
          List.fold_left (fun acc x ->
              match acc with
              | Some _ -> acc
              | _ ->  self#xpr_implies_violation inv#index x) None l
       | _ -> None
            
  method check_violation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_existential_violation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_violation_result deps msg ;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- delegation ------------------------------------- *)

  method private inv_implies_delegation inv =
    match (v,inv#expr) with
    | _ -> None
         
  method check_delegation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_delegation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg  ;
                  true
                end
             | _ -> false) false invs

end
  
let check_stack_address_escape (poq:po_query_int) (v:lval option) (e:exp) =
  let invs = poq#get_invariants 2 in
  let _ = poq#set_diagnostic_invariants 2 in
  let checker = new stack_address_escape_checker_t poq v e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

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
   
(* chutil *)
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open Xsimplify

(* cchlib *)
open CCHBasicTypes
open CCHTypesToPretty

(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open  CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class buffer_checker_t
        (poq:po_query_int)
        (e1:exp)
        (e2:exp)
        (invs1:invariant_int list)
        (invs2:invariant_int list) =
object (self)
  (* ----------------------------- safe ------------------------------------- *)

  method private xpr_implies_safe inv1index inv2index x1 x2 =
    match poq#xpr_buffer_offset_size 1 inv1index x1 with
    | Some (gname, xsize, xoffset, deps) ->
       let xconstraint = XOp (XGe, [ XOp (XMinus, [ xsize ; xoffset ]) ; x2 ]) in
       let sconstraint = simplify_xpr xconstraint in
       if is_true sconstraint then
         let msg = "buffer: " ^ gname ^ " has size: " ^ (x2s xsize)  ^ " and offset: "
                   ^ (x2s xoffset) ^ ", which satisfies safety constraint: "
                   ^ (x2s xconstraint)  in
         Some (deps,msg)
       else
         begin
           poq#set_diagnostic ("remaining constraint: "  ^ (x2s sconstraint)) ;
           None
         end
    | _ -> None
       
  method private inv_implies_safe inv1 inv2 =
    match (inv1#expr,inv2#upper_bound_xpr) with
    | (Some x1, Some x2) -> self#xpr_implies_safe inv1#index inv2#index x1 x2
    | _ -> None
         
  method check_safe =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_safe inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_safe_result deps msg ;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1
      
  (* ----------------------- violation -------------------------------------- *)

  method private xpr_implies_violation inv1index inv2index x1 x2 =
    match poq#xpr_buffer_offset_size 1 inv1index x1 with
    | Some (gname, xsize, xoffset, deps) ->
       let vconstraint = XOp (XLt, [ XOp (XMinus, [ xsize ; xoffset ]) ; x2 ]) in
       let safeconstraint = XOp (XGe, [ XOp (XMinus, [ xsize ; xoffset ]) ; x2 ]) in
       let sconstraint = simplify_xpr vconstraint in
       if is_true sconstraint then
         let msg = "buffer: " ^ gname ^ " has size: " ^ (x2s xsize)  ^ " and offset: "
                   ^ (x2s xoffset) ^ ", which violates safety constraint: "
                   ^ (x2s safeconstraint) in
         Some (deps,msg)
       else
         None
    | _ -> None

  method private inv_implies_violation inv1 inv2 =
    match (inv1#expr,inv2#upper_bound_xpr) with
    | (Some x1, Some x2) -> self#xpr_implies_violation inv1#index inv2#index x1 x2
    | _ -> None
         
  method check_violation =
    match (invs1,invs2) with
    | ([],_) | (_,[]) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_violation inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_violation_result deps msg ;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1
                       
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_buffer (poq:po_query_int) (e1:exp) (e2:exp) =
  let invs1 = poq#get_invariants 1 in
  let invs2 = poq#get_invariants 2 in
  let _ = poq#set_diagnostic_invariants 1 in
  let _ = poq#set_diagnostic_invariants 2 in
  let checker = new buffer_checker_t poq e1 e2 invs1 invs2 in
  checker#check_safe || checker#check_violation || checker#check_delegation

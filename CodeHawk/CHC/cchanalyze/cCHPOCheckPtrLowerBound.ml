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
open CHLanguage
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
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil

(* cchpre *)
open CCHPOPredicate
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class ptr_lower_bound_checker_t
        (poq: po_query_int)
        (typ: typ)
        (op: binop)
        (e1: exp)
        (e2: exp)
        (invs1: invariant_int list)
        (invs2: invariant_int list) =
object (self)

  method private mk_predicate (a1: exp) (a2: exp): po_predicate_t =
    PPtrLowerBound (typ, op, a1, a2)

  (* ----------------------------- safe ------------------------------------- *)

  method private inv12_implies_safe (_inv1: invariant_int) (_inv2: invariant_int) =
    None

  method private x2_implies_safe (invindex: int) (x: xpr_t) =
    let deps = DLocal [invindex] in
    match x with
    | XConst (IntConst n) when n#geq numerical_zero ->
       let msg = "non-negative increment: " ^ n#toString in
       Some (deps, msg)
    | _ -> None

  method private inv2_implies_safe (inv: invariant_int) =
    match inv#lower_bound_xpr with
    | Some x -> self#x2_implies_safe inv#index x
    | _ -> None

  method private check_pluspi_safe =
    match invs2 with
    | [] ->
       begin
         poq#set_diagnostic ("no invariants for " ^ (e2s e2));
         false
       end
    | _ ->
       (List.fold_left (fun acc inv ->
           acc ||
             match self#inv2_implies_safe inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs2)
       ||
         (List.fold_left (fun acc1 inv1 ->
              acc1 ||
                List.fold_left (fun acc2 inv2 ->
                    acc2 ||
                      match self#inv12_implies_safe inv1 inv2 with
                      | Some (deps,msg) ->
                         begin
                           poq#record_safe_result deps msg;
                           true
                         end
                      | _ -> false) acc1 invs2) false invs1)

  method private check_minuspi_safe = false

  method check_safe =
    match op with
    | PlusPI | IndexPI -> self#check_pluspi_safe
    | MinusPI -> self#check_minuspi_safe
    | _ -> false

  (* ----------------------- violation -------------------------------------- *)

  method private xpr_implies_minuspi_universal_violation
                   (invindices: int list) (x1: xpr_t) (x2: xpr_t) =
    match (x1, x2) with
    | (XVar v, XConst (IntConst n)) when poq#env#is_function_return_value v ->
       let callee = poq#env#get_callvar_callee v in
       let (pcs,epcs) = poq#get_postconditions v in
       List.fold_left (fun acc (pc, _) ->
           let deps = DEnvC (invindices,[PostAssumption (callee.vid, pc)]) in
           match acc with
           | Some _ -> acc
           | _ ->
              match pc with
              | XRevBuffer (ReturnValue, NumConstant b) when n#gt b ->
                 let msg =
                   "decrement: "
                   ^ n#toString
                   ^ " violates lower bound: "
                   ^ b#toString
                   ^ " of buffer returned by "
                   ^ callee.vname in
                 Some (deps,msg)
              | _ -> None) None (pcs @ epcs)
    | (XVar v, _) when poq#env#is_memory_address v ->
       let (memref, offset) = poq#env#get_memory_address v in
       begin
         match (memref#get_base, offset) with
         | (CBaseVar basevar, NoOffset) ->
            self#basevar_implies_minuspi_universal_violation
              invindices basevar numerical_zero x2
         | _ -> None
       end
    | _ -> None

  method private basevar_implies_minuspi_universal_violation
                   (invindices: int list)
                   (v: variable_t)
                   (offsetlb: numerical_t)
                   (decr: xpr_t) =
    let xoff = num_constant_expr offsetlb in
    let check_rv_offset callee deps b =
      let xbneg = num_constant_expr b#neg in
      let vconstraint = XOp (XLt, [XOp (XMinus, [xoff; decr]); xbneg]) in
      let sconstraint = simplify_xpr vconstraint in
      if is_true sconstraint then
        let msg =
          "offset: "
          ^ offsetlb#toString
          ^ " minus decr: "
          ^ (x2s decr)
          ^ " violates lower bound: "
          ^ b#toString
          ^ " of the buffer returned by: "
          ^ callee.vname in
        Some (deps, msg)
      else
        None in
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs, _) = poq#get_postconditions v  in
      List.fold_left (fun acc (pc,_) ->
          let deps = DEnvC (invindices, [PostAssumption (callee.vid, pc)]) in
          match acc with
          | Some _ -> acc
          | _ ->
             match pc with
             | XRevBuffer (ReturnValue, NumConstant b) ->
                check_rv_offset callee deps b
             | XAllocationBase ReturnValue ->
                check_rv_offset callee deps numerical_zero
             | _ -> None) None pcs
    else if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      begin
        match memref#get_base with
        | CStackAddress stackvar when poq#env#is_local_variable stackvar ->
           let (vinfo, _) = poq#env#get_local_variable stackvar in
           let deps = DLocal invindices in
           let vconstraint = XOp (XGt, [decr; xoff]) in
           let sconstraint = simplify_xpr vconstraint in
           if is_true sconstraint then
             let msg =
               "offset: "
               ^ offsetlb#toString
               ^ " minus decr: "
               ^ (x2s decr)
               ^ " violates lower bound of stack variable: "
               ^ vinfo.vname in
             Some (deps, msg)
           else
             None
        | CBaseVar v ->
           self#basevar_implies_minuspi_universal_violation
             invindices v offsetlb decr
        | _ -> None
      end
    else
      None

  method private xpr_implies_pluspi_universal_violation
                   (_invindices: int list) (_x1: xpr_t) (_x2: xpr_t) =
    None

  method private basevar_implies_pluspi_universal_violation
                   (invindices: int list)
                   (v: variable_t)
                   (offsetub: numerical_t)
                   (incr: xpr_t) =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs, _) = poq#get_postconditions v in
      List.fold_left (fun acc (pc, _) ->
          let deps  = DEnvC (invindices, [PostAssumption (callee.vid, pc)]) in
          match acc with
          | Some _ -> acc
          | _ ->
             match pc with
             | XAllocationBase ReturnValue ->
                let vconstraint = XOp (XLt, [incr; zero_constant_expr]) in
                let sconstraint = simplify_xpr vconstraint in
                if is_true sconstraint then
                  let msg =
                    "increment "
                    ^ (x2s incr)
                    ^ " violates lower bound 0 "
                    ^ "of the buffer returned by: "
                    ^ callee.vname in
                  Some (deps, msg)
                else
                  None
             | _ -> None) None pcs
    else if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      begin
        match memref#get_base with
        | CBaseVar v ->
           self#basevar_implies_pluspi_universal_violation
             invindices v offsetub incr
        | _ -> None
      end
    else
      None

  method private inv_implies_minuspi_universal_violation
                   (inv1: invariant_int) (inv2: invariant_int) =
    match (inv1#base_offset_value, inv2#lower_bound_xpr) with
    | (Some (_,XVar v,Some lb, _, _), Some decr) ->
       self#basevar_implies_minuspi_universal_violation
         [inv1#index; inv2#index] v lb decr
    | _ ->
       match (inv1#upper_bound_xpr,inv2#lower_bound_xpr) with
       | (Some x1, Some x2) ->
          self#xpr_implies_minuspi_universal_violation
            [inv1#index; inv2#index] x1 x2
       | _ -> None

  method private inv_implies_pluspi_universal_violation
                   (inv1: invariant_int) (inv2: invariant_int) =
    match (inv1#base_offset_value, inv2#upper_bound_xpr) with
    | (Some (_,XVar v, _, Some ub, _), Some incr) ->
       self#basevar_implies_pluspi_universal_violation
         [inv1#index; inv2#index] v ub incr
    | _ ->
       match (inv1#upper_bound_xpr, inv2#upper_bound_xpr) with
       | (Some x1, Some x2) ->
          self#xpr_implies_pluspi_universal_violation
            [inv1#index; inv2#index] x1 x2
       | _ -> None

  method private check_pluspi_violation =
    match (invs1, invs2) with
    |  ([], _) | (_, []) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_pluspi_universal_violation inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_violation_result deps msg;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1

  method private check_minuspi_violation =
    match (invs1, invs2) with
    | ([], _) | (_, []) -> false
    | _ ->
       List.fold_left (fun acc1 inv1 ->
           acc1 ||
             List.fold_left (fun acc2 inv2 ->
                 acc2 ||
                   match self#inv_implies_minuspi_universal_violation inv1 inv2 with
                   | Some (deps,msg) ->
                      begin
                        poq#record_violation_result deps msg;
                        true
                      end
                   | _ -> false) acc1 invs2) false invs1

  method check_violation =
    match op  with
    | PlusPI | IndexPI -> self#check_pluspi_violation
    | MinusPI -> self#check_minuspi_violation
    | _ -> false
  (* ----------------------- delegation ------------------------------------- *)

  method private xpr_implies_delegation
                   (inv1index: int) (inv2index: int) (x1: xpr_t) (x2: xpr_t) =
    match (poq#x2api x1, poq#x2api x2) with
    | (Some a1, Some a2)
         when poq#is_api_expression x1 || poq#is_api_expression x2 ->
       let pred = self#mk_predicate a1 a2 in
       let deps = DEnvC ([inv1index; inv2index],[ApiAssumption pred]) in
       let msg =
         "condition "
         ^ (p2s (po_predicate_to_pretty pred))
         ^ " delegated to the api" in
       Some (deps, msg)
    | _ -> None

  method private inv_implies_delegation
                   (inv1: invariant_int) (inv2: invariant_int) =
    match (inv1#expr, inv2#expr) with
    |  (Some x1, Some x2) ->
        self#xpr_implies_delegation inv1#index inv2#index x1 x2
    | _ -> None

  method private check_pluspi_delegation_xpr2
                   (_vname: string)
                   (xoffset: xpr_t)
                   (_deps1: dependencies_t)
                   (inv2index: int)
                   (x2: xpr_t) =
    let typesize = size_of_type poq#fenv typ in
    let xbyteincr = simplify_xpr (XOp (XMult, [x2; typesize])) in
    let totaloffset = simplify_xpr (XOp (XPlus, [xoffset;  xbyteincr])) in
    let xconstraint = XOp (XGe, [totaloffset; zero_constant_expr]) in
    let sconstraint = simplify_xpr xconstraint in
    if poq#is_api_expression sconstraint then
      let aconstraint = poq#get_api_expression sconstraint in
      let pred = PValueConstraint aconstraint in
      let deps = DEnvC ([inv2index], [ApiAssumption pred]) in
      let msg =
        "constraint "
        ^ (p2s (po_predicate_to_pretty pred))
        ^ "delegated to the api" in
      Some (deps, msg)
    else
      None

  method private invs2_implies_pluspi_delegation
                   (vname: string) (xoffset: xpr_t) (deps1: dependencies_t) =
    List.fold_left  (fun acc inv2 ->
        match acc with
        | Some _ -> acc
        | _ ->
           match inv2#upper_bound_xpr with
           | Some xincr ->
              self#check_pluspi_delegation_xpr2
                vname xoffset deps1 inv2#index xincr
           | _ -> None) None invs2

  method check_delegation =
    match (invs1,invs2) with
    | ([], _) | (_, []) -> false
    |  _ ->
        List.fold_left (fun acc1 inv1 ->
            acc1 ||
              List.fold_left (fun acc2 inv2 ->
                  acc2 ||
                    match self#inv_implies_delegation inv1 inv2 with
                    | Some (deps,msg) ->
                       begin
                         poq#record_safe_result deps msg;
                         true
                       end
                    | _ ->
                       match op with
                       | PlusPI | IndexPI ->
                          begin
                            match poq#get_buffer_offset_size 3 typ e1 with
                            | Some (vname,_,xoffset,deps1) ->
                               begin
                                 match self#invs2_implies_pluspi_delegation
                                         vname xoffset deps1 with
                                 | Some (deps,msg) ->
                                    begin
                                      poq#record_safe_result deps msg;
                                      true
                                    end
                                 | _ -> false
                               end
                            | _ -> false
                          end
                       | _ -> false) acc1 invs2) false invs1
end


let check_ptr_lower_bound
      (poq: po_query_int) (typ: typ) (op: binop) (e1: exp) (e2: exp) =
  let invs1 = poq#get_invariants 3 in
  let invs2 = poq#get_invariants 4 in
  let _ = poq#set_diagnostic_invariants 3 in
  let _ = poq#set_diagnostic_invariants 4 in
  let checker = new ptr_lower_bound_checker_t poq typ op e1 e2 invs1 invs2 in
  checker#check_safe || checker#check_violation || checker#check_delegation

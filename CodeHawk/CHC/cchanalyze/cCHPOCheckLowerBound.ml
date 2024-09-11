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


class lower_bound_checker_t
        (poq: po_query_int)
        (typ: typ)
        (e: exp)
        (invs: invariant_int list)  =
object (self)

  method private memref_to_string (memref: memory_reference_int) =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  (* ----------------------------- safe ------------------------------------- *)

  method private memref_implies_safe
                   (invindex: int) (memref: memory_reference_int) =
    let deps = DLocal [invindex] in
    let _ =
      poq#set_diagnostic_arg
        2 ("memory address: " ^ self#memref_to_string memref) in
    match memref#get_base with
    | CGlobalAddress gvar ->
       let (gvinfo, _offset) = poq#env#get_global_variable gvar in
       let msg = "address of global variable: " ^ gvinfo.vname in
       Some (deps, msg)
    | CStringLiteral _ ->
       let msg = "address of a string literal" in
       Some (deps, msg)
    | CStackAddress svar ->
       let (vinfo, _offset) = poq#env#get_local_variable svar in
       let msg = "address of stack variable: " ^ vinfo.vname in
       Some (deps, msg)
    | CBaseVar svar ->
       let msg =
         "address of externally provided variable/field: "
         ^ svar#getName#getBaseName in
       Some (deps, msg)
    | _ ->
       None

  method private var_implies_safe (invindex: int) (v: variable_t) =
    let deps = DLocal [invindex] in
    if poq#env#is_initial_parameter_value v then
       let par = poq#env#get_initial_value_variable v in
       let msg =
         "initial value of parameter: "
         ^ par#getName#getBaseName
         ^ " satisfies lower bound by IH" in
       Some (deps, msg)
    else if poq#env#is_initial_global_value v then
      let var = poq#env#get_initial_value_variable v in
      let msg =
        "initial value of global value: "
        ^ var#getName#getBaseName
        ^ " satisfies lower bound by IH" in
      Some (deps, msg)    (* TBD: check intervening calls *)
    else if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let msg =
        "return value from function "
        ^ callee.vname
        ^ " satisfies lower bound by IH" in
      Some (deps, msg)
    else if poq#env#is_memory_address v then
      let (memref,offset) = poq#env#get_memory_address v in
      match offset with
      | NoOffset -> self#memref_implies_safe invindex memref
      | _ ->
         match self#memref_implies_safe invindex memref with
         | Some (deps,msg) ->
            let msg =
              "offset: "
              ^ (p2s (offset_to_pretty offset))
              ^ ";  "
              ^ msg in
            Some (deps, msg)
         | _ -> None
    else
      None

  method private xpr_implies_safe (invindex: int) (x: xpr_t) =
    let deps = DLocal [invindex] in
    match x with
    | XConst (IntConst n) when n#equal numerical_zero ->
       let msg = "value is null pointer" in
       Some (deps, msg)
    | XConst (IntConst n) when n#gt numerical_zero ->
       let msg = "absolute memory address: " ^ n#toString in
       Some (deps, msg)
    | XVar v -> self#var_implies_safe invindex v
    | XOp (XPlus, [XVar v; XConst (IntConst n)]) when n#geq numerical_zero ->
       begin
         match self#var_implies_safe invindex v with
         | Some (deps,msg) ->
            let msg = msg ^ " with non-negative increment: " ^ n#toString in
            Some (deps, msg)
         | _ -> None
       end
    | _ -> None

  method private xprlist_implies_safe (invindex: int)  (l: xpr_t list) =
    match l with
    | [] -> None
    | h::tl ->
       match self#xpr_implies_safe invindex h with
       | None -> None
       | Some r ->
          List.fold_left (fun acc x ->
              match acc with
              | None -> None
              | Some (deps, msg) ->
                 match self#xpr_implies_safe invindex x with
                 | Some (d, m) ->
                    let deps = join_dependencies deps d in
                    let msg = msg ^ "; " ^ m in
                    Some (deps, msg)
                 | _ -> None) (Some r) tl

  method private inv_implies_safe (inv: invariant_int) =
    match inv#lower_bound_xpr with
    | Some x -> self#xpr_implies_safe inv#index x
    | _ ->
       match inv#base_offset_value with
       | Some (_, XVar v, Some lb, _,_ ) when lb#geq numerical_zero ->
          begin
            match self#var_implies_safe inv#index v with
            | Some (deps,msg) ->
               let msg = msg ^ " (with non-negative offset)" in
               Some (deps,msg)
            | _ ->
               match inv#lower_bound_xpr_alternatives with
               | Some l -> self#xprlist_implies_safe inv#index l
               | _ -> None
          end
       | _ ->
          match inv#lower_bound_xpr_alternatives with
          | Some l -> self#xprlist_implies_safe inv#index l
          | _ -> None

  method check_safe =
    match invs with
    | [] ->
       begin
         poq#set_diagnostic ("no invariants found for " ^ (e2s e));
         false
       end
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_safe inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- violation -------------------------------------- *)

  method private memref_offset_implies_universal_violation
                   (invindex: int)
                   (memref: memory_reference_int)
                   (xoffset: xpr_t) =
    let deps = DLocal [invindex] in
    match memref#get_base with
    | CGlobalAddress gvar ->
       let (gvinfo, offset) = poq#env#get_global_variable gvar in
       begin
         match offset with
         | NoOffset ->
            let vconstraint = XOp (XLt, [xoffset; zero_constant_expr]) in
            let sconstraint = simplify_xpr vconstraint in
            if is_true sconstraint then
              let msg =
                "negative offset from base of global variable: "
                ^ gvinfo.vname in
              Some (deps, msg)
            else
              None
         | _ -> None
       end
    | CStackAddress svar ->
       let (vinfo, offset) = poq#env#get_local_variable svar in
       begin
         match offset with
         | NoOffset ->
            let vconstraint = XOp (XLt, [xoffset; zero_constant_expr]) in
            let sconstraint = simplify_xpr vconstraint in
            if is_true sconstraint then
              let msg  =
                "negative offset from base of stack variable: "
                ^ vinfo.vname  in
              Some (deps, msg)
            else
              None
         | _ -> None
       end
    | CBaseVar v ->
       self#var_offset_implies_universal_violation invindex v xoffset
    | _ -> None

  method private var_offset_implies_universal_violation
                   (invindex: int) (v: variable_t) (xoffset: xpr_t) =
    if poq#env#is_memory_address v then
      let memref = poq#env#get_memory_reference v in
      self#memref_offset_implies_universal_violation invindex memref xoffset
    else if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let (pcs,_) = poq#get_postconditions v in
      List.fold_left (fun acc (pc, _) ->
          match acc with
          | Some _ -> acc
          | _ ->
             match pc with
             | XRevBuffer (ReturnValue, NumConstant n) ->
                let xallowedoffset = num_constant_expr n#neg in
                let vconstraint = XOp (XLt, [xoffset; xallowedoffset]) in
                let sconstraint = simplify_xpr vconstraint in
                if is_true sconstraint then
                  let deps = DEnvC ([invindex],[PostAssumption (callee.vid,pc)]) in
                  let msg =
                    Printf.sprintf
                      "increment %s violates the lower bound: %s of the buffer returned by %s"
                      (x2s xoffset) (x2s xallowedoffset) callee.vname in
                  Some (deps, msg)
                else
                  None
             | _ -> None)  None pcs
    else
      None

  method private xpr_implies_universal_violation invindex x =
    match x with
    | XConst (IntConst n) when n#lt numerical_zero ->
       let deps = DLocal [invindex] in
       let msg = "value: " ^ n#toString  ^ "  violates zero lower bound" in
       Some (deps,msg)
    | XVar v -> self#var_offset_implies_universal_violation invindex v zero_constant_expr
    | XOp (XPlus, [XVar v; xincr]) ->
       self#var_offset_implies_universal_violation invindex v xincr
    | XOp (XMinus, [XVar v; xdecr]) ->
       let xincr = simplify_xpr (XOp (XMinus, [zero_constant_expr; xdecr])) in
       self#var_offset_implies_universal_violation invindex v xincr
    | _ -> None

  method private inv_implies_universal_violation inv =
    match  inv#upper_bound_xpr with
    | Some x -> self#xpr_implies_universal_violation inv#index x
    | _  -> None

  method check_violation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_universal_violation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_violation_result deps msg;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- delegation ------------------------------------- *)

  method private inv_implies_delegation inv =
    match inv#expr with
    | Some x when poq#is_api_expression x ->
       let pred = PLowerBound (typ, poq#get_api_expression x) in
       let deps = DEnvC ([inv#index],[ApiAssumption pred]) in
       let msg = "condition " ^ (p2s (po_predicate_to_pretty pred))
               ^ " delegated to the api" in
       Some (deps,msg)
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
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs
end


let check_lower_bound (poq:po_query_int) (typ:typ) (e:exp) =
  let invs = poq#get_invariants 2 in
  let _ = poq#set_diagnostic_invariants 2 in
  let checker = new lower_bound_checker_t poq typ e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

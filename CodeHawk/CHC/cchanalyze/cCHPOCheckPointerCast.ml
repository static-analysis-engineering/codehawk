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
open CCHTypesUtil
open CCHTypesToPretty

(* cchpre *)
open CCHMemoryBase
open CCHPOPredicate
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class pointer_cast_checker_t
        (poq: po_query_int)
        (tfrom: typ)
        (tto: typ)
        (e: exp)
        (invs: invariant_int list) =
object (self)

  val ttosize = size_of_type poq#fenv tto
  val tfromsize = size_of_type poq#fenv tfrom

  method private mk_predicate (a: exp): po_predicate_t =
    PPointerCast (tfrom, tto, a)

  method private size_warning (typsize: xpr_t) (bufsize: xpr_t) =
    match (typsize, bufsize) with
    | (XConst (IntConst t), _) when t#equal numerical_zero ->
       "warning: type size is zero"
    | (XConst (IntConst t), XConst (IntConst b)) when t#gt numerical_zero ->
       if (b#modulo t)#equal numerical_zero then
         ""
       else
         " (warning: buffer size: "
         ^ b#toString
         ^ " is not an integral multiple of element size: "
         ^ t#toString
         ^ ")"
    | _ -> ""

  method private size_msg callee (typsize: xpr_t) (bufsize: xpr_t)  =
    match (typsize, bufsize) with
    | (XConst (IntConst t), XConst (IntConst b)) when t#gt numerical_zero ->
       let elementcount = b#div t in
       let msg =
         "size of buffer: "
         ^ b#toString
         ^ " returned by: "
         ^ callee
         ^ " is sufficient to hold "
         ^ elementcount#toString
         ^ " elements of target type: "
         ^ (p2s (typ_to_pretty tto))
         ^ " with size: "
         ^ t#toString in
       Some (msg ^ self#size_warning typsize bufsize)
    | _ -> None

  method private memref_to_string (memref: memory_reference_int) =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  (* ----------------------------- safe ------------------------------------- *)

  method private declared_variable_implies_safe
                   (isglobal: bool)
                   (invindex: int)
                   (vinfo: varinfo)
                   (voffset: offset) =
    let pvar = if isglobal then "global" else "local" in
    match voffset with
    | NoOffset ->
       let vsize = size_of_type poq#fenv vinfo.vtype in
       let xconstraint = XOp  (XGe, [vsize; ttosize]) in
       let sconstraint = simplify_xpr xconstraint in
       if is_true sconstraint then
         let deps = DLocal [invindex] in
         let msg =
           pvar
           ^ " variable: "
           ^ vinfo.vname
           ^ " has size: "
           ^ (x2s vsize)
           ^ ", which is sufficient to hold at least one element of targetttype: "
           ^ (p2s (typ_to_pretty tto))
           ^ " with size: "
           ^ (x2s ttosize)  in
         Some (deps, msg)
       else
         begin
           poq#set_diagnostic
             (pvar ^ " variable: remaining constraint: " ^ (x2s sconstraint));
             None
         end
    | _ ->
       begin
         poq#set_diagnostic
           (pvar ^ " variable with offset: " ^ (p2s (offset_to_pretty voffset)));
         None
       end

  method private memref_implies_safe
                   (invindex: int) (memref: memory_reference_int) =
    let _ =
      poq#set_diagnostic_arg
        3 ("memory address: " ^ (self#memref_to_string memref)) in
    match memref#get_base with
    | CGlobalAddress gvar ->
       let (gvinfo, offset) = poq#env#get_global_variable gvar in
       self#declared_variable_implies_safe true invindex gvinfo offset
    | CStackAddress svar ->
       let (vinfo, offset) = poq#env#get_local_variable svar in
       self#declared_variable_implies_safe false invindex vinfo offset
    | CBaseVar v -> self#var_implies_safe invindex  v
    | _ -> None

  method private var_implies_safe (invindex: int) (v: variable_t) =
    if poq#env#is_function_return_value v then
      let callee = poq#env#get_callvar_callee v in
      let _ =
        poq#set_diagnostic_arg
          3 ("function return value from: " ^ callee.vname) in
      match poq#get_function_return_value_buffer_size v with
      | Some (assumptions,xsize) ->
         let xconstraint = XOp (XGe, [xsize; ttosize]) in
         let sconstraint = simplify_xpr xconstraint in
         if is_true sconstraint then
           let deps = DEnvC ( [invindex], assumptions) in
           let msg =
             match self#size_msg callee.vname ttosize xsize with
             | Some msg -> msg
             | _ ->
                "size of buffer: "
                ^ (x2s xsize)
                ^ " returned by: "
                ^ callee.vname
                ^ " is sufficient to hold at least one element of targettype: "
                ^ (p2s (typ_to_pretty tto))
                ^ " with size: "
                ^ (x2s ttosize) in
           Some (deps,msg)
         else
           begin
             poq#set_diagnostic ("remaining constraint: " ^ (x2s sconstraint));
             None
           end
      | _ -> None
    else if poq#env#is_memory_address v then
      let (memref, offset) = poq#env#get_memory_address v in
      match offset with
      | NoOffset -> self#memref_implies_safe invindex memref
      |  _ -> None
    else
      None

  method private xpr_implies_safe (invindex: int) (x: xpr_t) =
    match tfrom with
    | TVoid _ ->
       begin
         match x with
         | XVar v -> self#var_implies_safe invindex v
         | _ -> None
       end
    |  _ ->
        match x with
        | XVar v ->
           begin
             match self#var_implies_safe invindex v with
             | Some (deps, msg) ->
                let msg =
                  "cast from "
                  ^ (p2s (typ_to_pretty tfrom))
                  ^ " with size: "
                  ^ (x2s tfromsize)
                  ^ " is safe: "
                  ^  msg in
                Some (deps, msg)
             | _ -> None
           end
        | _ -> None

  method private inv_implies_safe inv =
    match inv#expr with
    | Some x -> self#xpr_implies_safe inv#index x
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
             | Some (deps, msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- violation -------------------------------------- *)

  method private var_implies_violation (invindex: int) (v: variable_t) =
    if poq#env#is_function_return_value v then
      match poq#get_function_return_value_buffer_size v with
      | Some (assumptions,xsize) ->
         let vconstraint = XOp (XLt, [xsize; ttosize]) in
         let sconstraint = simplify_xpr vconstraint in
         if is_true sconstraint then
           let deps = DEnvC ( [invindex], assumptions) in
           let msg =
             "buffer of size: "
             ^ (x2s xsize)
             ^ " is not large enough to hold one object with type size: "
             ^ (x2s ttosize) in
           Some (deps,msg)
         else
           None
      | _ -> None
    else if poq#env#is_memory_address v then
      let (memref,offset) = poq#env#get_memory_address v in
      match (memref#get_base,offset) with
      | (CBaseVar basevar, NoOffset) ->
         self#var_implies_violation invindex basevar
      | _ -> None
    else
      None

  method private xpr_implies_violation (invindex: int) (x: xpr_t) =
    match tfrom with
    | TVoid _ ->
       begin
         match x with
         | XVar v -> self#var_implies_violation (invindex: int) (v: variable_t)
         | _ -> None
       end
    | _ -> None

  method private inv_implies_violation (inv: invariant_int) =
    match inv#expr with
    | Some x -> self#xpr_implies_violation inv#index x
    | _ -> None

  method check_violation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_violation inv with
             | Some (deps,msg) ->
                begin
                  poq#record_violation_result deps msg;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- delegation ------------------------------------- *)

  method private memref_implies_delegation
                   (invindex: int) (memref: memory_reference_int) =
    match memref#get_base with
    | CBaseVar v -> self#var_implies_delegation invindex v
    | _ -> None

  method private var_implies_delegation (invindex: int) (v: variable_t) =
    if poq#env#is_memory_address v then
      let (memref,offset) = poq#env#get_memory_address v in
      match offset with
      | NoOffset -> self#memref_implies_delegation invindex memref
      | _ -> None
    else if poq#is_api_expression (XVar v) then
      let pred = self#mk_predicate (poq#get_api_expression (XVar v)) in
      let deps = DEnvC ([invindex],[ApiAssumption pred]) in
      let msg  =
        "condition "
        ^ (p2s (po_predicate_to_pretty pred))
        ^ " delegated to the api" in
      Some (deps, msg)
    else
      None

  method private xpr_implies_delegation (invindex: int) (x: xpr_t) =
    if poq#is_api_expression x then
      let pred = self#mk_predicate (poq#get_api_expression x) in
      let deps = DEnvC ([invindex],[ApiAssumption pred]) in
      let msg =
        "condition  "
        ^ (p2s (po_predicate_to_pretty pred))
        ^ " delegated to the api" in
      Some (deps, msg)
    else
      match x with
      | XVar v -> self#var_implies_delegation invindex v
      | _ -> None

  method private inv_implies_delegation (inv: invariant_int) =
    match inv#lower_bound_xpr with
    | Some x -> self#xpr_implies_delegation inv#index x
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


let check_pointer_cast (poq: po_query_int) (tfrom: typ) (tto: typ) (e: exp) =
  let invs = poq#get_invariants 3 in
  let _ = poq#set_diagnostic_invariants 3 in
  let checker = new pointer_cast_checker_t poq tfrom tto e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

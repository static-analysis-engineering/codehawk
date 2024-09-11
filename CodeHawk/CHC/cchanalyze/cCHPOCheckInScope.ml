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
open CHPretty

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHTypesToPretty

(* cchpre *)
open CCHMemoryBase
open CCHPreTypes
open CCHProofObligation

(* cchanalyze *)
open CCHAnalysisTypes


let p2s = pretty_to_string
let e2s e = p2s (exp_to_pretty e)


class in_scope_checker_t
        (poq:po_query_int)
        (e:exp)
        (invs:invariant_int list) =
object (self)

  val memregmgr = poq#env#get_variable_manager#memregmgr

  method private is_uninterpreted (s: symbol_t) =
    memregmgr#is_uninterpreted s#getSeqNumber

  method private plist (l: symbol_t list) =
    pretty_print_list
      l
      (fun s ->
        LBLOCK [STR (poq#env#get_region_name s#getSeqNumber); NL]) "[" "," "]"

  method private memref_to_string (memref: memory_reference_int) =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  method private var_address_to_string (vinfo: varinfo) (offset: offset) =
    let s_offset = match offset with
      | NoOffset -> " (no offset)"
      | o -> " " ^ (p2s (offset_to_pretty o)) in
    "address of variable: " ^ vinfo.vname ^ s_offset

  (* ----------------------------- safe ------------------------------------- *)

  method private region_implies_safe (invindex: int) (region: symbol_t) =
    let region = poq#env#get_memory_region region in
    self#memrefbase_implies_safe invindex region#get_memory_base

  method private regions_implies_safe
                   (invindex: int) (regions: symbol_t list) =
    if List.exists self#is_uninterpreted regions then
      begin
        poq#set_diagnostic_arg
          1 ("encountered undetermined regions: " ^ (p2s (self#plist regions)));
        None
      end
    else
      let regions = poq#remove_null_syms regions in
      match regions with
      | [] ->
         begin
           poq#set_diagnostic_arg 1 ("encountered empty set of regions");
           None
         end
      | h::tl ->
         match self#region_implies_safe invindex h with
         | None -> None
         | Some r  ->
            List.fold_left (fun acc r ->
                match acc with
                | None -> None
                | Some (deps, msg) ->
                   match self#region_implies_safe invindex r with
                   | Some (d,m) ->
                      let deps = join_dependencies deps d in
                      let msg = msg ^ "; " ^ m in
                      Some (deps, msg)
                   | _ -> None) (Some r) tl

  method private memrefbase_implies_safe
                   (invindex: int) (memrefbase: memory_base_t) =
    let deps = DLocal [invindex] in
    match memrefbase with
    | CStackAddress stackvar when poq#env#is_local_variable stackvar ->
       let (vinfo,offset) = poq#env#get_local_variable stackvar in
       let msg = self#var_address_to_string vinfo offset in
       Some (deps, msg)
    | CStringLiteral _ ->
       let msg = "value is address of a string literal" in
       Some (deps, msg)
    | CGlobalAddress gvar ->
       let (vinfo, offset) = poq#env#get_global_variable gvar in
       let msg = self#var_address_to_string vinfo offset in
       Some (deps, msg)
    | CBaseVar v -> self#var_implies_safe invindex v
    | _ -> None

  method private var_implies_safe (invindex: int) (v: variable_t) =
    let deps = DLocal [invindex] in
    if poq#env#is_function_return_value v then
       let callee = poq#env#get_callvar_callee v  in
       let msg =
         Printf.sprintf
           "return value from: %s is in scope by IH (checked at return)"
           callee.vname in
       Some (deps,msg)
    else if poq#is_api_expression (XVar v) then
      let msg =
        Printf.sprintf
          "variable: %s is an argument to the function" v#getName#getBaseName in
       Some (deps, msg)
    else if poq#env#is_initial_global_value v then
       let var = poq#env#get_initial_value_variable v in
       let msg =
         Printf.sprintf
           "initial value of %s is in scope by IH (checked at assignment)"
           var#getName#getBaseName in
       Some (deps, msg)
    else
      if poq#env#is_memory_address v then
        let memref = poq#env#get_memory_reference v in
        let _ =
          poq#set_diagnostic_arg
            1 ("memory address: " ^ (self#memref_to_string memref)) in
        self#memrefbase_implies_safe invindex memref#get_base
    else
      None

  method private xpr_implies_safe (invindex: int) (x: xpr_t) =
    match x with
    | XConst (IntConst n) when n#equal numerical_zero ->
       let deps = DLocal [invindex] in
       let msg = "NULL is in scope" in
       Some (deps, msg)
    | XVar v
      | XOp (_, [XVar v; _]) -> self#var_implies_safe invindex v
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
                    let deps = join_dependencies deps d  in
                    let msg = msg ^ "; " ^ m in
                    Some (deps, msg)
                 | _ -> None) (Some r) tl

  method private inv_implies_safe (inv: invariant_int) =
    let r = None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr with
         | Some x -> self#xpr_implies_safe inv#index x
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#base_offset_value with
         | Some (_,XVar v,_,_,_) -> self#var_implies_safe inv#index  v
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr_alternatives with
         | None | Some [] -> None
         | Some l -> self#xprlist_implies_safe inv#index l in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         if inv#is_regions then
           let regions = inv#get_regions in
           self#regions_implies_safe inv#index regions
         else
           None  in
    r

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
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_in_scope (poq: po_query_int) (e: exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let checker = new in_scope_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation

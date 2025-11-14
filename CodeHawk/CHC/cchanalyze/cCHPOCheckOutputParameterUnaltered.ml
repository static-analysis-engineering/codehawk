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

(* chlib *)
open CHLanguage

(* xprlib *)
open XprTypes

(* cchlib *)
open CCHBasicTypes

(* cchpre *)
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes


let x2p = XprToPretty.xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)
let _e2s e = p2s (CCHTypesToPretty.exp_to_pretty e)


let _fenv = CCHFileEnvironment.file_environment


class outputparameter_unaltered_checker_t
        (poq: po_query_int)
        (vinfo: varinfo)
        (_offset: offset)
        (invs: invariant_int list) =
object (self)

  method private vinfo = vinfo

  method private get_symbol_name (s: symbol_t) =
    s#getBaseName
    ^ (match s#getAttributes with
       | [] -> ""
       | l  -> "(" ^ (String.concat "" l) ^ ")")

  (* ------------------------------- safe ----------------------------------- *)
  (* check_safe
     - check_invs_safe
       - inv_implies_safe
         - inv_xpr_implies_safe
   *)

  method private inv_xpr_implies_safe (invindex: int) (xpr: xpr_t) =
    let mname = "inv_xpr_implies_safe" in
    let numv = poq#env#mk_program_var vinfo NoOffset NUM_VAR_TYPE in
    match xpr with
    | XVar v when poq#env#is_initial_parameter_deref_value v ->
       let paramvar = poq#env#get_initial_value_variable v in
       if poq#env#is_memory_variable paramvar then
         let (memref, _offset) = poq#env#get_memory_variable paramvar in
         (match memref#get_base with
          | CBaseVar base ->
             let basevar = poq#env#get_initial_value_variable base in
             if basevar#equal numv then
               let deps = DLocal ([invindex]) in
               let msg =
                 ("value of " ^ (x2s xpr) ^ " is equal to initial value of "
                  ^ "memory pointed to by parameter " ^ vinfo.vname) in
               let site = Some (__FILE__, __LINE__, mname) in
               Some (deps, msg, site)
             else
               begin
                 poq#set_diagnostic
                   ~site:(Some (__FILE__, __LINE__, mname))
                   ("value of " ^ " is not equal to initial value of "
                    ^ "memory pointed to by parameter " ^ vinfo.vname);
                 None
               end
          | memrefbase ->
             begin
               poq#set_diagnostic
                 ~site:(Some (__FILE__, __LINE__, mname))
                 ("[memory-base]: "
                  ^ (CCHMemoryBase.memory_base_to_string memrefbase));
               None
             end)
       else
         begin
           poq#set_diagnostic
             ~site:(Some (__FILE__, __LINE__, mname))
             ("[paramvar]: " ^ (p2s paramvar#toPretty));
           None
         end
    | _ ->
       begin
         poq#set_diagnostic
           ~site:(Some (__FILE__, __LINE__, mname)) ("[xpr]: " ^ (x2s xpr));
         None
       end

  method private inv_implies_safe (inv: invariant_int) =
    let mname = "inv_implies_safe" in
    match inv#get_fact with
    | NonRelationalFact (_, FSymbolicExpr x) ->
       self#inv_xpr_implies_safe inv#index x
    | _ ->
       begin
         poq#set_diagnostic
           ~site:(Some (__FILE__, __LINE__, mname))
           ("[inv]: " ^ (p2s inv#toPretty));
         None
       end

  method private check_invs_safe =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_safe inv with
             | Some (deps, msg, site) ->
                begin
                  poq#record_safe_result ~site deps msg;
                  true
                end
             | _ -> false) false invs

  (* --------------------------- violation ---------------------------------- *)
  (* check_violation
     - inv_implies_violation
   *)

  method private inv_implies_violation (inv: invariant_int) =
    let mname = "inv_implies_violation" in
    match inv#get_fact with
    | NonRelationalFact (_, FInitializedSet l) ->
       let localAssigns =
         List.filter (fun s -> not (s#getBaseName = "parameter")) l in
       begin
         match localAssigns with
         | [] -> None
         | _ ->
            let deps = DLocal [inv#index] in
            let msg =
              (String.concat
                 "_xx_" (List.map self#get_symbol_name localAssigns)) in
            let site = Some (__FILE__, __LINE__, mname) in
            Some (deps, msg, site)
       end
    | _ ->
       begin
         poq#set_diagnostic
           ~site:(Some (__FILE__, __LINE__, mname))
           ("[inv]: " ^ (p2s inv#toPretty));
         None
       end

  method check_safe =
    self#check_invs_safe

  method check_violation =
    List.fold_left (fun acc inv ->
        acc
        || (match self#inv_implies_violation inv with
            | Some (deps, msg, site) ->
               begin
                 poq#record_violation_result ~site deps msg;
                 true
               end
            | _ -> false)) false invs

end


let check_outputparameter_unaltered
      (poq:po_query_int) (vinfo: varinfo) (offset: offset) =
  let invs = poq#get_init_vinfo_mem_invariants vinfo offset in
  let _ =
    poq#set_init_vinfo_mem_diagnostic_invariants
      ~site:(Some (__FILE__, __LINE__, "check_outputparameter_unaltered"))
      vinfo
      offset in
  let _ =
    if (List.length invs) = 0 then
      poq#set_diagnostic
        ~site:(Some (__FILE__, __LINE__, "check_outputparameter_unaltered"))
        ("no invariants available at this location for " ^ vinfo.vname) in
  let checker = new outputparameter_unaltered_checker_t poq vinfo offset invs in
  checker#check_violation || checker#check_safe

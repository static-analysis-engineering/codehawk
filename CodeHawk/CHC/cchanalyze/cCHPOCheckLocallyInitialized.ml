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

(* chutil *)

(* xprlib *)
open XprTypes

(* cchlib *)
open CCHBasicTypes
open CCHTypesToPretty
open CCHTypesUtil

(* cchpre *)
open CCHMemoryBase
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes


let x2p = XprToPretty.xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (CCHTypesToPretty.exp_to_pretty e)


let _fenv = CCHFileEnvironment.file_environment


class locally_initialized_checker_t
        (poq: po_query_int)
        (vinfo: varinfo)
        (lval: lval)
        (invs: invariant_int list) =
object (self)

  method private vinfo = vinfo

  method private get_symbol_name (s: symbol_t) =
    s#getBaseName
    ^ (match s#getAttributes with
       | [] -> ""
       | l  -> "(" ^ (String.concat "" l) ^ ")")

  (* --------------------------- safe --------------------------------------- *)
  (* check_safe
     - check_safe_invs
       - inv_implies_safe
         - inv_xpr_implies_safe
     - check_safe_lval
       - check_safe_memlval
         - memlval_implies_safe
   *)

  method private memlval_memref_implies_safe
                   (invindex: int)
                   (memlval: lval)
                   (memref: memory_reference_int) =
    let mname = "memlval_memref_implies_safe" in
    match memref#get_base with
    | CStackAddress svar ->
       let (svinfo, _) = poq#env#get_local_variable svar in
       let deps = DLocal [invindex] in
       let msg =
         "pointer variable "
         ^ (p2s (lval_to_pretty memlval))
         ^ " points at stack variable "
         ^ svinfo.vname
         ^ " which is distinct from the memory pointed at by "
         ^ vinfo.vname in
       let site = Some (__FILE__, __LINE__, mname) in
       Some (deps, msg, site)
    | _ ->
       begin
         poq#set_diagnostic
           ~site:(Some (__FILE__, __LINE__, mname))
           ("[memref-base]: "
            ^ (p2s (memory_base_to_pretty memref#get_base)));
         None
       end

  method private memlval_implies_safe (memlval: lval) (inv: invariant_int) =
    let mname = "memlval_vinv_implies_safe" in
    match inv#expr with
    | Some (XVar v) when poq#env#is_memory_address v ->
       let (memref, _) = poq#env#get_memory_address v in
       self#memlval_memref_implies_safe inv#index memlval memref
    | _ ->
       begin
         poq#set_diagnostic
           ~site:(Some (__FILE__, __LINE__, mname))
           ("[inv]: " ^ (p2s inv#toPretty));
         None
       end

  method private check_safe_memlval (memlval: lval) (memoffset: offset) =
    let mname = "check_safe_memlval" in
    match (memlval, memoffset) with
    | ((Var (_vname, vid), NoOffset), _) ->
       let vinfo = poq#env#get_varinfo vid in
       let vinfovalues = poq#get_vinfo_offset_values vinfo in
       List.fold_left (fun acc (inv, offset) ->
           acc
           || (match offset with
               | NoOffset ->
                  (match self#memlval_implies_safe memlval inv with
                   | Some (deps, msg, site) ->
                      begin
                        poq#record_safe_result ~site deps msg;
                        true
                      end
                   | _ ->
                      false)
               | _ ->
                  begin
                    poq#set_diagnostic
                      ~site:(Some (__FILE__, __LINE__, mname))
                      ("[memlval, memoffset, vinfo, inv, offset]: "
                       ^ (p2s (lval_to_pretty memlval))
                       ^ ", "
                       ^ (p2s (offset_to_pretty memoffset))
                       ^ ", "
                       ^ vinfo.vname
                       ^ ", "
                       ^ (p2s inv#toPretty)
                       ^ ", "
                       ^ (p2s (offset_to_pretty offset)));
                    false
                  end)) false vinfovalues
    | _ -> false

  method private check_safe_lval =
    match lval with
    | (Mem (Lval memlval), memoffset) ->
       self#check_safe_memlval memlval memoffset
    | _ -> false

  method private inv_xpr_implies_safe (invindex: int) (x: xpr_t) =
    let mname = "xpr_implies_safe" in
    if poq#is_api_expression x then
      let _ =
        poq#set_diagnostic_arg
          ~site:(Some (__FILE__, __LINE__, mname))
          2
          ("api expression: " ^ (e2s (poq#get_api_expression x))) in
      match poq#get_api_expression x with
      | Lval (Mem (Lval (Var vpar, NoOffset)), NoOffset)
           when not ((fst vpar) = vinfo.vname) ->
         let deps = DLocal ([invindex]) in
         let msg =
           ("value of " ^ (p2s (lval_to_pretty lval))
            ^ " is not obtained from dereferencing parameter "
            ^ vinfo.vname
            ^ ", but from a different parameter: "
            ^ (fst vpar)) in
         let site = Some (__FILE__, __LINE__, mname) in
         Some (deps, msg, site)
      | api_e ->
         begin
           poq#set_diagnostic
             ~site:(Some (__FILE__, __LINE__, mname))
             ("[api_e]: " ^ (e2s api_e));
           None
         end
    else
      begin
        poq#set_diagnostic
          ~site:(Some (__FILE__, __LINE__, mname)) ("[xpr]: " ^ (x2s x));
        None
      end

  method private inv_implies_safe (inv: invariant_int) =
    let mname = "inv_implies_safe" in
    match inv#expr with
    | Some x -> self#inv_xpr_implies_safe inv#index x
    | _ ->
       match inv#get_fact with
       | NonRelationalFact (_, FInitializedSet l) ->
          let localAssigns =
            List.filter (fun s -> not (s#getBaseName = "parameter")) l in
          (match localAssigns with
           | [] -> None
           | _ ->
              let deps = DLocal [inv#index] in
              let msg =
                "local assignment(s): "
                ^ (String.concat
                     "_xx_" (List.map self#get_symbol_name localAssigns)) in
              let site = Some (__FILE__, __LINE__, mname) in
              Some (deps, msg, site))
       | _ ->
          begin
            poq#set_diagnostic
              ~site:(Some (__FILE__, __LINE__, mname))
              ("[inv]: " ^ (p2s inv#toPretty));
            None
          end

  method private check_safe_invs =
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
     - check_violation_invs
       - inv_implies_violation
         - xpr_implies_violation

     - check_violation_lval
       - check_violation_memlval
         - memlval_vinv_implies_violation
   *)

  method private xpr_implies_violation (invindex: int) (x: xpr_t) =
    let mname = "xpr_implies_violation" in
    if poq#is_api_expression x then
      let _ =
        poq#set_diagnostic_arg
          ~site:(Some (__FILE__, __LINE__, mname))
          2
          ("api expression: " ^ (e2s (poq#get_api_expression x))) in
      match poq#get_api_expression x with
      | Lval (Mem (Lval (Var vpar, NoOffset)), NoOffset)
           when (fst vpar) = vinfo.vname ->
         let deps = DLocal ([invindex]) in
         let msg =
           ("value of " ^ (p2s (lval_to_pretty lval))
            ^ " is obtained from dereferencing parameter "
            ^ (fst vpar)) in
         let site = Some (__FILE__, __LINE__, mname) in
         Some (deps, msg, site)
      | api_e ->
         begin
           poq#set_diagnostic
             ~site:(Some (__FILE__, __LINE__, mname))
             ("[api_e]: " ^ (e2s api_e));
           None
         end
    else
      begin
        poq#set_diagnostic
          ~site:(Some (__FILE__, __LINE__, mname)) ("[xpr]: " ^ (x2s x));
        None
      end

  method private inv_implies_violation (inv: invariant_int) =
    let mname = "inv_implies_violation" in
    match inv#expr with
    | Some x -> self#xpr_implies_violation inv#index x
    | _ ->
       begin
         poq#set_diagnostic
           ~site:(Some (__FILE__, __LINE__, mname))
           ("[inv]: " ^ (p2s inv#toPretty));
         None
       end

  method private memlval_vinv_implies_violation
                   (inv: invariant_int) (memoffset: offset) =
    let mname = "memlval_vinv_implies_violation" in
    match inv#expr with
    | Some x when poq#is_api_expression x ->
       begin
         match poq#get_api_expression x with
         | Lval lval ->
            if is_constant_offset memoffset then
              let memlval = (Mem (Lval lval), memoffset) in
              let deps = DLocal ([inv#index]) in
              let msg =
                "initialized from parameter "
                ^ (p2s (lval_to_pretty memlval))
                ^ " with offset "
                ^ (p2s (offset_to_pretty memoffset)) in
              let site = Some (__FILE__, __LINE__, mname) in
              Some (deps, msg, site)
            else
              begin
                poq#set_diagnostic
                  ~site:(Some (__FILE__, __LINE__, mname))
                  ("[api-lval, memoffset]: "
                   ^ (p2s (lval_to_pretty lval))
                   ^ ", "
                   ^ (p2s (offset_to_pretty memoffset)));
                None
              end
         | api_e ->
            begin
              poq#set_diagnostic
                ~site:(Some (__FILE__, __LINE__, mname))
                ("[api_e]: " ^ (e2s api_e));
              None
            end
       end
    | _ ->
       begin
         poq#set_diagnostic
           ~site:(Some (__FILE__, __LINE__, mname))
           ("[inv, memoffset]: "
            ^ (p2s inv#toPretty)
            ^ ", "
            ^ (p2s (offset_to_pretty memoffset)));
         None
       end

  method private check_violation_memlval (memlval: lval) (memoffset: offset) =
    match memlval with
    | (Var (vname, vid), NoOffset) when vid > 0 && vinfo.vname = vname ->
       let vinfovalues = poq#get_vinfo_offset_values vinfo in
       List.fold_left (fun acc (inv, offset) ->
           acc
           || match offset with
              | NoOffset ->
                 begin
                   match self#memlval_vinv_implies_violation
                           inv memoffset with
                   | Some (deps, msg, site) ->
                      begin
                        poq#record_violation_result ~site deps msg;
                        true
                      end
                   | _ -> false
                 end
              | _ -> false) false vinfovalues
    | _ -> false

  method private check_violation_lval =
    match lval with
    | (Mem (Lval memlval), memoffset) ->
       self#check_violation_memlval memlval memoffset
    | _ -> false

  method private check_violation_invs =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_violation inv with
             | Some (deps, msg, site) ->
                begin
                  poq#record_violation_result ~site deps msg;
                  true
                end
             | _ -> false) false invs

  method check_safe =
    self#check_safe_invs || self#check_safe_lval

  method check_violation =
    self#check_violation_invs || self#check_violation_lval

end


let check_locally_initialized (poq:po_query_int) (vinfo: varinfo) (lval:lval) =
  let f_priority (inv: invariant_int) =
    match inv#get_fact with
    | NonRelationalFact (_, FInitializedSet _) -> true
    | _ -> false in
  let invs =
    CCHInvariantFact.prioritize_invariants f_priority (poq#get_invariants 2) in
  let _ = poq#set_diagnostic_invariants 2 in
  let _ =
    poq#set_init_vinfo_mem_diagnostic_invariants
      ~site:(Some (__FILE__, __LINE__, "check_locally_initialized"))
      vinfo
      (snd lval) in
  let _ =
    if (List.length invs) = 0 then
      poq#set_diagnostic
        ~site:(Some (__FILE__, __LINE__, "check_locally_initialized"))
        ("no invariants available at this location for lval "
         ^ (p2s (lval_to_pretty lval))) in
  let checker = new locally_initialized_checker_t poq vinfo lval invs in
  checker#check_safe || checker#check_violation

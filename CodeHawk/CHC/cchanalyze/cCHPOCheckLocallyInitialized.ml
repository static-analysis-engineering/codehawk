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
open CCHPreTypes

(* cchanalyze *)
open CCHAnalysisTypes


let x2p = XprToPretty.xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let _x2s x = p2s (x2p x)
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

  method private xpr_implies_safe (invindex: int) (x: xpr_t) =
    if poq#is_api_expression x then
      let _ =
        poq#set_diagnostic_arg
          2 ("api expression: " ^ (e2s (poq#get_api_expression x))) in
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
         Some (deps, msg)
      | _ -> None
    else
      None

  method private inv_implies_safe (inv: invariant_int) =
    match inv#expr with
    | Some x -> self#xpr_implies_safe inv#index x
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
              Some (deps, msg))
       | _ -> None

  method private check_invs_safe =
    match invs with
    | [] -> false
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

  method private xpr_implies_violation (invindex: int) (x: xpr_t) =
    if poq#is_api_expression x then
      let _ =
        poq#set_diagnostic_arg
          2 ("api expression: " ^ (e2s (poq#get_api_expression x))) in
      match poq#get_api_expression x with
      | Lval (Mem (Lval (Var vpar, NoOffset)), NoOffset)
           when (fst vpar) = vinfo.vname ->
         let deps = DLocal ([invindex]) in
         let msg =
           ("value of " ^ (p2s (lval_to_pretty lval))
            ^ " is obtained from dereferencing parameter "
            ^ (fst vpar)) in
         Some (deps, msg)

      | _ -> None
    else
      None

  method private inv_implies_violation (inv: invariant_int) =
    match inv#expr with
    | Some x -> self#xpr_implies_violation inv#index x
    | _ -> None

  method private vinv_implies_deref_offset_violation
                   (inv: invariant_int) (memoffset: offset) =
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
              Some (deps, msg)
            else
              None
         | _ ->
            None
       end
    | _ -> None

  method private check_lval_deref_violation (memlval: lval) (memoffset: offset) =
    match memlval with
    | (Var (vname, vid), NoOffset) when vid > 0 && vinfo.vname = vname ->
       let vinfovalues = poq#get_vinfo_offset_values vinfo in
       List.fold_left (fun acc (inv, offset) ->
           acc
           || match offset with
              | NoOffset ->
                 begin
                   match self#vinv_implies_deref_offset_violation
                           inv memoffset with
                   | Some (deps, msg) ->
                      begin
                        poq#record_violation_result deps msg;
                        true
                      end
                   | _ -> false
                 end
              | _ -> false) false vinfovalues
    | _ -> false

  method private check_lval_violation =
    match lval with
    | (Mem (Lval memlval), memoffset) ->
       self#check_lval_deref_violation memlval memoffset
    | _ -> false

  method private check_invs_violation =
    match invs with
    | [] -> false
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_violation inv with
             | Some (deps, msg) ->
                begin
                  poq#record_violation_result deps msg;
                  true
                end
             | _ -> false) false invs

  method check_safe =
    self#check_invs_safe

  method check_violation =
    self#check_invs_violation || self#check_lval_violation

end


let check_locally_initialized (poq:po_query_int) (vinfo: varinfo) (lval:lval) =
  let invs = poq#get_invariants 2 in
  let _ = poq#set_diagnostic_invariants 2 in
  let _ = poq#set_init_vinfo_mem_diagnostic_invariants vinfo (snd lval) in
  let checker = new locally_initialized_checker_t poq vinfo lval invs in
  checker#check_safe || checker#check_violation

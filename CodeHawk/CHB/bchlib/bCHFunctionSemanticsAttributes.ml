(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026  Aarno Labs LLC

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

(* Output path: function semantics → attributes (for delegated preconditions,
   side effects, postconditions, error-postconditions, and qualifiers in
   generated header files).

   Emitted forms:
   - chk_pre  : delegated proof obligations (preconditions)
   - chk_se   : side effects (block-write, freed, modifies, invalidates)
   - chk_post : postconditions on the return value or a parameter
   - chk_epost: error-path postconditions
   - chk_qual : CodeHawk-specific qualifiers (sets_errno)
   - noreturn, pure, const, warn_unused_result: standard GCC qualifiers

   GCC compatibility forms (access, nonnull, format) are accepted on input
   but never generated here.

   See bCHAttributesFunctionSemantics.ml for the input path. *)

(* chutil *)
open CHLogger
open CHTraceResult

(* bchlib *)
open BCHBCTypePretty
open BCHBCTypes
open BCHBTerm
open BCHLibTypes

module TR = CHTraceResult

let (let*) x f = CHTraceResult.tbind f x

let p2s = CHPrettyUtil.pretty_to_string

let eloc (line: int): string = __FILE__ ^ ":" ^ (string_of_int line)
let elocm (line: int): string = (eloc line) ^ ": "


let bterm_to_numerical_constant (t: bterm_t): int option =
  match t with
  | NumConstant n -> Some n#toInt
  | _ -> None


let bterm_par_to_argument_index (p: bterm_t): int traceresult =
  match p with
  | ArgValue par ->
     (match par.apar_index with
      | Some index -> Ok index
      | _ ->
         Error [(elocm __LINE__)
                ^ "Unable to convert parameter "
                ^ (BCHFtsParameter.fts_parameter_to_string par)
                ^ " to an index"])
  | _ ->
     Error [(elocm __LINE__) ^ "Unexpected bterm: " ^ (BCHBTerm.bterm_to_string p)]


let is_same_bterm_par (t1: bterm_t) (t2: bterm_t): bool =
  TR.tfold
    ~ok:(fun index1 ->
      TR.tfold
        ~ok:(fun index2 -> index1 = index2)
        ~error:(fun _ -> false)
        (bterm_par_to_argument_index t2))
    ~error:(fun _ -> false)
    (bterm_par_to_argument_index t1)


let chk_pre_attribute (params: b_attrparam_t list): b_attribute_t =
  Attr ("chk_pre", params)


let convert_buffer
      (loc: location_int)
      (ty: btype_t)
      (pbuffer: bterm_t)
      (psize: bterm_t): b_attributes_t =
  match psize with
  | ArgNullTerminatorPos ntposarg ->
     if is_same_bterm_par pbuffer ntposarg then
       TR.tfold
         ~ok:(fun argindex ->
           [chk_pre_attribute
              [ACons ("deref_read", [ACons ("ntp", [])]); AInt argindex]])
         ~error:(fun _ -> [])
         (bterm_par_to_argument_index pbuffer)
     else
       begin
         log_diagnostics_result
           ~tag:"convert_buffer:unexpected ntposarg"
           ~msg:(p2s loc#toPretty)
           __FILE__ __LINE__
           ["pbuffer: " ^ (bterm_to_string pbuffer);
            "psize: " ^ (bterm_to_string psize)];
         []
       end
  | _ ->
     begin
       log_diagnostics_result
         ~tag:"convert_buffer:not yet implemented"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["type: " ^ (btype_to_string ty);
          "pbuffer: " ^ (bterm_to_string pbuffer);
          "psize: " ^ (bterm_to_string psize)];
       []
     end               
  

let convert_initialized_range
      (loc: location_int)
      (ty: btype_t)
      (pbuffer: bterm_t)
      (psize: bterm_t): b_attributes_t =
  match psize with
  | ArgNullTerminatorPos ntposarg ->
     if is_same_bterm_par pbuffer ntposarg then
       TR.tfold
         ~ok:(fun argindex ->
           [chk_pre_attribute
              [ACons ("initialized_range", [ACons ("ntp", [])]); AInt argindex]])
         ~error:(fun _ -> [])
         (bterm_par_to_argument_index pbuffer)
     else
       begin
         log_diagnostics_result
           ~tag:"convert_initialized_range:unexpected ntposarg"
           ~msg:(p2s loc#toPretty)
           __FILE__ __LINE__
           ["pbuffer: " ^ (bterm_to_string pbuffer);
            "psize: " ^ (bterm_to_string psize)];
         []
       end
  | _ ->
     begin
       log_diagnostics_result
         ~tag:"convert_initialized_range:not yet implemented"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["type: " ^ (btype_to_string ty);
          "pbuffer: " ^ (bterm_to_string pbuffer);
          "psize: " ^ (bterm_to_string psize)];
       []
     end               
  

let convert_not_null (loc: location_int) (p: bterm_t): b_attributes_t =
  TR.tfold
    ~ok:(fun argindex ->
      [Attr ("chk_pre", [ACons ("not_null", []); AInt argindex])])
    ~error:(fun e ->
      begin
        log_error_result
          ~tag:"convert_not_null"
          ~msg:(p2s loc#toPretty)
          __FILE__ __LINE__
          [String.concat ", " e];
        []
      end)
    (bterm_par_to_argument_index p)


let convert_null_terminated
      (loc: location_int) (p: bterm_t): b_attributes_t =
  TR.tfold
    ~ok:(fun argindex ->
      [Attr ("chk_pre", [ACons ("null_terminated", []); AInt argindex])])
    ~error:(fun e ->
      begin
        log_error_result
          ~tag:"convert_null_terminated"
          ~msg:(p2s loc#toPretty)
          __FILE__ __LINE__
          [String.concat ", " e];
        []
      end)
    (bterm_par_to_argument_index p)


let convert_output_format_string (loc: location_int) (p: bterm_t): b_attributes_t =
  TR.tfold
    ~ok:(fun argindex ->
      [Attr ("chk_pre", [ACons ("output_format_string", []); AInt argindex])])
    ~error:(fun e ->
      begin
        log_error_result
          ~tag:"convert_output_format_string"
          ~msg:(p2s loc#toPretty)
          __FILE__ __LINE__
          [String.concat ", " e];
        []
      end)
    (bterm_par_to_argument_index p)


let convert_trusted_os_cmd_fmt_string
      (loc: location_int)
      (p: bterm_t)
      (kind: format_args_kind_t)
      (optlen: bterm_t option): b_attributes_t =
  let kindparam =
    AStr (BCHExternalPredicate.format_args_kind_to_string kind) in
  let lenarg =
    match optlen with
    | Some t ->
       (match bterm_to_numerical_constant t with
        | None ->
           begin
             log_diagnostics_result
               ~tag:"convert_trusted_cmd_fmt_string:non_constant length"
               ~msg:(p2s loc#toPretty)
               __FILE__ __LINE__
               ["len: " ^ (bterm_to_string t)];
             None
           end
        | Some numlen -> Some numlen)
    | _ -> None in
  TR.tfold
    ~ok:(fun argindex ->
      let tagparams =
        match lenarg with Some len -> [kindparam; AInt len] | _ -> [kindparam] in
      [chk_pre_attribute
         [ACons ("trusted_os_cmd_fmt_string", tagparams); AInt argindex]])
    ~error:(fun e ->
      begin
        log_error_result
          ~tag:"converted_trusted_os_cmd_fmt_string"
          ~msg:(p2s loc#toPretty)
          __FILE__ __LINE__
          [String.concat ", " e];
        []
      end)
    (bterm_par_to_argument_index p)         


let convert_preconditions_to_attributes
      (_finfo: function_info_int)
      (preconditions: proofobligation_int list): b_attributes_t =
  List.fold_left (fun acc po ->
      match po#status with
      | Delegated xpred ->
         (match xpred with
          | XXBuffer (ty, pb, ps) ->
             (convert_buffer po#loc ty pb ps) @ acc
          | XXInitializedRange (ty, pb, ps) ->
             (convert_initialized_range po#loc ty pb ps) @ acc
          | XXNotNull p ->
             (convert_not_null po#loc p) @ acc
          | XXNullTerminated p ->
             (convert_null_terminated po#loc p) @ acc
          | XXOutputFormatString p ->
             (convert_output_format_string po#loc p) @ acc
          | XXTrustedOsCmdFmtString (p, kind, optlen) ->
             (convert_trusted_os_cmd_fmt_string po#loc p kind optlen) @ acc
          | _ -> acc)
      | _ -> acc) [] preconditions      


let convert_xxpredicate_to_post_attrparams
      (ctx: string)
      (xpred: xxpredicate_t): b_attrparam_t list option =
  let target_params target =
    match target with
    | ReturnValue _ -> Some []
    | ArgValue par ->
       (match par.apar_index with
        | Some index -> Some [AInt index]
        | None ->
           begin
             log_diagnostics_result
               ~tag:"convert_xxpredicate_to_post_attrparams:no index"
               ~msg:ctx
               __FILE__ __LINE__
               ["par: " ^ (bterm_to_string (ArgValue par))];
             None
           end)
    | _ ->
       begin
         log_diagnostics_result
           ~tag:"convert_xxpredicate_to_post_attrparams:unexpected target"
           ~msg:ctx
           __FILE__ __LINE__
           ["target: " ^ (bterm_to_string target)];
         None
       end in
  let make pred target =
    match target_params target with
    | None -> None
    | Some argparams -> Some (ACons (pred, []) :: argparams) in
  let zero = CHNumerical.numerical_zero in
  let negone = CHNumerical.mkNumerical (-1) in
  match xpred with
  | XXNotNull target         -> make "not_null" target
  | XXNull target            -> make "null" target
  | XXNonNegative target     -> make "non_negative" target
  | XXNotZero target         -> make "not_zero" target
  | XXPositive target        -> make "positive" target
  | XXNullTerminated target  -> make "null_terminated" target
  | XXNewMemory (target, RunTimeValue) -> make "new_memory" target
  | XXAllocationBase target  -> make "allocation_base" target
  | XXTrustedString target   -> make "trusted_string" target
  | XXTrustedOsCmdString target -> make "trusted_os_cmd_string" target
  | XXTainted target         -> make "tainted" target
  | XXRelationalExpr (PEquals, target, NumConstant n) when n#equal negone ->
     make "negone" target
  | XXRelationalExpr (PEquals, target, NumConstant n) when n#equal zero ->
     make "zero" target
  | XXRelationalExpr (PLessThan, target, NumConstant n) when n#equal zero ->
     make "negative" target
  | XXRelationalExpr (PLessEqual, target, NumConstant n) when n#equal zero ->
     make "nonpositive" target
  | _ ->
     begin
       log_diagnostics_result
         ~tag:"convert_xxpredicate_to_post_attrparams:not representable"
         ~msg:ctx
         __FILE__ __LINE__
         ["pred: " ^ (p2s (BCHExternalPredicate.xxpredicate_to_pretty xpred))];
       None
     end


let convert_postconditions_to_attributes
      (ctx: string)
      (attrname: string)
      (postconditions: xxpredicate_t list): b_attributes_t =
  List.filter_map (fun xpred ->
      match convert_xxpredicate_to_post_attrparams ctx xpred with
      | None -> None
      | Some params -> Some (Attr (attrname, params))) postconditions


let convert_sideeffect_to_attribute
      (ctx: string)
      (xpred: xxpredicate_t): b_attribute_t option =
  let par_index par =
    match par.apar_index with
    | Some index -> Ok index
    | None ->
       Error [(elocm __LINE__)
              ^ "parameter has no index: "
              ^ par.apar_name] in
  match xpred with
  | XXBlockWrite (_, ArgValue par, RunTimeValue) ->
     TR.tfold
       ~ok:(fun index ->
         Some (Attr ("chk_se", [ACons ("deref_write", []); AInt index])))
       ~error:(fun e ->
         begin
           log_diagnostics_result
             ~tag:"convert_sideeffect_to_attribute:deref_write"
             ~msg:ctx __FILE__ __LINE__ e;
           None
         end)
       (par_index par)

  | XXBlockWrite (_, ArgValue par, ArgValue sizepar) ->
     TR.tfold
       ~ok:(fun (index, sizeindex) ->
         Some (Attr ("chk_se",
                     [ACons ("deref_write", []); AInt index; AInt sizeindex])))
       ~error:(fun e ->
         begin
           log_diagnostics_result
             ~tag:"convert_sideeffect_to_attribute:deref_write(sized)"
             ~msg:ctx __FILE__ __LINE__ e;
           None
         end)
       (let* i = par_index par in
        let* s = par_index sizepar in
        Ok (i, s))

  | XXBlockWrite (_, ArgValue par, NumConstant n) ->
     TR.tfold
       ~ok:(fun index ->
         Some (Attr ("chk_se",
                     [ACons ("deref_write", [AInt n#toInt]); AInt index])))
       ~error:(fun e ->
         begin
           log_diagnostics_result
             ~tag:"convert_sideeffect_to_attribute:deref_write(const)"
             ~msg:ctx __FILE__ __LINE__ e;
           None
         end)
       (par_index par)

  | XXFreed (ArgValue par) ->
     TR.tfold
       ~ok:(fun index ->
         Some (Attr ("chk_se", [ACons ("freed", []); AInt index])))
       ~error:(fun e ->
         begin
           log_diagnostics_result
             ~tag:"convert_sideeffect_to_attribute:freed"
             ~msg:ctx __FILE__ __LINE__ e;
           None
         end)
       (par_index par)

  | XXModified (ArgValue par) ->
     TR.tfold
       ~ok:(fun index ->
         Some (Attr ("chk_se", [ACons ("modifies", []); AInt index])))
       ~error:(fun e ->
         begin
           log_diagnostics_result
             ~tag:"convert_sideeffect_to_attribute:modifies"
             ~msg:ctx __FILE__ __LINE__ e;
           None
         end)
       (par_index par)

  | XXInvalidated (ArgValue par) ->
     TR.tfold
       ~ok:(fun index ->
         Some (Attr ("chk_se", [ACons ("invalidates", []); AInt index])))
       ~error:(fun e ->
         begin
           log_diagnostics_result
             ~tag:"convert_sideeffect_to_attribute:invalidates"
             ~msg:ctx __FILE__ __LINE__ e;
           None
         end)
       (par_index par)

  | XXConditional (XXNotNull (ArgValue par),
                   XXBlockWrite (_, ArgValue par', RunTimeValue))
       when is_same_bterm_par (ArgValue par) (ArgValue par') ->
     TR.tfold
       ~ok:(fun index ->
         Some (Attr ("chk_se", [ACons ("deref_write_null", []); AInt index])))
       ~error:(fun e ->
         begin
           log_diagnostics_result
             ~tag:"convert_sideeffect_to_attribute:deref_write_null"
             ~msg:ctx __FILE__ __LINE__ e;
           None
         end)
       (par_index par)

  | XXConditional (XXNotNull (ArgValue par),
                   XXBlockWrite (_, ArgValue par', ArgValue sizepar))
       when is_same_bterm_par (ArgValue par) (ArgValue par') ->
     TR.tfold
       ~ok:(fun (index, sizeindex) ->
         Some (Attr ("chk_se",
                     [ACons ("deref_write_null", []); AInt index; AInt sizeindex])))
       ~error:(fun e ->
         begin
           log_diagnostics_result
             ~tag:"convert_sideeffect_to_attribute:deref_write_null(sized)"
             ~msg:ctx __FILE__ __LINE__ e;
           None
         end)
       (let* i = par_index par in
        let* s = par_index sizepar in
        Ok (i, s))

  | _ ->
     begin
       log_diagnostics_result
         ~tag:"convert_sideeffect_to_attribute:not representable"
         ~msg:ctx
         __FILE__ __LINE__
         ["pred: " ^ (p2s (BCHExternalPredicate.xxpredicate_to_pretty xpred))];
       None
     end


let convert_sideeffects_to_attributes
      (ctx: string)
      (sideeffects: xxpredicate_t list): b_attributes_t =
  List.filter_map (convert_sideeffect_to_attribute ctx) sideeffects


let convert_qualifiers_to_attributes
      (qualifiers: function_qualifiers_t): b_attributes_t =
  let attrs = [] in
  let attrs =
    match qualifiers.fq_noreturn with
    | Some true -> Attr ("noreturn", []) :: attrs
    | _ -> attrs in
  let attrs =
    match qualifiers.fq_functional with
    | Some FPure  -> Attr ("pure", []) :: attrs
    | Some FConst -> Attr ("const", []) :: attrs
    | _ -> attrs in
  let attrs =
    match qualifiers.fq_sets_errno with
    | Some true ->
       Attr ("chk_qual", [ACons ("sets_errno", [])]) :: attrs
    | _ -> attrs in
  let attrs =
    match qualifiers.fq_must_use_return with
    | Some true -> Attr ("warn_unused_result", []) :: attrs
    | _ -> attrs in
  attrs


let convert_semantics_to_attributes (finfo: function_info_int): b_attributes_t =
  let ctx = finfo#get_name in
  let delegatedpos = finfo#proofobligations#delegated_proofobligations in
  let sem = finfo#get_summary#get_function_semantics in
  let preattrs = convert_preconditions_to_attributes finfo delegatedpos in
  let seattrs = convert_sideeffects_to_attributes ctx sem.fsem_sideeffects in
  let postattrs =
    convert_postconditions_to_attributes ctx "chk_post" sem.fsem_post in
  let epostattrs =
    convert_postconditions_to_attributes ctx "chk_epost" sem.fsem_errorpost in
  let qualattrs = convert_qualifiers_to_attributes sem.fsem_qualifiers in
  preattrs @ seattrs @ postattrs @ epostattrs @ qualattrs


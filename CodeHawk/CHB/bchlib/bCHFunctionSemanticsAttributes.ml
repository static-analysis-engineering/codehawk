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
   side effects, postconditions in generated header files).

   Only canonical CodeHawk forms (chk_pre, chk_se, chk_post) are emitted.
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


let convert_semantics_to_attributes (finfo: function_info_int): b_attributes_t =
  let delegatedpos = finfo#proofobligations#delegated_proofobligations in
  let preattrs = convert_preconditions_to_attributes finfo delegatedpos in
  preattrs
  

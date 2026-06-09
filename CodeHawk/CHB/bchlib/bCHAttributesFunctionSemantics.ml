(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024-2026  Aarno Labs LLC

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

(* Input path: attributes → function semantics (preconditions, side effects,
   postconditions).

   Accepted attribute forms:
   - GCC compatibility (read-only; never emitted on output):
       access, nonnull, format
   - Canonical CodeHawk forms (input and output):
       chk_pre, chk_se, chk_post

   See bCHFunctionSemanticsAttributes.ml for the output path. *)

(* chutil *)
open CHLogger
open CHTraceResult

(* bchlib *)
open BCHBCTypes
open BCHBCTypePretty
open BCHBCTypeUtil
open BCHFtsParameter
open BCHFunctionInterface
open BCHLibTypes

module TR = CHTraceResult


let (let*) x f = CHTraceResult.tbind f x

let eloc (line: int): string = __FILE__ ^ ":" ^ (string_of_int line)
let elocm (line: int): string = (eloc line) ^ ": "


let get_par
      (fparameters: fts_parameter_t list)
      (index: int): fts_parameter_t traceresult =
  try
    Ok (List.find (fun p ->
            match p.apar_index with Some ix -> ix = index | _ -> false)
          fparameters)
  with
  | Not_found ->
     Error [(elocm __LINE__)
            ^ "Unable to find parameter with index: "
            ^ (string_of_int index);
            "parameters: "
            ^ (String.concat ", " (List.map (fun p -> p.apar_name) fparameters))]


let get_derefty (par: fts_parameter_t): btype_t traceresult =
  if is_pointer par.apar_type then
    Ok (ptr_deref par.apar_type)
  else
    Error [(elocm __LINE__)
           ^ "Expected a pointer but found " ^ (btype_to_string par.apar_type)]


let fparams_to_string (fparams: fts_parameter_t list): string =
  "fparams: " ^ (String.concat ", " (List.map fts_parameter_to_string fparams))


let attrparams_to_string (tag: string) (attrparams: b_attrparam_t list): string =
  tag ^ ": " ^ (String.concat ", " (List.map b_attrparam_to_string attrparams))


let get_deref_read_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     let* ty = get_derefty par in
     Ok (XXBuffer (ty, ArgValue par, RunTimeValue))

  | ([], [AInt refindex; AInt sizeindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* sizeparam = get_par fparams sizeindex in
     let* ty = get_derefty bufferparam in
     Ok (XXBuffer (ty, ArgValue bufferparam, ArgValue sizeparam))

  | ([AInt size], [AInt refindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* ty = get_derefty bufferparam in
     let sizeparam = CHNumerical.mkNumerical size in
     Ok (XXBuffer (ty, ArgValue bufferparam, NumConstant sizeparam))

  | ([ACons ("ntp", [])], [AInt refindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* ty = get_derefty bufferparam in
     let bparam = ArgValue bufferparam in
     Ok (XXBuffer (ty, bparam, ArgNullTerminatorPos bparam))

  | _ ->
     Error [(elocm __LINE__) ^ "deref_read params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_deref_write_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     let* ty = get_derefty par in
     Ok (XXBlockWrite (ty, ArgValue par, RunTimeValue))

  | ([], [AInt refindex; AInt sizeindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* sizeparam = get_par fparams sizeindex in
     let* ty = get_derefty bufferparam in
     Ok (XXBlockWrite (ty, ArgValue bufferparam, ArgValue sizeparam))

  | ([AInt size], [AInt refindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* ty = get_derefty bufferparam in
     let sizeparam = CHNumerical.mkNumerical size in
     Ok (XXBlockWrite (ty, ArgValue bufferparam, NumConstant sizeparam))

  | _ ->
     Error [(elocm __LINE__) ^ "deref_write params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_initialized_range_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([ACons ("ntp", [])], [AInt refindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* ty = get_derefty bufferparam in
     let bparam = ArgValue bufferparam in
     Ok (XXInitializedRange(ty, bparam, ArgNullTerminatorPos bparam))

  | _ ->
     Error [(elocm __LINE__) ^ "initialized_range params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_deref_read_write_preconditions
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t list traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     let* ty = get_derefty par in
     Ok [XXBuffer (ty, ArgValue par, RunTimeValue);
         XXBlockWrite (ty, ArgValue par, RunTimeValue)]

  | ([], [AInt refindex; AInt sizeindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* sizeparam = get_par fparams sizeindex in
     let* ty = get_derefty bufferparam in
     Ok [XXBuffer (ty, ArgValue bufferparam, ArgValue sizeparam);
         XXBlockWrite (ty, ArgValue bufferparam, ArgValue sizeparam)]

  | ([AInt size], [AInt refindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* ty = get_derefty bufferparam in
     let sizeparam = CHNumerical.mkNumerical size in
     Ok [XXBuffer (ty, ArgValue bufferparam, NumConstant sizeparam);
         XXBlockWrite (ty, ArgValue bufferparam, NumConstant sizeparam)]

  | ([ACons ("ntp", [])], [AInt refindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* ty = get_derefty bufferparam in
     let bparam = ArgValue bufferparam in
     Ok [XXBuffer (ty, bparam, ArgNullTerminatorPos bparam);
         XXBlockWrite (ty, bparam, RunTimeValue)]

  | _ ->
     Error [(elocm __LINE__) ^ "deref_read write_params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_not_null_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXNotNull (ArgValue par))

  | _ ->
     Error [(elocm __LINE__) ^ "not_null params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_nonnull_preconditions
      (fparams: fts_parameter_t list)
      (attrparams: b_attrparam_t list): xxpredicate_t list =
  match attrparams with
  | [] ->
     (* bare nonnull: all pointer parameters must be non-null *)
     List.filter_map (fun par ->
         if is_pointer par.apar_type then
           Some (XXNotNull (ArgValue par))
         else
           None) fparams
  | _ ->
     (* indexed nonnull: listed parameters must be non-null *)
     List.filter_map (fun attrparam ->
         match attrparam with
         | AInt index ->
            TR.tfold
              ~ok:(fun par -> Some (XXNotNull (ArgValue par)))
              ~error:(fun _ -> None)
              (get_par fparams index)
         | _ -> None) attrparams


let get_format_preconditions
      (name: string)
      (fparams: fts_parameter_t list)
      (attrparams: b_attrparam_t list): xxpredicate_t list =
  match attrparams with
  | ACons (archetype, []) :: AInt string_index :: _ ->
     let mk_pre constructor =
       TR.tfold
         ~ok:(fun par -> [constructor (ArgValue par)])
         ~error:(fun _ -> [])
         (get_par fparams string_index) in
     (match archetype with
      | "printf" | "gnu_printf" -> mk_pre (fun t -> XXOutputFormatString t)
      | "scanf" | "gnu_scanf" -> mk_pre (fun t -> XXInputFormatString t)
      | _ ->
         begin
           log_diagnostics_result
             ~tag:"get_format_preconditions:archetype not handled"
             ~msg:name
             __FILE__ __LINE__
             ["archetype: " ^ archetype];
           []
         end)
  | _ ->
     begin
       log_diagnostics_result
         ~tag:"get_format_preconditions:params not recognized"
         ~msg:name
         __FILE__ __LINE__
         [attrparams_to_string "attrparams" attrparams];
       []
     end


let get_null_terminated_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXNullTerminated (ArgValue par))

  | _ ->
     Error [(elocm __LINE__) ^ "null_terminated params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_output_format_string_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXOutputFormatString (ArgValue par))

  | _ ->
     Error [(elocm __LINE__) ^ "output_format_string params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_trusted_os_cmd_fmt_string_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([AStr kind; AInt size], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     let* kind = BCHExternalPredicate.string_to_format_args_kind kind in
     let xsize = NumConstant (CHNumerical.mkNumerical size) in
     Ok (XXTrustedOsCmdFmtString (ArgValue par, kind, Some xsize))

  | _ ->
     Error [(elocm __LINE__) ^ "trusted_os_cmd_fmt_string params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let string_to_relational_op (s: string): relational_op_t traceresult =
  match s with
  | "eq"  -> Ok PEquals
  | "lt"  -> Ok PLessThan
  | "leq" -> Ok PLessEqual
  | "gt"  -> Ok PGreaterThan
  | "geq" -> Ok PGreaterEqual
  | "neq" -> Ok PNotEqual
  | _ -> Error [(elocm __LINE__) ^ "Unknown relational operator: " ^ s]


let get_input_format_string_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXInputFormatString (ArgValue par))
  | _ ->
     Error [(elocm __LINE__) ^ "input_format_string params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_not_zero_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXNotZero (ArgValue par))
  | _ ->
     Error [(elocm __LINE__) ^ "not_zero params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_non_negative_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXNonNegative (ArgValue par))
  | _ ->
     Error [(elocm __LINE__) ^ "non_negative params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_relational_expr_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([ACons (opstr, [])], [AInt index1; AInt index2]) ->
     let* op = string_to_relational_op opstr in
     let* par1 = get_par fparams index1 in
     let* par2 = get_par fparams index2 in
     Ok (XXRelationalExpr (op, ArgValue par1, ArgValue par2))
  | _ ->
     Error [(elocm __LINE__) ^ "relational_expr params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_no_overlap_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt index1; AInt index2]) ->
     let* par1 = get_par fparams index1 in
     let* par2 = get_par fparams index2 in
     Ok (XXNoOverlap (ArgValue par1, ArgValue par2))
  | _ ->
     Error [(elocm __LINE__) ^ "no_overlap params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_allocation_base_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXAllocationBase (ArgValue par))
  | _ ->
     Error [(elocm __LINE__) ^ "allocation_base params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_trusted_string_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXTrustedString (ArgValue par))
  | _ ->
     Error [(elocm __LINE__) ^ "trusted_string params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_trusted_os_cmd_string_precondition
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     Ok (XXTrustedOsCmdString (ArgValue par))
  | _ ->
     Error [(elocm __LINE__) ^ "trusted_os_cmd_string params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_chk_pre_conditions
      (name: string)
      (fparams: fts_parameter_t list)
      (attrparams: b_attrparam_t list): xxpredicate_t list =
  match attrparams with
  | (ACons ("deref_read", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_pre_conditions:deref_read"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_deref_read_precondition fparams tagparams argparams)

  | (ACons ("deref_write", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_pre_conditions:deref_write"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_deref_write_precondition fparams tagparams argparams)

  | (ACons ("initialized_range", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:initialized_range"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_initialized_range_precondition fparams tagparams argparams)

  | (ACons ("not_null", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:not_null"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_not_null_precondition fparams tagparams argparams)

  | (ACons ("null_terminated", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:null_terminated"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_null_terminated_precondition fparams tagparams argparams)

  | (ACons ("output_format_string", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:output_format_string"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_output_format_string_precondition fparams tagparams argparams)

  | (ACons ("trusted_os_cmd_fmt_string", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:trusted_os_cmd_fmt_string"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_trusted_os_cmd_fmt_string_precondition fparams tagparams argparams)

  | (ACons ("input_format_string", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:input_format_string"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_input_format_string_precondition fparams tagparams argparams)

  | (ACons ("not_zero", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:not_zero"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_not_zero_precondition fparams tagparams argparams)

  | (ACons ("non_negative", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:non_negative"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_non_negative_precondition fparams tagparams argparams)

  | (ACons ("relational_expr", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:relational_expr"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_relational_expr_precondition fparams tagparams argparams)

  | (ACons ("no_overlap", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:no_overlap"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_no_overlap_precondition fparams tagparams argparams)

  | (ACons ("allocation_base", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:allocation_base"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_allocation_base_precondition fparams tagparams argparams)

  | (ACons ("trusted_string", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:trusted_string"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_trusted_string_precondition fparams tagparams argparams)

  | (ACons ("trusted_os_cmd_string", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_chk_preconditions:trusted_os_cmd_string"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_trusted_os_cmd_string_precondition fparams tagparams argparams)

  | (ACons (tag, _)) :: _ ->
     begin
       log_diagnostics_result
         ~tag:"get_chk_pre_conditions:tag not recognized"
         ~msg:name
         __FILE__ __LINE__
         ["tag: " ^ tag];
       []
     end

  | _ ->
     begin
       log_diagnostics_result
         ~tag:"get_chk_pre_conditions:not recognized"
         ~msg:name
         __FILE__ __LINE__
         [fparams_to_string fparams; attrparams_to_string "attrparams" attrparams];
       []
     end


let get_access_preconditions
      (name: string)
      (fparams: fts_parameter_t list)
      (attrparams: b_attrparam_t list): xxpredicate_t list =
  match attrparams with
  | (ACons ("read_only", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_access_preconditions:read_only"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_deref_read_precondition fparams tagparams argparams)

  | (ACons ("write_only", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_access_preconditions:write_only"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_deref_write_precondition fparams tagparams argparams)

  | (ACons ("read_write", tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> xpre)
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_access_preconditions:read_write"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_deref_read_write_preconditions fparams tagparams argparams)

  | (ACons (tag, _)) :: _ ->
     begin
       log_diagnostics_result
         ~tag:"get_access_preconditions:tag not recognized"
         ~msg:name
         __FILE__ __LINE__
         ["tag: " ^ tag];
       []
     end

  | _ ->
     begin
       log_diagnostics_result
         ~tag:"get_access_preconditions:not yet implemented"
         ~msg:name
         __FILE__ __LINE__
         [fparams_to_string fparams; attrparams_to_string "params" attrparams];
       []
     end


let get_deref_write_sideeffect
      (fparams: fts_parameter_t list)
      (tagparams: b_attrparam_t list)
      (argparams: b_attrparam_t list): xxpredicate_t traceresult =
  match (tagparams, argparams) with
  | ([], [AInt refindex]) ->
     let* par = get_par fparams refindex in
     let* ty = get_derefty par in
     Ok (XXBlockWrite (ty, ArgValue par, RunTimeValue))

  | ([], [AInt refindex; AInt sizeindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* sizeparam = get_par fparams sizeindex in
     let* ty = get_derefty bufferparam in
     Ok (XXBlockWrite (ty, ArgValue bufferparam, ArgValue sizeparam))

  | ([AInt size], [AInt refindex]) ->
     let* bufferparam = get_par fparams refindex in
     let* ty = get_derefty bufferparam in
     let sizeparam = CHNumerical.mkNumerical size in
     Ok (XXBlockWrite (ty, ArgValue bufferparam, NumConstant sizeparam))

  | _ ->
     Error [(elocm __LINE__) ^ "deref_write_sideeffect params not recognized";
            fparams_to_string fparams;
            attrparams_to_string "tagparams" tagparams;
            attrparams_to_string "argparams" argparams]


let get_access_sideeffect
      (name: string)
      (fparams: fts_parameter_t list)
      (attrparams: b_attrparam_t list): xxpredicate_t list =
  match attrparams with
  | (ACons ("read_only", _)) :: _ -> []

  | (ACons (("write_only" | "read_write"), tagparams)) :: argparams ->
     TR.tfold
       ~ok:(fun xpre -> [xpre])
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"get_access_sideeffect:write_only_read_write"
             ~msg:name
             __FILE__ __LINE__
             [String.concat ", " e];
           []
         end)
       (get_deref_write_sideeffect fparams tagparams argparams)

  | (ACons (tag, _)) :: _ ->
     begin
       log_diagnostics_result
         ~tag:"get_access_sideeffect:tag not recognized"
         ~msg:name
         __FILE__ __LINE__
         ["tag: " ^ tag];
       []
     end

  | _ ->
     begin
       log_diagnostics_result
         ~tag:"get_access_sideeffect:not yet implemented"
         ~msg:name
         __FILE__ __LINE__
         [fparams_to_string fparams; attrparams_to_string "params" attrparams];
       []
     end


let convert_b_attributes_to_function_conditions
      (fintf: function_interface_t)
      (attrs: b_attributes_t):
      (xxpredicate_t list * xxpredicate_t list * xxpredicate_t list) =
  let fparameters = get_fts_parameters fintf in
  let name = fintf.fintf_name in

  List.fold_left (fun ((xpre, xside, xpost) as acc) attr ->
      match attr with
      | Attr ("access", attrparams) ->
         let pre = get_access_preconditions name fparameters attrparams in
         let side = get_access_sideeffect name fparameters attrparams in
         (pre @ xpre, side @ xside, xpost)

      | Attr ("nonnull", attrparams) ->
         let pre = get_nonnull_preconditions fparameters attrparams in
         (pre @ xpre, xside, xpost)

      | Attr ("format", attrparams) ->
         let pre = get_format_preconditions name fparameters attrparams in
         (pre @ xpre, xside, xpost)

      | Attr ("chk_pre", attrparams) ->
         let pre = get_chk_pre_conditions name fparameters attrparams in
         (pre @ xpre, xside, xpost)

      | Attr (attrname, _) ->
         begin
           log_diagnostics_result
             ~tag:"convert_b_attributes_to_function_conditions:not yet handled"
             ~msg:name
             __FILE__ __LINE__
             ["attrname: " ^ attrname];
           acc
         end) ([], [], []) attrs

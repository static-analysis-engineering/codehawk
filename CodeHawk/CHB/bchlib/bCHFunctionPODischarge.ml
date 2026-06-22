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

(* chlib *)
open CHLanguage

(* chutil *)
open CHFormatStringParser
open CHLogger

(* xprlib *)
open XprTypes
open Xsimplify

(* bchlib *)
open BCHBCTypes
open BCHExternalPredicate
open BCHGlobalState
open BCHLibTypes
open BCHXPOPredicate

module TR = CHTraceResult


let p2s = CHPrettyUtil.pretty_to_string
let x2p = XprToPretty.xpr_formatter#pr_expr
let x2s x = p2s (x2p x)

(* =========================================================================
   General utilities
   ========================================================================= *)

(** [get_constant_string x] returns a string if the expression is a constant
    address that is present in the string table.

    Note: during analysis constant strings present in the binary that are
    referenced in instructions are collected in BCHString.string_table. Care
    should be taken that the proof obligation discharge is performed after
    that process is completed. *)
let get_constant_string (loc: location_int) (x: xpr_t): string option =
  match x with
  | XConst (IntConst n) ->
     let dw = BCHDoubleword.numerical_mod_to_doubleword n in
     if BCHStrings.string_table#has_string dw then
       Some (BCHStrings.string_table#get_string dw)
     else
       begin
         log_diagnostics_result
           ~tag:"get_constant_string:string not found"
           ~msg:(p2s loc#toPretty)
           __FILE__ __LINE__
           ["address: " ^ n#toString];
         None
       end
  | _ -> None


let call_writes_to_buffer (floc: floc_int) (buffer: xpr_t): bool =
  if not floc#has_call_target then
    false
  else
    let ctinfo = floc#get_call_target in
    match floc#get_bterm_evaluator with
    | None -> false
    | Some btermev ->
       List.exists (fun se ->
           match se with
           | XXBlockWrite (_, bterm, _) ->
              (match btermev#bterm_xpr bterm with
               | Some xse ->
                  let xse' = floc#inv#rewrite_expr xse in
                  (* Check address equality by simplifying the difference *)
                  (match simplify_xpr (XOp (XMinus, [xse'; buffer])) with
                   | XConst (IntConst n) -> n#equal CHNumerical.numerical_zero
                   | _ -> false)
               | _ -> false)
           | _ -> false)
         ctinfo#get_sideeffects


(* =========================================================================
   Reaching-definition utilities
   ========================================================================= *)

(** [buffer_writer_callsite finfo cia xpr] searches for the call site
    that last wrote to the memory buffer whose address is [xpr] at
    instruction [cia].

    For a stack buffer (i.e., [xpr] is an expression relative to the
    initial stack pointer), the memory variable for the corresponding stack
    slot is obtained from the function's stackframe, and its reaching
    definitions are queried.

    On success, returns the call-site location.*)
let buffer_writer_callsite
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t): location_int option =
  match finfo#stackframe#xpr_containing_stackslot xpr with
  | Some slot ->
     let memvar = finfo#env#mk_stackslot_variable slot NoOffset in
     let symvar = finfo#env#mk_symbolic_variable memvar in
     let varinv = finfo#ivarinv loc#ci in
     let vinvs = varinv#get_var_reaching_defs symvar in
     let defsites =
       List.concat_map (fun vinv ->
           List.filter_map (fun sym ->
               let defcia = sym#getBaseName in
               if defcia = "init" then
                 None
               else if finfo#has_call_target defcia then
                 Some (BCHLocation.ctxt_string_to_location finfo#a defcia)
               else
                 None)
             vinv#get_reaching_defs)
         vinvs in
     (match defsites with
      | [defloc] -> Some defloc
      | [] ->
         begin
           log_diagnostics_result
             ~tag:"buffer_writer_callsite:no defining locations"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["xpr: " ^ (x2s xpr);
              "memvar: " ^ (p2s memvar#toPretty);
              "stackslot: " ^ (slot#name ^ "@" ^ (string_of_int slot#offset))];
           None
         end
      | _ ->
         begin
           log_diagnostics_result
             ~tag:"buffer_writer_callsite:multiple defining locations"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["xpr: " ^ (x2s xpr);
              "memvar: " ^ (p2s memvar#toPretty);
              "defsites: "
              ^ (String.concat ", " (List.map (fun l -> p2s l#toPretty) defsites))];
           None
         end)
  | None ->
     begin
       log_diagnostics_result
         ~tag:"buffer_writer_callsite:not a stack buffer"
         ~msg:(p2s loc#toPretty) __FILE__ __LINE__["xpr: " ^ (x2s xpr)];
       None
     end

(* =========================================================================
   Discharge strategies per PO type
   ========================================================================= *)

(** Discharge strategies for a single open proof obligation.

    Each strategy returns a [po_status_t]:
    - stmt: [Discharged msg]: closed, evidence in [msg]
    - delegate_local: [DelegatedLocal (cia, xpo)]: transferred to another
         instruction or another argument in the same instruction
    - delegate_api: [Delegated xxp]: transferred to the current function's
         own preconditions
    - delegate_global: [DelegatedGlobal (dw, xxp)]: registered in the global
         state at address [dw]
    - [Open]: unable to discharge
 *)

(* -------------------------------------------------------------------------
   XPOTrustedOsCmdString
   ------------------------------------------------------------------------- *)

let trusted_os_cmd_string_constant_string_stmt
      (loc: location_int) (x: xpr_t): po_status_t =
  match get_constant_string loc x with
  | Some s -> Discharged ("constant string: " ^ s)
  | _ -> Open


let trusted_os_cmd_string_delegate_local_instr
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t): po_status_t =
  let floc = BCHFloc.get_finfo_floc finfo loc in
  let btermev = floc#get_bterm_evaluator in
  if not floc#has_call_target then
    Open
  else if Option.is_none btermev then
    Open
  else
    let btermev = Option.get btermev in
    let ctinfo = floc#get_call_target in
    if call_writes_to_buffer floc xpr then
      (* the string value is written by the instruction itself (like in,
         e.g., sprintf) so the proof obligation must be transferred to
         the source of that output.*)
      List.fold_left (fun acc se ->
          match acc with
          | Open ->
             (match se with
              | XXWritesStringFromFmtString (dst, src, fmtkind, optlen) ->
                 (match (btermev#bterm_xpr dst, btermev#bterm_xpr src) with
                  | (Some dstptr, Some srcptr) ->
                     let  dstptr' = floc#inv#rewrite_expr dstptr in
                     let iswrite =
                       (match simplify_xpr (XOp (XMinus, [dstptr'; xpr])) with
                        | XConst (IntConst n) -> n#equal CHNumerical.numerical_zero
                        | _ -> false) in
                     if iswrite then
                       let xlen =
                         match optlen with
                         | Some len -> btermev#bterm_xpr len
                         | _ -> None in
                       let fmtargs =
                         match btermev#get_annotated_format_arguments src with
                         | Some fmtargs -> fmtargs
                         | _ -> [] in
                       let new_xpo =
                         XPOTrustedOsCmdFmtString (srcptr, fmtkind, xlen, fmtargs) in
                       let _ =
                         finfo#proofobligations#add_proofobligation
                           floc#l#ci new_xpo Open in
                       DelegatedLocal (loc#ci, new_xpo)
                     else
                       Open
                  | _ -> Open)
              | _ -> Open)
          | _ -> acc) Open ctinfo#get_sideeffects
    else
      Open


let trusted_os_cmd_string_delegate_local
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t): po_status_t =
  match buffer_writer_callsite finfo loc xpr with
  | None -> Open
  | Some defloc ->
     (* Check that the call at defloc has a BlockWrite side effect on the
        same buffer.  Use the invariant at defloc to evaluate expressions. *)
     let deffloc = BCHFloc.get_finfo_floc finfo defloc in
     if call_writes_to_buffer deffloc xpr then
       begin
         (* Create a new open PO at the writer call site *)
         let new_xpo = XPOTrustedOsCmdString xpr in
         finfo#proofobligations#add_proofobligation defloc#ci new_xpo Open;
         (* The original PO is delegated to the xxpredicate form *)
         DelegatedLocal (defloc#ci, new_xpo)
       end
     else
       Open


let discharge_trusted_os_cmd_string
      (finfo: function_info_int)
      (loc: location_int)
      (x: xpr_t): po_status_t =
  let status = trusted_os_cmd_string_constant_string_stmt loc x in
  let status =
    match status with
    | Open -> trusted_os_cmd_string_delegate_local_instr finfo loc x
    | _ -> status in
  let status =
    match status with
    | Open -> trusted_os_cmd_string_delegate_local finfo loc x
    | _ -> status in
  status


(* -------------------------------------------------------------------------
   XPOTrustedOsCmdFmtString
   ------------------------------------------------------------------------- *)

(* A format string is considered to construct a safe string to pass to a call
   to [system] if it does not contain any %s format specifiers.*)
let trusted_os_cmd_fmt_string_no_string_conversions
      (loc: location_int) (x: xpr_t): po_status_t =
  match get_constant_string loc x with
  | Some s ->
     let formatspec = CHFormatStringParser.parse_formatstring s false in
     if List.exists (fun a ->
            match a#get_conversion with
            | CHFormatStringParser.StringConverter -> true
            | _ -> false) formatspec#get_arguments then
       Open
     else
       Discharged ("constant format string without string converters: " ^ s)
  | _ ->
     Open


let trusted_os_cmd_fmt_string_va_list_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (x: xpr_t)
      (optlen: xpr_t option): po_status_t =
  let floc = BCHFloc.get_finfo_floc finfo loc in
  let xpxt_opt = floc#get_expression_externalizer in
  match xpxt_opt with
  | Some xpxt ->
     let xoptlen =
       match optlen with
       | Some len -> xpxt#xpr_to_bterm BCHBCTypeUtil.t_int len
       | _ -> None in
     (match xpxt#xpr_to_bterm BCHBCTypeUtil.t_charptr x with
      | Some xfmt ->
         let xpred = XXTrustedOsCmdFmtString (xfmt, FMT_ARGS, xoptlen) in
         let _ = finfo#add_precondition xpred in
         Delegated (xpred)
      | _ -> Open)
  | _ -> Open


let trusted_os_cmd_fmt_string_fmt_args_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (fmtargs: annotated_format_arg_t list): po_status_t =
  let strargs =
    List.filter (fun (conv, _, _) ->
        match conv with
        | CHFormatStringParser.StringConverter -> true
        | _ -> false) fmtargs in
  List.fold_left (fun _acc (_, _, argxpr) ->
      let new_xpo = XPOTrustedOsCmdFmtArgString (argxpr, NO_QUOTES, None) in
      finfo#proofobligations#add_proofobligation loc#ci new_xpo Open;
      DelegatedLocal (loc#ci, new_xpo)
    ) Open strargs


let discharge_trusted_os_cmd_fmt_string
      (finfo: function_info_int)
      (loc: location_int)
      (x: xpr_t)
      (kind: format_args_kind_t)
      (optlen: xpr_t option)
      (fmtargs: annotated_format_arg_t list): po_status_t =
  let status = trusted_os_cmd_fmt_string_no_string_conversions loc x in
  let status =
    match status with
    | Open ->
       (match kind with
        | VA_LIST ->
           trusted_os_cmd_fmt_string_va_list_delegate finfo loc x optlen
        | FMT_ARGS ->
           trusted_os_cmd_fmt_string_fmt_args_delegate finfo loc fmtargs)
    | _ -> status in
  match status with
  | Open ->
     begin
       log_diagnostics_result
         ~tag:"discharge_trusted_os_cmd_fmt_string"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["x: " ^ (x2s x);
          "fmtarg count: " ^ (string_of_int (List.length fmtargs))];
       status
     end
  | _ ->
     status


(* -------------------------------------------------------------------------
   XPOTrustedOsCmdFmtArgString
   ------------------------------------------------------------------------- *)

let trusted_os_cmd_fmt_arg_string_constant_string_stmt
      (loc: location_int) (x: xpr_t) (_quotes: quote_status_t): po_status_t =
  match get_constant_string loc x with
  | Some s -> Discharged ("constant string: " ^ s)
  | _ -> Open


(** Discharge by matching a [XXTrustedOsCmdString] or [XXTrustedString]
    postcondition on the call that produced [x] as its return value. *)
let trusted_os_cmd_fmt_arg_string_return_value_postcondition
      (finfo: function_info_int)
      (_loc: location_int)
      (x: xpr_t)
      (_quotes: quote_status_t)
      (_optlen: int option): po_status_t =
  match x with
  | XVar v when finfo#env#is_return_value v || finfo#env#is_sideeffect_value v ->
     TR.tfold
       ~ok:(fun callsite ->
         let ctinfo = finfo#get_call_target callsite in
         let is_trusted post =
           match post with
           | XXTrustedOsCmdString (ReturnValue _) -> true
           | XXTrustedString (ReturnValue _) -> true
           | _ -> false in
         let is_violated post =
           match post with
           | XXTainted (ReturnValue _) -> true
           | _ -> false in
         if List.exists is_trusted ctinfo#get_postconditions then
           Discharged ("return value of " ^ ctinfo#get_name ^ " is trusted")
         else if List.exists is_violated ctinfo#get_postconditions then
           Violated ("return value of " ^ ctinfo#get_name ^ " is potentially tainted")
         else
           Open)
       ~error:(fun _ -> Open)
       (finfo#env#get_call_site v)
  | _ -> Open


let trusted_os_cmd_fmt_arg_string_delegate_local
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t)
      (quotes: quote_status_t)
      (optlen: int option): po_status_t =
  match buffer_writer_callsite finfo loc xpr with
  | None ->
     begin
       log_diagnostics_result
         ~tag:"trusted_os_cmd_fmt_arg_string_delegate_local:open"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["finfo: " ^ finfo#get_name; "xpr: " ^ (x2s xpr)];
       Open
     end
  | Some defloc ->
     let deffloc = BCHFloc.get_finfo_floc finfo defloc in
     if call_writes_to_buffer deffloc xpr then
       begin
         let new_xpo = XPOTrustedOsCmdFmtArgString (xpr, quotes, optlen) in
         finfo#proofobligations#add_proofobligation defloc#ci new_xpo Open;
         DelegatedLocal (defloc#ci, new_xpo)
       end
     else
       Open


let discharge_trusted_os_cmd_fmt_arg_string
      (finfo: function_info_int)
      (loc: location_int)
      (x: xpr_t)
      (quotes: quote_status_t)
      (optlen: int option): po_status_t =
  let status =
    trusted_os_cmd_fmt_arg_string_constant_string_stmt loc x quotes in
  let status =
    match status with
    | Open ->
       trusted_os_cmd_fmt_arg_string_return_value_postcondition
         finfo loc x quotes optlen
    | _ -> status in
  let status =
    match status with
    | Open ->
       trusted_os_cmd_fmt_arg_string_delegate_local
         finfo loc x quotes optlen
    | _ -> status in
  status


(* -------------------------------------------------------------------------
   XPOOutputFormatString
   ------------------------------------------------------------------------- *)

(** Direct discharge: format string is a constant string.*)
let output_format_string_constant_string_stmt
      (loc: location_int) (x: xpr_t): po_status_t =
  match get_constant_string loc x with
  | Some s -> Discharged ("constant string: " ^ s)
  | _ -> Open


(* Delegate to a precondition on a the calling function.*)
let output_format_string_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (x: xpr_t): po_status_t =
  match x with
  | XVar v when finfo#env#is_initial_register_value v ->
     TR.tfold
       ~ok:(fun reg ->
         let _ =
           finfo#add_register_parameter_location reg BCHBCTypeUtil.t_charptr 4 in
         let ftspar = finfo#get_summary#get_parameter_for_register reg in
         let dst = ArgValue ftspar in
         let xpred = XXOutputFormatString dst in
         let _ = finfo#add_precondition xpred in
         Delegated xpred)
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"discharge_output_format_string"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["v: " ^ (p2s v#toPretty); String.concat ", " e];
           Open
         end)
       (finfo#env#get_initial_register_value_register v)
  | _ ->
     Open


let discharge_output_format_string
      (finfo: function_info_int) (loc: location_int) (xpr: xpr_t): po_status_t =
  let status = output_format_string_constant_string_stmt loc xpr in
  let status =
    match status with
    | Open -> output_format_string_delegate finfo loc xpr
    | _ -> status in
  status


(* -------------------------------------------------------------------------
   XPORestrictedOutputFormatString
   ------------------------------------------------------------------------- *)

let specifier_of_conversion (c: conversion_t): string =
  match c with
  | StringConverter -> "s"
  | IntConverter | DecimalConverter -> "d"
  | UnsignedDecimalConverter -> "u"
  | UnsignedOctalConverter -> "o"
  | UnsignedHexConverter false -> "x"
  | UnsignedHexConverter true -> "X"
  | FixedDoubleConverter false -> "f"
  | FixedDoubleConverter true -> "F"
  | ExpDoubleConverter false -> "e"
  | ExpDoubleConverter true -> "E"
  | FlexDoubleConverter false -> "g"
  | FlexDoubleConverter true -> "G"
  | HexDoubleConverter false -> "a"
  | HexDoubleConverter true -> "A"
  | UnsignedCharConverter -> "c"
  | PointerConverter -> "p"
  | OutputArgument -> "n"


let restricted_output_format_string_constant_string_stmt
      (loc: location_int) (x: xpr_t) (sl: string list): po_status_t =
  match get_constant_string loc x with
  | Some s ->
     let fmtspec = parse_formatstring s false in
     let actual =
       List.map
         (fun a -> specifier_of_conversion a#get_conversion)
         fmtspec#get_arguments in
     if actual = sl then
       Discharged (
           "format specifiers ["
           ^ (String.concat "," sl)
           ^ "] match: " ^ s)
     else
       Violated (
           "format specifiers ["
           ^ (String.concat "," actual)
           ^ "] do not match required ["
           ^ (String.concat "," sl)
           ^ "]: " ^ s)
  | _ -> Open


let restricted_output_format_string_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (x: xpr_t)
      (sl: string list): po_status_t =
  match x with
  | XVar v when finfo#env#is_initial_register_value v ->
     TR.tfold
       ~ok:(fun reg ->
         let _ =
           finfo#add_register_parameter_location reg BCHBCTypeUtil.t_charptr 4 in
         let ftspar = finfo#get_summary#get_parameter_for_register reg in
         let dst = ArgValue ftspar in
         let xpred = XXRestrictedOutputFormatString (dst, sl) in
         let _ = finfo#add_precondition xpred in
         Delegated xpred)
       ~error:(fun e ->
         begin
           log_error_result
             ~tag:"discharge_restricted_output_format_string"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["v: " ^ (p2s v#toPretty); String.concat ", " e];
           Open
         end)
       (finfo#env#get_initial_register_value_register v)
  | _ ->
     Open


let discharge_restricted_output_format_string
      (finfo: function_info_int)
      (loc: location_int)
      (x: xpr_t)
      (sl: string list): po_status_t =
  let status = restricted_output_format_string_constant_string_stmt loc x sl in
  match status with
  | Open -> restricted_output_format_string_delegate finfo loc x sl
  | _ -> status


(* -------------------------------------------------------------------------
   XPOBuffer / XPOBlockWrite (stack size check)
   ------------------------------------------------------------------------- *)

(** Discharge a buffer or block-write PO by checking the stack frame: if the
    required size fits within the available slot, discharge; if it exceeds the
    slot, the PO is violated. *)
let discharge_stack_buffer
      (finfo: function_info_int)
      (loc: location_int)
      (ty: btype_t)
      (v: variable_t)
      (off: CHNumerical.numerical_t)
      (size: CHNumerical.numerical_t)
      (tag: string): po_status_t =
  let buffer = finfo#stackframe#get_max_slot_size off#neg#toInt in
  match buffer with
  | Some slotsize ->
     if size#toInt <= slotsize then
       Discharged (
           "buffer size " ^ size#toString
           ^ " fits in available space of "
           ^ (string_of_int slotsize) ^ " bytes")
     else
       Violated (
           "buffer size "
           ^ size#toString ^ " is too large; available space is "
           ^ (string_of_int slotsize) ^ " bytes")
  | None ->
     let _ =
       log_diagnostics_result
         ~tag:("discharge_stack_buffer:" ^ tag ^ ":open")
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["unable to determine buffer size at offset " ^ off#toString;
          "v: " ^ (p2s v#toPretty);
          "ty: " ^ (BCHBCTypePretty.btype_to_string ty)] in
     Open


let blockwrite_buffer_discharge_stack_buffer
      (finfo: function_info_int)
      (loc: location_int)
      (ty: BCHBCTypes.btype_t)
      (xpr: xpr_t)
      (bwlen: xpr_t): po_status_t =
  match (xpr, bwlen) with
  | (XOp (XMinus, [XVar v; XConst (IntConst off)]), XConst (IntConst size))
       when finfo#env#is_initial_stackpointer_value v ->
     discharge_stack_buffer finfo loc ty v off size "blockwrite"
  | _ ->
     begin
       log_diagnostics_result
         ~tag:"blockwrite_buffer_discharge_stack_buffer:open"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["xpr: " ^ (x2s xpr); "bwlen: " ^ (x2s bwlen)];
       Open
     end

(* -------------------------------------------------------------------------
   XPOBlockWrite
   ------------------------------------------------------------------------- *)

(** Discharge [XPOBlockWrite(ty, XVar v, bwlen)] when [v] is an initial
    register value: promote to a precondition / side effect of the current
    function (interprocedural delegation). *)
let blockwrite_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (ty: BCHBCTypes.btype_t)
      (xpr: xpr_t)
      (bwlen: xpr_t): po_status_t =
  let floc = BCHFloc.get_finfo_floc finfo loc in
  match floc#get_expression_externalizer with
  | None ->
     begin
       log_diagnostics_result
         ~tag:"blockwrite_delegate:no expression_externalizer"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["xpr: " ^ (x2s xpr); "bwlen: " ^ (x2s bwlen)];
       Open
     end
  | Some xprxt ->
     let xlenterm =
       (* If the destination is external, but the length term cannot be
          externalized, an external predicate is created with a runtime
          value argument for its length. The rationale for still
          delegating this proof obligation is that communicating that
          this function writes to an external buffer takes priority over
          having an incomplete predicate, as the writing affects the
          semantics of the caller. *)
       match xprxt#xpr_to_bterm BCHBCTypeUtil.t_int bwlen with
       | Some bterm -> bterm
       | _ -> RunTimeValue in
     (match xprxt#xpr_to_bterm ty xpr with
      | Some (NumConstant n) when n#gt CHNumerical.numerical_zero ->
         let dw = BCHDoubleword.numerical_mod_to_doubleword n in
         let xxp = XXBlockWrite (ty, NumConstant n, xlenterm) in
         begin
           global_system_state#add_precondition dw loc xxp;
           log_diagnostics_result
             ~tag:"blockwrite_delegate:delegate_global"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["dw: " ^ dw#to_hex_string;
              "xxp: " ^ (p2s (xxpredicate_to_pretty xxp))];
           DelegatedGlobal (dw, xxp)
         end
      | Some dst ->
         let xpred = XXBlockWrite (ty, dst, xlenterm) in
         begin
           finfo#add_precondition xpred;
           finfo#add_sideeffect xpred;
           log_diagnostics_result
             ~tag:"blockwrite_delegate:delegate_api_sideeffect"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["xpred: " ^ (p2s (xxpredicate_to_pretty xpred))];
           Delegated xpred
         end
      | _ ->
         begin
           log_diagnostics_result
             ~tag:"blockwrite_delegate:open"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["xpr: " ^ (x2s xpr); "bwlen: " ^ (x2s bwlen)];
           Open
         end)


let discharge_blockwrite
      (finfo: function_info_int)
      (loc: location_int)
      (ty: btype_t)
      (xpr: xpr_t)
      (bwlen: xpr_t): po_status_t =
  let status =
    blockwrite_buffer_discharge_stack_buffer finfo loc ty xpr bwlen in
  let status =
    match status with
    | Open -> blockwrite_delegate finfo loc ty xpr bwlen
    | _ -> status in
  match status with
  | Open ->
     begin
       log_diagnostics_result
         ~tag:"discharge_blockwrite:open"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["xpr: " ^ (x2s xpr); "bwlen: " ^ (x2s bwlen)];
       status
     end
  | _ ->
     status

(* -------------------------------------------------------------------------
   XPOBuffer
   ------------------------------------------------------------------------- *)

let buffer_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (ty: BCHBCTypes.btype_t)
      (xpr: xpr_t)
      (bwlen: xpr_t): po_status_t =
  let floc = BCHFloc.get_finfo_floc finfo loc in
  match floc#get_expression_externalizer with
  | None ->
     begin
       log_diagnostics_result
         ~tag:"buffer_delegate:no expression_externalizer"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["xpr: " ^ (x2s xpr); "bwlen: " ^ (x2s bwlen)];
       Open
     end
  | Some xprxt ->
     (match xprxt#xpr_to_bterm ty xpr with
      | Some (NumConstant n) when n#gt CHNumerical.numerical_zero ->
         let dw = BCHDoubleword.numerical_mod_to_doubleword n in
         (match xprxt#xpr_to_bterm BCHBCTypeUtil.t_int bwlen with
          | Some (NumConstant ns) ->
             let xxp = XXBuffer (ty, NumConstant n, NumConstant ns) in
             begin
               global_system_state#add_precondition dw loc xxp;
               log_diagnostics_result
                 ~tag:"buffer_delegate:delegate_global"
                 ~msg:(p2s loc#toPretty)
                 __FILE__ __LINE__
                 ["dw: " ^ dw#to_hex_string;
                  "xxp: " ^ (p2s (xxpredicate_to_pretty xxp))];
               DelegatedGlobal (dw, xxp)
             end
          | _ ->
             begin
               log_diagnostics_result
                 ~tag:"buffer_delegate:delegate_global:open"
                 ~msg:(p2s loc#toPretty)
                 __FILE__ __LINE__
                 ["dw: " ^ dw#to_hex_string; "bwlen: " ^ (x2s bwlen)];
               Open
             end)
      | Some dst ->
         (match xprxt#xpr_to_bterm BCHBCTypeUtil.t_int bwlen with
          | Some lenterm ->
             let xpred = XXBuffer (ty, dst, lenterm) in
             let _ = finfo#add_precondition xpred in
             Delegated xpred
          | _ ->
             begin
               log_diagnostics_result
                 ~tag:"buffer_delegate:dest:open"
                 ~msg:(p2s loc#toPretty)
                 __FILE__ __LINE__
                 ["dst: " ^ (BCHBTerm.bterm_to_string dst); "bwlen: " ^ (x2s bwlen)];
               Open
             end)
      | _ ->
         begin
           log_diagnostics_result
             ~tag:"buffer_delegate:open"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["xpr: " ^ (x2s xpr); "bwlen: " ^ (x2s bwlen)];
           Open
         end)


let discharge_buffer
      (finfo: function_info_int)
      (loc: location_int)
      (ty: btype_t)
      (xpr: xpr_t)
      (bwlen: xpr_t): po_status_t =
  let status =
    blockwrite_buffer_discharge_stack_buffer finfo loc ty xpr bwlen in
  let status =
    match status with
    | Open -> buffer_delegate finfo loc ty xpr bwlen
    | _ -> status in
  match status with
  | Open ->
     begin
       log_diagnostics_result
         ~tag:"discharge_buffer:open"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["xpr: " ^ (x2s xpr); "bwlen: " ^ (x2s bwlen)];
       status
     end
  | _ ->
     status

(* -------------------------------------------------------------------------
   XPONotNull
   ------------------------------------------------------------------------- *)

let not_null_constant_address (loc: location_int) (xpr: xpr_t): po_status_t =
  match xpr with
  | XConst (IntConst n) ->
     let _ =
       log_diagnostics_result
         ~tag:"not_null_constant_address"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__ ["address: " ^ n#toString] in
     Discharged ("constant address: " ^ n#toString)
  | _ ->
     Open


let not_null_stack_address
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t): po_status_t =
  match xpr with
  | XOp (XMinus, [XVar v; _]) when finfo#env#is_initial_stackpointer_value v ->
     let _ =
       log_diagnostics_result
         ~tag:"not_null_stack_address"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__ ["address: " ^ (x2s xpr)] in
     Discharged ("stack address: " ^ (x2s xpr))
  | _ ->
     Open


let not_null_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t): po_status_t =
  let floc = BCHFloc.get_finfo_floc finfo loc in
  match floc#get_expression_externalizer with
  | None ->
     begin
       log_diagnostics_result
         ~tag:"not_null_delegate:no expression_externalizer"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__ ["xpr: " ^ (x2s xpr)];
       Open
     end
  | Some xprxt ->
     (match xprxt#xpr_to_bterm BCHBCTypeUtil.t_voidptr xpr with
      | Some (NumConstant n) when n#gt CHNumerical.numerical_zero ->
         Discharged ("constant address: " ^ n#toString)
      | Some t ->
         let xxp = XXNotNull t in
         let _ = finfo#add_precondition xxp in
         Delegated xxp
      | _ ->
         begin
           log_diagnostics_result
             ~tag:"not_null_delegate:open"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__ ["xpr: " ^ (x2s xpr)];
           Open
         end)


let discharge_not_null
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t): po_status_t =
  let status = not_null_constant_address loc xpr in
  let status =
    match status with
    | Open -> not_null_stack_address finfo loc xpr
    | _ -> status in
  let status =
    match status with
    | Open -> not_null_delegate finfo loc xpr
    | _ -> status in
  match status with
  | Open ->
     begin
       log_diagnostics_result
         ~tag:"discharge_not_null:open"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__ ["xpr: " ^ (x2s xpr)];
       status
     end
  | _ ->
     status

(* -------------------------------------------------------------------------
   XPONullTerminated
   ------------------------------------------------------------------------- *)

let null_terminated_constant_string
      (loc: location_int) (xpr: xpr_t): po_status_t =
  match get_constant_string loc xpr with
  | Some s ->
     begin
       log_diagnostics_result
         ~tag:"null_terminated_constant_string"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["string: " ^ s];
       Discharged ("constant string: " ^ s)
     end
  | _ ->
     Open


let null_terminated_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t): po_status_t =
  let floc = BCHFloc.get_finfo_floc finfo loc in
  match floc#get_expression_externalizer with
  | None ->
     begin
       log_diagnostics_result
         ~tag:"null_termiatned_delegate:no expression_externalizer"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__ ["xpr: " ^ (x2s xpr)];
       Open
     end
  | Some xprxt ->
     (match xprxt#xpr_to_bterm BCHBCTypeUtil.t_voidptr xpr with
      | Some (NumConstant n) when n#gt CHNumerical.numerical_zero ->
         Discharged ("constant address: " ^ n#toString)
      | Some t ->
         let xxp = XXNullTerminated t in
         let _ = finfo#add_precondition xxp in
         Delegated xxp
      | _ ->
         begin
           log_diagnostics_result
             ~tag:"null_terminated_delegate:open"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["xpr: " ^ (x2s xpr)];
           Open
         end)


let discharge_null_terminated
      (finfo: function_info_int)
      (loc: location_int)
      (xpr: xpr_t): po_status_t =
  let status = null_terminated_constant_string loc xpr in
  let status =
    match status with
    | Open -> null_terminated_delegate finfo loc xpr
    | _ -> status in
  match status with
  | Open ->
     begin
       log_diagnostics_result
         ~tag:"discharge_null_terminated:open"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__ ["xpr: " ^ (x2s xpr)];
       status
     end
  | _ ->
     status

(* -------------------------------------------------------------------------
   XPOInitializedRange
   ------------------------------------------------------------------------- *)

let initialized_range_constant_string
      (loc: location_int) (xpr: xpr_t): po_status_t =
  match get_constant_string loc xpr with
  | Some s ->
     begin
       log_diagnostics_result
         ~tag:"initialized_range_constant_string"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["string: " ^ s];
       Discharged ("constant string: " ^ s)
     end
  | _ ->
     Open


let initialized_range_delegate
      (finfo: function_info_int)
      (loc: location_int)
      (ty: BCHBCTypes.btype_t)
      (xpr: xpr_t)
      (size: xpr_t): po_status_t =
  let floc = BCHFloc.get_finfo_floc finfo loc in
  match floc#get_expression_externalizer with
  | None ->
     begin
       log_diagnostics_result
         ~tag:"initialized_range_delegate:no expression_externalizer"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__
         ["xpr: " ^ (x2s xpr); "size: " ^ (x2s size)];
       Open
     end
  | Some xprxt ->
     (match xprxt#xpr_to_bterm ty xpr with
      | Some (NumConstant n) when n#gt CHNumerical.numerical_zero ->
         let dw = BCHDoubleword.numerical_mod_to_doubleword n in
         (match xprxt#xpr_to_bterm BCHBCTypeUtil.t_int size with
          | Some (NumConstant ns) ->
             let xxp = XXInitializedRange (ty, NumConstant n, NumConstant ns) in
             begin
               global_system_state#add_precondition dw loc xxp;
               log_diagnostics_result
                 ~tag:"buffer_delegate:delegate_global"
                 ~msg:(p2s loc#toPretty)
                 __FILE__ __LINE__
                 ["dw: " ^ dw#to_hex_string;
                  "xxp: " ^ (p2s (xxpredicate_to_pretty xxp))];
               DelegatedGlobal (dw, xxp)
             end
          | _ ->
             begin
               log_diagnostics_result
                 ~tag:"initialized_range_delegate:delegate_global:open"
                 ~msg:(p2s loc#toPretty)
                 __FILE__ __LINE__
                 ["dw: " ^ dw#to_hex_string; "size: " ^ (x2s size)];
               Open
             end)
      | Some dst ->
         (match xprxt#xpr_to_bterm BCHBCTypeUtil.t_int size with
          | Some lenterm ->
             let xpred = XXInitializedRange (ty, dst, lenterm) in
             let _ = finfo#add_precondition xpred in
             Delegated xpred
          | _ ->
             begin
               log_diagnostics_result
                 ~tag:"initialized_range_delegate:dest:open"
                 ~msg:(p2s loc#toPretty)
                 __FILE__ __LINE__
                 ["dst: " ^ (BCHBTerm.bterm_to_string dst); "size: " ^ (x2s size)];
               Open
             end)
      | _ ->
         begin
           log_diagnostics_result
             ~tag:"initialized_range_delegate:open"
             ~msg:(p2s loc#toPretty)
             __FILE__ __LINE__
             ["xpr: " ^ (x2s xpr); "size: " ^ (x2s size)];
           Open
         end)


let discharge_initialized_range
      (finfo: function_info_int)
      (loc: location_int)
      (ty: btype_t)
      (xpr: xpr_t)
      (size: xpr_t): po_status_t =
  let status = initialized_range_constant_string loc xpr in
  let status =
    match status with
    | Open -> initialized_range_delegate finfo loc ty xpr size
    | _ -> status in
  match status with
  | Open ->
     begin
       log_diagnostics_result
         ~tag:"discarhge_initialized_range:open"
         ~msg:(p2s loc#toPretty)
         __FILE__ __LINE__ ["xpr: " ^ (x2s xpr); "size: " ^ (x2s size)];
       Open
     end
  | _ ->
     status

(* =========================================================================
   Main dispatch
   ========================================================================= *)

(** Attempt to discharge or delegate a single open proof obligation.

    Returns the new status, or [Open] if unable to discharge. *)
let discharge_one
      (finfo: function_info_int)
      (po: proofobligation_int): po_status_t =
  match po#xpo with

  | XPOTrustedOsCmdString x ->
     discharge_trusted_os_cmd_string finfo po#loc x

  | XPOTrustedOsCmdFmtString (x, kind, optlen, fmtargs) ->
     discharge_trusted_os_cmd_fmt_string finfo po#loc x kind optlen fmtargs

  | XPOTrustedOsCmdFmtArgString (x, quotes, optlen) ->
     discharge_trusted_os_cmd_fmt_arg_string finfo po#loc x quotes optlen

  | XPOOutputFormatString x ->
     discharge_output_format_string finfo po#loc x

  | XPORestrictedOutputFormatString (x, sl) ->
     discharge_restricted_output_format_string finfo po#loc x sl

  | XPOBlockWrite (ty, x, bwlen) ->
     discharge_blockwrite finfo po#loc ty x bwlen

  | XPOBuffer (ty, x, bwlen) ->
     discharge_buffer finfo po#loc ty x bwlen

  | XPONotNull x ->
     discharge_not_null finfo po#loc x

  | XPONullTerminated x ->
     discharge_null_terminated finfo po#loc x

  | XPOInitializedRange (ty, x, size) ->
     discharge_initialized_range finfo po#loc ty x size

  | _ -> Open


(* =========================================================================
   Fixpoint iteration
   ========================================================================= *)

(** Run one discharge pass over all currently open proof obligations.
    Returns the number of obligations whose status changed. *)
let discharge_pass
      (finfo: function_info_int): int =
  let openpos = finfo#proofobligations#open_proofobligations in
  List.fold_left (fun changed po ->
      let newstatus = discharge_one finfo po in
      match newstatus with
      | Open -> changed
      | _ ->
         begin
           log_diagnostics_result
             ~tag:"discharge_pass"
             ~msg:(p2s po#loc#toPretty)
             __FILE__ __LINE__
             ["xpo: " ^ (p2s (xpo_predicate_to_pretty po#xpo));
              "status: "
              ^ (p2s (BCHProofObligations.po_status_to_pretty newstatus))];
           po#update_status newstatus;
           changed + 1
         end)
    0 openpos


(* =========================================================================
   Entry point
   ========================================================================= *)

(** Discharge all open proof obligations for [finfo], iterating to fixpoint.

    Each pass may close some obligations directly and create new ones via
    intra-function delegation (e.g., by adding a [XPOTrustedOsCmdString] at
    the [sprintf] call site that wrote the buffer questioned at a [system]
    call site).  Iteration continues until a pass produces no changes, at
    which point the remaining open obligations cannot be decided within the
    function.

    [max_passes] is a safety bound on iteration depth (default 8); in
    practice the chain system → sprintf → format-arg resolves in at most 3
    passes. *)
let discharge_function_proofobligations
      ?(max_passes = 8)
      (finfo: function_info_int): unit =
  let rec loop n =
    if n = 0 then
      ()
    else
      let changed = discharge_pass finfo in
      if changed > 0 then loop (n - 1)
  in
  loop max_passes

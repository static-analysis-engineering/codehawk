(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2025  Aarno Labs LLC

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
open CHNumerical

(* chutil *)
open CHLogger
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open Xsimplify

(* bchlib *)
open BCHBCTypeUtil
open BCHBTerm
open BCHDoubleword
open BCHExternalPredicate
open BCHGlobalState
open BCHLibTypes
open BCHStrings
open BCHXPOPredicate

module TR = CHTraceResult


let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)

let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("callsemanticsrecorder:" ^ tag) msg


class call_semantics_recorder_t
        (loc: location_int)
        (finfo: function_info_int)
        (termev: bterm_evaluator_int)
        (xprxt: expression_externalizer_int)
        (ctinfo: call_target_info_int): call_semantics_recorder_int =
object (self)

  method termev = termev

  method private xprxt = xprxt

  method loc = loc

  method finfo = finfo

  method calltargetinfo = ctinfo

  method private simplify_precondition (xpo: xpo_predicate_t) =
    match xpo with
    | XPORelationalExpr (op, x1, x2) ->
       let x = XOp (relational_op_to_xop op, [x1; x2]) in
       if is_true (simplify_xpr x) then
         Discharged ((x2s x) ^ " simplified to true")
       else
         Open
    | XPONonNegative x ->
       (match simplify_xpr x with
        | XConst (IntConst n) when n#geq numerical_zero ->
           Discharged ("constant is non-negative: " ^ n#toString)
        | _ -> Open)
    | XPOPositive x ->
       (match simplify_xpr x with
        | XConst (IntConst n) when n#gt numerical_zero ->
           Discharged ("constant is positive: " ^ n#toString)
        | _ -> Open)
    | XPONotNull x ->
       (match x with
        | XConst (IntConst n) when n#gt numerical_zero ->
           let n = n#modulo numerical_e32 in
           Discharged
             ("non-null constant address: "
              ^ TR.tget_ok (numerical_to_hex_string n))
        | XOp (XMinus, [XVar v; _]) as addr
             when self#finfo#env#is_initial_stackpointer_value v ->
           Discharged ("stack-pointer address: " ^ (x2s addr))
        | _ -> Open)
    | XPONullTerminated x ->
       (match x with
        | XConst (IntConst n) ->
           let dw = numerical_mod_to_doubleword n in
           if string_table#has_string dw then
             Discharged ("constant string: " ^ (string_table#get_string dw))
           else
             Open
        | _ -> Open)
    | XPOInitializedRange (ty, ptr, size) when is_int ty ->
       (match (ptr, size) with
        | (XConst (IntConst n1), XOp ((Xf "ntpos"), [XConst (IntConst n2)]))
             when n1#equal n2 ->
           let dw = numerical_mod_to_doubleword n1 in
           if string_table#has_string dw then
             Discharged ("constant string: " ^ (string_table#get_string dw))
           else
             Open
        | _ -> Open)
    | XPOBuffer (ty, ptr, size) when is_int ty ->
       (match (ptr, size) with
        | (XConst (IntConst n1), XOp ((Xf "ntpos"), [XConst (IntConst n2)]))
             when n1#equal n2 ->
           let dw = numerical_mod_to_doubleword n1 in
           if string_table#has_string dw then
             Discharged ("constant string: " ^ (string_table#get_string dw))
           else
             Open
        | _ -> Open)
    | XPOOutputFormatString x ->
       (match x with
        | XConst (IntConst n) ->
           let dw = numerical_mod_to_doubleword n in
           if string_table#has_string dw then
             Discharged ("constant string: " ^ (string_table#get_string dw))
           else
             Open
        | _ -> Open)
    | XPOAllocationBase x ->
       (match x with
        | XVar v when self#finfo#env#is_return_value v ->
           log_tfold
             (log_error "simplify_precondition" "invalid call site")
             ~ok:(fun cia ->
               if self#finfo#has_call_target cia then
                 let ctinfo = self#finfo#get_call_target cia in
                 let name = ctinfo#get_name in
                 if name == "malloc" || name == "strdup" then
                   Discharged ("return value from " ^ name)
                 else
                   Open
               else
                 Open)
             ~error:(fun _ -> Open)
             (self#finfo#env#get_call_site v)
        | _ -> Open)
    | _ -> Open

  method private delegate_precondition (xpo: xpo_predicate_t): po_status_t =
    match xpo with
    | XPONotNull x ->
       let x = simplify_xpr x in
       (match self#xprxt#xpr_to_bterm t_voidptr x with
        | Some (NumConstant n) when n#gt numerical_zero ->
           let dw = numerical_mod_to_doubleword n in
           DelegatedGlobal (dw, XXNotNull (NumConstant n))
        | Some t -> Delegated (XXNotNull t)
        | _ -> Open)
    | XPONullTerminated x ->
       let x = simplify_xpr x in
       (match self#xprxt#xpr_to_bterm t_voidptr x with
        | Some (NumConstant n) when n#gt numerical_zero ->
           let dw = numerical_mod_to_doubleword n in
           DelegatedGlobal (dw, XXNullTerminated (NumConstant n))
        | Some t -> Delegated (XXNullTerminated t)
        | _ -> Open)
    | XPOBlockWrite (ty, ptr, size) ->
       (match self#xprxt#xpr_to_bterm t_voidptr ptr with
        | Some (NumConstant n) when n#gt numerical_zero ->
           let dw = numerical_mod_to_doubleword n in
           (match self#xprxt#xpr_to_bterm t_int size with
            | Some (NumConstant ns) ->
               DelegatedGlobal
                 (dw, XXBlockWrite(ty, NumConstant n, NumConstant ns))
            | _ -> Open)
        | Some ptrt ->
           (match self#xprxt#xpr_to_bterm t_int size with
            | Some sizet ->
               Delegated (XXBlockWrite (ty, ptrt, sizet))
            | _ -> Open)
        | _ -> Open)
    | XPOBuffer (ty, ptr, size) ->
       (match self#xprxt#xpr_to_bterm t_voidptr ptr with
        | Some (NumConstant n) when n#gt numerical_zero ->
           let dw = numerical_mod_to_doubleword n in
           (match self#xprxt#xpr_to_bterm t_int size with
            | Some (NumConstant ns) ->
               DelegatedGlobal
                 (dw, XXBlockWrite(ty, NumConstant n, NumConstant ns))
            | _ -> Open)
        | Some ptrt ->
           (match self#xprxt#xpr_to_bterm t_int size with
            | Some sizet ->
               Delegated (XXBuffer (ty, ptrt, sizet))
            | _ -> Open)
        | _ -> Open)
    | XPOInitializedRange (ty, ptr, size) ->
       (match self#xprxt#xpr_to_bterm t_voidptr ptr with
        | Some (NumConstant n) when n#gt numerical_zero ->
           let dw = numerical_mod_to_doubleword n in
           (match self#xprxt#xpr_to_bterm t_int size with
            | Some (NumConstant ns) ->
               DelegatedGlobal
                 (dw, XXBlockWrite(ty, NumConstant n, NumConstant ns))
            | _ -> Open)
        | Some ptrt ->
           (match self#xprxt#xpr_to_bterm t_int size with
            | Some sizet ->
               Delegated (XXInitializedRange (ty, ptrt, sizet))
            | _ -> Open)
        | _ -> Open)
    | _ -> Open

  method record_precondition (pre: xxpredicate_t) =
    let xpo = xxp_to_xpo_predicate self#termev self#loc pre in
    let status = self#simplify_precondition xpo in
    match status with
    | Discharged _ -> self#add_po xpo status
    | _ ->
       let status = self#delegate_precondition xpo in
       match status with
       | Delegated xxp ->
          begin
            self#add_po xpo status;
            self#add_pre xxp
          end
       | DelegatedGlobal (dw, xxp) ->
          begin
            self#add_po xpo status;
            self#add_gpo dw xxp
          end
       | _ ->
          self#add_po xpo status

  method private record_blockreads (pre: xxpredicate_t) =
    let _ =
      ch_diagnostics_log#add
        "record blockread"
        (LBLOCK [loc#toPretty; STR ": ";
                 xxpredicate_to_pretty pre]) in
    let xpo = xxp_to_xpo_predicate self#termev self#loc pre in
    match xpo with
    | XPOBuffer (ty, addr, size) ->
       (match self#termev#xpr_local_stack_address addr with
        | Some offset ->
           let _ =
             ch_diagnostics_log#add
               "record blockread"
               (LBLOCK [loc#toPretty; STR ": ";
                        STR "offset: ";
                        INT offset]) in
           let csize =
             match size with
             | XConst (IntConst n) -> Some n#toInt
             | _ ->
                TR.tfold_default (fun s -> Some s) None (size_of_btype ty) in
           self#finfo#stackframe#add_block_read
             ~offset:(-offset) ~size:csize ~typ:(Some ty) self#loc#ci
        | _ -> ())
    | _ -> ()

  method private add_po (xpo: xpo_predicate_t) (status: po_status_t) =
    self#finfo#proofobligations#add_proofobligation self#loc#ci xpo status

  method private add_gpo (dw: doubleword_int) (xxp: xxpredicate_t) =
    global_system_state#add_precondition dw self#loc xxp

  method private add_pre (xxp: xxpredicate_t) =
    self#finfo#update_summary (self#finfo#get_summary#add_precondition xxp)

  method private add_se (xxp: xxpredicate_t) =
    self#finfo#update_summary (self#finfo#get_summary#add_sideeffect xxp)

  method record_sideeffect (se: xxpredicate_t) =
    let xpo = xxp_to_xpo_predicate self#termev self#loc se in
    match (se, xpo) with
    | (XXBlockWrite (_, taddr, _tsize),
       XPOBlockWrite (ty, addr, size)) ->
       (match self#termev#xpr_local_stack_address addr with
        | Some offset ->
           let numoffset = (CHNumerical.mkNumerical offset)#neg in
           let csize =
             match size with
             | XConst (IntConst n) -> Some n#toInt
             | _ ->
                TR.tfold_default (fun s -> Some s) None (size_of_btype ty) in
           let sevalue =
             self#finfo#env#mk_stack_sideeffect_value
               ~btype:(Some ty) self#loc#ci numoffset (bterm_to_string taddr) in
           self#finfo#stackframe#add_block_write
             ~offset:(-offset)
             ~size:csize
             ~typ:(Some ty)
             ~xpr:(Some (XVar sevalue))
             self#loc#ci
        | _ ->
           match self#xprxt#xpr_to_bterm ty addr with
           | Some t ->
              (match self#xprxt#xpr_to_bterm t_int size with
               | Some sizet ->
                  let xxpse = XXBlockWrite (ty, t, sizet) in
                  self#add_se xxpse
               | _ ->
                  chlog#add
                    "external side effect not recorded"
                    (LBLOCK [
                         self#loc#toPretty;
                         STR ": ";
                         (xpo_predicate_to_pretty xpo)]))
           | _ ->
              chlog#add
                "blockwrite not recorded"
                (LBLOCK [
                     self#loc#toPretty;
                     STR ": ";
                     (xpo_predicate_to_pretty xpo)]))
    | _ ->
       chlog#add
         "side effect not recorded"
         (LBLOCK [self#loc#toPretty; STR ": "; (xpo_predicate_to_pretty xpo)])

  method record_callsemantics =
    begin
      List.iter self#record_precondition self#calltargetinfo#get_preconditions;
      List.iter self#record_sideeffect self#calltargetinfo#get_sideeffects;
      List.iter self#record_blockreads self#calltargetinfo#get_preconditions;
    end

end


let mk_callsemantics_recorder = new call_semantics_recorder_t

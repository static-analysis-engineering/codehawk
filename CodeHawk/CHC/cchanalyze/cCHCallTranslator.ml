(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
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
open CHLogger
open CHNestedCommands
open CHPrettyUtil

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open XprUtil

(* cchlib *)
open CCHBasicTypes
open CCHBasicUtil
open CCHContext
open CCHExternalPredicate
open CCHFunctionSummary
open CCHLibTypes
open CCHTypesToPretty
open CCHTypesUtil
open CCHUtilities

(* cchpre *)
open CCHInvariantFact
open CCHPreTypes
open CCHProofScaffolding

(* cchanalyze *)
open CCHAnalysisTypes
open CCHCommand

module H = Hashtbl


let cd = CCHDictionary.cdictionary

let pr_expr = xpr_formatter#pr_expr
let p2s = pretty_to_string
let fenv = CCHFileEnvironment.file_environment


let is_assert_fail_function fname =  fname = "__assert_fail"


let get_function_summary (fname:string) =
    if fenv#has_external_header fname then
      let header = fenv#get_external_header fname in
      if function_summary_library#has_summary header fname then
        Some (function_summary_library#get_summary fname)
      else
        None
    else if function_summary_library#has_builtin_summary fname then
      Some (function_summary_library#get_summary fname)
    else
      None


let get_postconditions
      (caller:string)
      (callee:string option)
      (context:program_context_int):
      (annotated_xpredicate_t list * annotated_xpredicate_t list) =
  match callee with
  | Some callee ->
     begin
       match get_function_summary callee with
       | Some fs -> (fs.fs_postconditions, fs.fs_error_postconditions)
       | _ ->
          if proof_scaffolding#has_direct_callsite caller context then
            let directcallsite =
              proof_scaffolding#get_direct_callsite caller context in
            (directcallsite#get_postassumes,[])
          else if proof_scaffolding#has_indirect_callsite caller context then
            let indirectcallsite =
              proof_scaffolding#get_indirect_callsite caller context in
            (indirectcallsite#get_postassumes,[])
          else
            begin
              ch_error_log#add
                "no callsite"
                (LBLOCK [
                     STR "Caller: "; STR caller; STR "; callee: "; STR callee]);
              ([], [])
            end
     end
  | _ ->
     if proof_scaffolding#has_indirect_callsite caller context then
       let indirectcallsite =
         proof_scaffolding#get_indirect_callsite caller context in
       (indirectcallsite#get_postassumes,[])
     else
       begin
         ch_error_log#add
           "no callsite"
           (LBLOCK [
                STR "Caller: "; STR caller; STR "; context: "; context#toPretty]);
         ([], [])
       end


let get_sideeffects
      (caller:string)
      (callee:string option)
      (context:program_context_int):annotated_xpredicate_t list =
  match callee with
  | Some callee ->
     begin
       match get_function_summary callee with
       | Some fs -> fs.fs_sideeffects
       | _ ->
          if proof_scaffolding#has_direct_callsite caller context then
            let directcallsite =
              proof_scaffolding#get_direct_callsite caller context in
            directcallsite#get_postassumes
          else if proof_scaffolding#has_indirect_callsite caller context then
            let indirectcallsite =
              proof_scaffolding#get_indirect_callsite caller context in
            indirectcallsite#get_postassumes
          else
            begin
              ch_error_log#add
                "no callsite"
                (LBLOCK [
                     STR "Caller: "; STR caller; STR "; callee: "; STR callee]);
              []
            end
     end
  | _ ->
     if proof_scaffolding#has_indirect_callsite caller context then
       let indirectcallsite =
         proof_scaffolding#get_indirect_callsite caller context in
       indirectcallsite#get_postassumes
     else
       begin
         ch_error_log#add
           "no callsite"
           (LBLOCK [
                STR "Caller: "; STR caller; STR "; context: "; context#toPretty]);
         []
       end


let make_range_assert env (v:variable_t) (lb:numerical_t) (ub:numerical_t) =
  let tmpProvider = (fun () -> env#mk_num_temp) in
  let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
  let lbx = XOp (XGe, [XVar v; num_constant_expr lb]) in
  let ubx = XOp (XLe, [XVar v; num_constant_expr ub])  in
  let (lbcode,bLbExp) = xpr2boolexpr tmpProvider cstProvider lbx in
  let (ubcode,bUbExp) = xpr2boolexpr tmpProvider cstProvider ubx in
  [lbcode;
   ubcode;
   make_c_cmd (make_assert bLbExp);
   make_c_cmd  (make_assert bUbExp)]


let call_does_not_return
      (caller:string) (callee:string option) (context:program_context_int) =
  let (post, _) = get_postconditions caller callee context in
  List.exists (fun (p, _) -> match p with XFalse -> true | _ -> false) post


class num_call_translator_t
        (env:c_environment_int)
        (orakel:orakel_int)
        (exp_translator:exp_translator_int):call_translator_int =
object (self)

  val mutable context = mk_program_context ()
  val fdecls = env#get_fdecls
  val mutable location = unknown_location

  method translate
           (ctxt:program_context_int)
           (loc:location)
           (lhs:lval option)
           (f:exp)
           (args:exp list) =
    let _ = context <- ctxt in
    let _ = location <- loc in
    try
      match f with
      | Lval (Var (fname,fvid),NoOffset) ->
         self#translate_known_call lhs fname fvid args
      | Lval (Mem e,NoOffset) ->
         self#translate_indirect_deref_call lhs e args
      | _ ->
         self#translate_indirect_call lhs f args
    with
    | CCHFailure p ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Error in translating call: ";
                 exp_to_pretty f;
                 STR " with arguments ";
                 pretty_print_list args exp_to_pretty "(" "," ")";
                 (match lhs with
                  | Some lval ->
                     LBLOCK [
                         STR " and lhs variable ";
                         lval_to_pretty lval]
                  | _ -> STR "");
                 STR ": ";
                 p]))


  method private translate_known_call
                   (lhs:lval option)
                   (fname:string)
                   (fvid:int)
                   (args:exp list) =
    if call_does_not_return env#get_functionname (Some fname) context then
      let _ =
        chlog#add
          "call does not return (numerical)"
          (LBLOCK [STR env#get_functionname; STR ": "; STR fname]) in
      [make_c_cmd (ASSERT FALSE)]
    else
      let tmpProvider = fun () -> env#mk_num_temp in
      let cstProvider = fun (n:numerical_t) -> env#mk_num_constant n in

      let vinfo = fdecls#get_varinfo_by_vid fvid in
      let fnargs = List.map (exp_translator#translate_exp context) args in
      let fnxargs = List.map (orakel#get_external_value context) fnargs in
      let frVar = env#mk_function_return_value location context vinfo fnxargs in
      let rangeconstraints =
        match vinfo.vtype  with
        | TFun ((TInt (IChar, _)), _, _, _) | TFun ((TInt (ISChar, _)), _, _, _) ->
           let _ =
             chlog#add "return value range constraint" (LBLOCK [STR fname]) in
           (make_range_assert env  frVar (mkNumerical (-128)) (mkNumerical 127))
        | _ -> [] in
      let returntype =
        match fenv#get_type_unrolled vinfo.vtype with
        | TFun (ty, _, _, _) -> ty
        | _ ->
           raise
             (CCHFailure
                (LBLOCK [
                     STR "Unexpected type for function variable: ";
                     STR fname;
                     STR ": ";
                     typ_to_pretty vinfo.vtype])) in
      let argassigns =
        List.map (fun x ->
            let tmp = env#mk_num_temp in
            let (rhscode,numexp) = xpr2numexpr tmpProvider cstProvider x in
            let assign = make_c_cmd (ASSIGN_NUM (tmp,numexp)) in
            (tmp, [rhscode; assign])) fnargs in
      let argtmpvars = List.map fst argassigns in
      let argassigns = List.concat (List.map snd argassigns) in
      let callop =
        make_c_cmd
          (OPERATION
             { op_name = new symbol_t ~atts:[fname] "call";
               op_args =
                 List.map (fun v -> (v#getName#getBaseName, v, READ))
                   argtmpvars }) in
      let callop = make_c_cmd_block (rangeconstraints @ [callop]) in
      let rcode =
        match lhs with
        | None -> []
        | Some lval ->
           let postconditions = self#get_postconditions fname in
           let rvar = exp_translator#translate_lhs context lval in
           if rvar#isTmp then
             let memoryvars = env#get_memory_variables in
             let _ =
               log_diagnostics_result
                 ~tag:"abstract memory variables"
                 ~msg:env#get_functionname
                 __FILE__ __LINE__
                 (("callee: " ^ fname)
                  :: (List.map (fun v -> p2s v#toPretty) memoryvars)) in
             [make_c_cmd (ABSTRACT_VARS memoryvars)]
           else
             let ty = fenv#get_type_unrolled (env#get_variable_type rvar) in
             match ty with
             | TPtr _ ->
                (* problem: rvar is not a registered memory variable, so env will
                   return all memory variables, which will all be abstracted,
                   causing loss of precision *)
                let optbasevar =
                  self#get_external_post_value postconditions fnargs in
                let memoryvars =
                  match optbasevar with
                  | Some (XVar v) -> env#get_memory_variables_with_base v
                  | _ -> env#get_memory_variables_with_base rvar in
                let _ =
                  log_diagnostics_result
                    ~tag:"abstract memory variables"
                    ~msg:env#get_functionname
                    __FILE__ __LINE__
                    (("callee: " ^ fname)
                     :: ("base: " ^ (p2s rvar#toPretty))
                     :: (List.map (fun v -> p2s v#toPretty) memoryvars)) in
                let fieldcode = make_c_cmd (ABSTRACT_VARS memoryvars) in
                let (rcode, rval) =
                  self#get_arg_post_value postconditions fnargs frVar returntype in
                let assign = make_c_cmd (ASSIGN_NUM (rvar, rval)) in
                let postassert =
                  self#get_post_assert postconditions fname fvid rvar fnargs in
                [fieldcode; rcode; assign; postassert]
             | _ ->
                let (rcode,rval) =
                  self#get_arg_post_value postconditions fnargs frVar returntype in
                let assign = make_c_cmd (ASSIGN_NUM (rvar, rval)) in
                let postassert =
                  self#get_post_assert postconditions fname fvid rvar fnargs in
                [rcode; assign; postassert] in
      let assertfail =
        if is_assert_fail_function fname then
          make_c_cmd (ASSERT FALSE)
        else
          make_c_nop () in
      let sideeffects = self#get_sideeffects fname fvid args fnxargs in
      argassigns @ [callop; assertfail; sideeffects] @ rcode

  method private set_indirect_call vinfo =
    if proof_scaffolding#has_indirect_callsite env#get_functionname context then
      let callsite =
        proof_scaffolding#get_indirect_callsite env#get_functionname context in
      callsite#set_callees [vinfo]
    else
      ch_error_log#add
        "indirect call not found"
        (LBLOCK [
             STR env#get_functionname;
             STR " @ ";
             INT location.line;
             STR ": ";
             STR vinfo.vname])

  method private translate_indirect_deref_call
                   (lhs:lval option)
                   (e:exp)
                   (args:exp list) =
    let default =
      [make_c_cmd
         (OPERATION
            { op_name = new symbol_t ~atts:[p2s (exp_to_pretty e)] "indirect call";
              op_args = [] })] in
    let xpr = exp_translator#translate_exp context e in
    match xpr with
    | XVar v when env#is_memory_address v ->
       let memref = env#get_memory_reference v in
       begin
         match memref#get_base with
         | CGlobalAddress v ->
            let (vinfo, _offset) = env#get_global_variable v in
            begin
              self#set_indirect_call vinfo;
              self#translate_known_call lhs vinfo.vname vinfo.vid args
            end
         | _ ->
            begin
              chlog#add
                "deref call expression"
                (LBLOCK [
                     STR env#get_functionname;
                     STR " @ ";
                     INT location.line;
                     STR ": ";
                     exp_to_pretty e]);
              default
            end
       end
    | _ ->
       begin
         chlog#add
           "deref call expression"
           (LBLOCK [
                STR env#get_functionname;
                STR " @ ";
                INT location.line;
                STR ": ";
                exp_to_pretty e]);
         default
       end

  method private translate_indirect_call
                   (_lhs:lval option)
                   (_f:exp)
                   (_args:exp list) = []

  method private get_external_post_value
                   (postconditions:
                      annotated_xpredicate_t list * annotated_xpredicate_t list)
                   (_args: xpr_t list): xpr_t option =
    let get_external_pc_value (acc: xpr_t option) ((pc, _): annotated_xpredicate_t) =
      match acc with
      | Some _ -> acc
      | _ ->
         match pc with
         | XExternalStateValue (ReturnValue, ExternalState name) ->
            let lhs = env#mk_external_state_variable name NUM_VAR_TYPE in
            orakel#get_external_state_value context lhs
         | _ -> acc in
    match postconditions with
    | ([], _) -> None
    | (pl, _) -> List.fold_left get_external_pc_value None pl

  method private get_arg_post_value
                   (postconditions:
                      annotated_xpredicate_t list * annotated_xpredicate_t list)
                   (args:xpr_t list)
                   (returnvalue:variable_t)
                   (returntype:typ) =
    let rval =
      match postconditions with
      | (l, [])
        | (l, [(XNull _, _)]) ->
         List.fold_left (fun acc (pc, _) ->
             match acc with
             | Some _ -> acc
             | _ ->
                match pc with
                | XRelationalExpr (Eq,ReturnValue,ArgValue(ParFormal n,ArgNoOffset))
                  | XRelationalExpr
                      (Eq,ArgValue(ParFormal n,ArgNoOffset),ReturnValue) ->
                   let tmpProvider = (fun () -> env#mk_num_temp) in
                   let cstProvider =
                     (fun (n: numerical_t) -> env#mk_num_constant n) in
                   let arg = List.nth args (n-1) in
                   Some (xpr2numexpr tmpProvider cstProvider arg)
                | XTainted (ReturnValue, lb, ub) ->
                   let xlb = match lb with
                     | Some (NumConstant n) -> Some (XConst (IntConst n))
                     | _ -> None in
                   let xub = match ub with
                     | Some (NumConstant n) -> Some (XConst (IntConst n))
                     | _ -> None in
                   let cmd = make_c_cmd SKIP in
                   let taintval =
                     env#mk_tainted_value returnvalue xlb xub returntype in
                   Some (cmd, NUM_VAR taintval)
                | _ -> None) None l
      | _ -> None in
    match rval with
    | Some (c, r) -> (c, r)
    | _ ->
       match returntype with
       | TPtr (t,_) ->
          let basevar = env#mk_base_address_value returnvalue NoOffset t in
          (make_c_cmd SKIP, NUM_VAR basevar)
       | _ ->
          (make_c_cmd SKIP, NUM_VAR returnvalue)

  method private get_post_assert
                   (postconditions:annotated_xpredicate_t list * annotated_xpredicate_t list)
                   (fname:string)
                   (_fvid:int)
                   (rvar:variable_t)
                   (args:xpr_t list) =
    let tmpProvider = (fun () -> env#mk_num_temp) in
    let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
    let get_assert x =
      let (code, bExp) = xpr2boolexpr tmpProvider cstProvider x in
      [code; make_c_cmd (make_assert bExp)] in
    let make_post_assert (pc, _) =
      match pc with
      | XNonNegative ReturnValue ->
         get_assert (XOp (XGe, [XVar rvar; int_constant_expr 0]))
      | XRelationalExpr (op,ReturnValue,NumConstant x) ->
         get_assert (XOp (binop_to_xop op, [XVar rvar; num_constant_expr x]))
      | XRelationalExpr (op, NumConstant x, ReturnValue) ->
         get_assert (XOp (binop_to_xop op, [num_constant_expr x; XVar rvar]))
      | XRelationalExpr (Eq,ReturnValue,ArgValue(ParFormal n,ArgNoOffset))
        | XRelationalExpr (Eq,ArgValue(ParFormal n,ArgNoOffset),ReturnValue) ->
         let arg = List.nth args (n-1) in
         let (code, x) = xpr2numexpr tmpProvider cstProvider arg in
         [code; make_c_cmd (ASSIGN_NUM (rvar, x))]
      | XRelationalExpr (op,ReturnValue,ArgValue(ParFormal n,ArgNoOffset)) ->
         let arg = List.nth args (n-1) in
         get_assert (XOp (binop_to_xop op, [XVar rvar; arg]))
      | XRelationalExpr (op,ArgValue(ParFormal n,ArgNoOffset),ReturnValue) ->
         let arg = List.nth args (n-1) in
         get_assert (XOp (binop_to_xop op, [arg; XVar rvar]))
      | XRelationalExpr (Lt, ReturnValue,
                         ByteSize(ArgValue(ParFormal n, ArgNoOffset))) ->
         let arg = List.nth args (n-1) in
         let msg =
           LBLOCK [
               STR env#get_functionname;
               STR " : ";
               STR fname;
               STR ": less-than-size : ";
               pr_expr arg] in
         begin
           match arg with
           | XVar v when env#is_memory_address v ->
              let memref = env#get_memory_reference v in
              begin
                match memref#get_base with
                | CStackAddress stackvar when env#is_local_variable stackvar ->
                   let (vinfo, offset) = env#get_local_variable stackvar in
                   begin
                     match (vinfo.vtype,offset) with
                     | (TArray (_, Some len, _), NoOffset) ->
                        let b = exp_translator#translate_exp context len in
                        get_assert (XOp (XLt, [XVar rvar; b]))
                     | _ -> []
                   end
                | _ ->
                   begin
                     chlog#add "unused scalar postconditions" msg;
                     []
                   end
              end
           | _ ->
              begin
                chlog#add "unused scalar postconditions" msg;
                []
              end
         end
      | _ ->
         begin
           chlog#add
             "unused scalar postconditions"
             (LBLOCK [
                  STR env#get_functionname;
                  STR " : ";
                  STR fname;
                  STR ": ";
                  STR (xpredicate_tag pc)]);
           []
         end in
    let make l = List.concat (List.map make_post_assert l) in
    match postconditions with
    | ([], []) -> make_c_nop ()
    | (pl, []) -> make_c_cmd_block (make pl)
    | (pl, el) -> make_c_branch [make pl; make el]

  method private get_postconditions
                   (fname:string):
                   (annotated_xpredicate_t list * annotated_xpredicate_t list) =
    get_postconditions env#get_functionname (Some fname) context

  method private get_sideeffects
                   (fname:string)
                   (fvid:int)
                   (fnargs:exp list)
                   (fnxargs: (xpr_t option) list) =
    let rec compose_offset base offset =
      match base with
      | NoOffset -> offset
      | Field (fuse, NoOffset) ->  Field (fuse,offset)
      | Field (fuse, foffset) -> Field (fuse, compose_offset foffset offset)
      | Index _ ->
         begin
           ch_error_log#add
             "compose offset"
             (LBLOCK [
                  STR "base: ";
                  offset_to_pretty base;
                  STR "; offset: ";
                  offset_to_pretty offset]);
           NoOffset
         end in
    let rec assign_se_struct arg baseoffset comp rhs =
      List.fold_left (fun acc f ->
          let foffset = Field ((f.fname,f.fckey), NoOffset)  in
          let offset = compose_offset baseoffset foffset in
          let lhs = exp_translator#translate_lhs context (Mem arg,offset) in
          let assign = make_c_cmd (ASSIGN_NUM (lhs, NUM_VAR rhs)) in
          let subassigns =
            match fenv#get_type_unrolled f.ftype with
            | TComp (ckey, _) ->
               let comp = fenv#get_comp ckey in
               assign_se_struct arg offset comp rhs
            | _ -> []  in
          (assign :: subassigns) @ acc) [] comp.cfields in

    match get_sideeffects env#get_functionname (Some fname) context with
    | [] ->
       let argabstracts =
         List.fold_left (fun acc arg ->
             match arg with
             | AddrOf lval | StartOf lval ->
                let v = exp_translator#translate_lhs context lval in
                let _ =
                  log_diagnostics_result
                    ~tag:"abstract memory variables"
                    ~msg:env#get_functionname
                    __FILE__ __LINE__
                    [p2s v#toPretty] in
                (make_c_cmd (ABSTRACT_VARS [v])) :: acc
             | _ -> acc) [] fnargs in
       make_c_cmd_block argabstracts
    | l ->
       let assignments =
         List.fold_left (fun acc (se, _) ->
             match se with
             | XBlockWrite (ArgValue (ParFormal n, ArgNoOffset), _) ->
                let vinfo = fdecls#get_varinfo_by_vid fvid in
                let arg = List.nth fnargs (n - 1) in
                let lhs =
                  exp_translator#translate_lhs context (Mem arg,NoOffset) in
                if lhs#isTmp then
                  let memoryvars = env#get_memory_variables in
                  let _ =
                    log_diagnostics_result
                      ~tag:"abstract memory variables"
                      ~msg:env#get_functionname
                      __FILE__ __LINE__
                      (List.map (fun v -> p2s v#toPretty) memoryvars) in
                  [CCMD (ABSTRACT_VARS memoryvars)]
                else
                  let ty = fenv#get_type_unrolled (env#get_variable_type lhs) in
                  let sevar =
                    env#mk_function_sideeffect_value
                      location context vinfo fnxargs n ty in
                  let bwvar = env#mk_byte_sequence sevar None in
                  let assign = make_c_cmd  (ASSIGN_NUM (lhs, NUM_VAR bwvar)) in
                  let subassigns =
                    match ty with
                    | TComp (ckey,_) ->
                       let comp = fenv#get_comp ckey in
                       assign_se_struct arg NoOffset comp bwvar
                    | _ ->
                       [] in
                  assign :: subassigns

             | XInitializesExternalState (ExternalState name,
                                          ArgValue (ParFormal n, ArgNoOffset)) ->
                let arg = List.nth fnargs (n - 1) in
                let assigns =
                  match arg with
                  | CastE (_, Const (CInt (i64, _, _)))
                       when (Int64.compare i64 Int64.zero) = 0 -> []
                  | _ ->
                     let xarg = exp_translator#translate_exp context arg in
                     let lhs = env#mk_external_state_variable name NUM_VAR_TYPE in
                     match xarg with
                     | XVar v -> [make_c_cmd (ASSIGN_NUM (lhs, NUM_VAR v))]
                     | _ -> [] in
                assigns

             | XFormattedInput (ArgValue (ParFormal n,ArgNoOffset)) ->
                let (assignments,_) =
                  List.fold_left (fun (acc, i) arg ->
                      let vinfo = fdecls#get_varinfo_by_vid fvid in
                      let argty = type_of_exp fdecls arg in
                      let ty = match fenv#get_type_unrolled argty  with
                        | TPtr (t, _) -> t
                        | t ->
                           begin
                             ch_error_log#add
                               "input format argument"
                               (LBLOCK [
                                    STR "Unexpected type for argument ";
                                    INT i;
                                    STR ": ";
                                    typ_to_pretty t]);
                             TInt (IInt, [])
                           end in
                      let sevar =
                        env#mk_function_sideeffect_value
                          location context vinfo fnxargs i ty in
                      let (xoptlb,xoptub) =
                        match ty with
                        | TInt (ik, []) ->
                           (Some (num_constant_expr (get_safe_lowerbound ik)),
                            Some (num_constant_expr (get_safe_upperbound ik)))
                        | _ -> (None,None) in
                      let taintedvar =
                        env#mk_tainted_value sevar xoptlb xoptub ty in
                      match arg with
                      | AddrOf lval | StartOf lval ->
                         let v = exp_translator#translate_lhs context lval in
                         let assign = ASSIGN_NUM (v, NUM_VAR taintedvar) in
                         ((make_c_cmd assign) :: acc,i+1)
                      | _ ->
                         let v = exp_translator#translate_exp context arg in
                         match v with
                         | XVar v ->
                            if env#is_memory_address v then
                              let memaddress = env#get_memory_reference v in
                              if memaddress#is_stack_reference then
                                let stackvar = memaddress#get_stack_address_var in
                                let assign =
                                  ASSIGN_NUM (stackvar, NUM_VAR taintedvar) in
                                ((make_c_cmd assign) :: acc, i+1)
                              else if memaddress#is_global_reference then
                                let globalvar = memaddress#get_global_address_var in
                                let assign =
                                  ASSIGN_NUM (globalvar, NUM_VAR taintedvar) in
                                ((make_c_cmd assign) :: acc, i+1)
                              else
                                (acc, i+1)
                            else
                              (acc, i+1)
                         | _ -> (acc, i+1)) ([], n) fnargs in
                assignments @ acc
             | _ -> acc) [] l in
       make_c_cmd_block assignments

end


class valueset_call_translator_t
        (env:c_environment_int)
        (orakel:orakel_int)
        (exp_translator:exp_translator_int):call_translator_int =
object (self)

  val mutable context = mk_program_context ()
  val fdecls = env#get_fdecls
  val mutable location = unknown_location

  method translate
           (ctxt:program_context_int)
           (loc:location)
           (lhs:lval option)
           (f:exp)
           (args:exp list) =
    let _ = context <- ctxt in
    let _ = location <- loc in
    try
      match f with
      | Lval (Var (fname, fvid), NoOffset) ->     (* direct call *)
         if call_does_not_return env#get_functionname (Some fname) context then
           let _ =
             chlog#add
               "call does not return (valuesets)"
               (LBLOCK [STR env#get_functionname; STR ": "; STR fname]) in
           [make_c_cmd (ASSERT FALSE)]
         else
           let vinfo = fdecls#get_varinfo_by_vid fvid in
           let fnargs = List.map (exp_translator#translate_exp ctxt) args in
           let fnxargs = List.map (orakel#get_external_value ctxt) fnargs in
           let callop =
             make_c_cmd
               (OPERATION
                  { op_name = new symbol_t ~atts:[fname] "call";
                    op_args = [] }) in
           let returntype =
             match fenv#get_type_unrolled vinfo.vtype with
             | TFun (ty, _, _, _) -> ty
             | _ ->
                raise
                  (CCHFailure
                     (LBLOCK [
                          STR "Unexpected type for function variable: ";
                          STR fname;
                          STR ": ";
                          typ_to_pretty vinfo.vtype])) in
           let rcode =
             match lhs with
             | None -> []
             | Some lval ->
                let postconditions = self#get_postconditions fname in
                let frVar =
                  env#mk_function_return_value loc context vinfo fnxargs in
                let rvar = exp_translator#translate_lhs ctxt lval in
                if rvar#isTmp then
                  let memoryvars = env#get_memory_variables in
                  let _ =
                    log_diagnostics_result
                      ~tag:"abstract memory variables"
                      ~msg:env#get_functionname
                      __FILE__ __LINE__
                      (List.map (fun v -> p2s v#toPretty) memoryvars) in
                  [make_c_cmd (ABSTRACT_VARS memoryvars)]
                else
                  let ty = fenv#get_type_unrolled (env#get_variable_type rvar) in
                  match ty with
                  | TComp _ ->
                     let memoryvars = env#get_memory_variables_with_base rvar in
                     let _ =
                       log_diagnostics_result
                         ~tag:"abstract memory variables"
                         ~msg:env#get_functionname
                         __FILE__ __LINE__
                         (List.map (fun v -> p2s v#toPretty) memoryvars) in
                     [make_c_cmd (ABSTRACT_VARS memoryvars)]
                  | _  ->
                     let (rcode, rval) =
                       self#get_arg_post_value
                         postconditions fnargs frVar returntype in
                     let assign = make_c_cmd (ASSIGN_NUM (rvar, rval)) in
                     let postassert =
                       self#get_post_assert
                         postconditions fname fvid rvar fnargs in
                     let domainop =
                       match type_of_lval fdecls lval with
                       | TPtr (t,_) ->
                          let frVar = env#mk_base_address_value frVar NoOffset t in
                          make_c_cmd
                            (DOMAIN_OPERATION (
                                 [valueset_domain],
                                 { op_name = new symbol_t "initialize_with_null";
                                   op_args = [(frVar#getName#getBaseName,
                                               frVar,
                                               READ)]}))
                       | _ -> make_c_nop () in
                     [rcode;  domainop; assign; postassert] in
           let sideeffects = self#get_sideeffects fname fvid args fnxargs in
           [callop] @ [sideeffects] @ rcode
      | _ ->
         let callop =
           make_c_cmd
             (OPERATION
                { op_name = new symbol_t ~atts:[p2s (exp_to_pretty f)]
                              "indirect call";
                  op_args = [] }) in
         [callop]
    with
    | CCHFailure p ->
       raise
         (CCHFailure
	    (LBLOCK [
                 STR "Error in translating call: ";
                 exp_to_pretty f;
		 STR " with arguments ";
		 pretty_print_list args exp_to_pretty "(" "," ")";
		 (match lhs with
                  | Some lval ->
		     LBLOCK [
                         STR " and return value ";
			 lval_to_pretty lval]
                  | _ -> STR "");
                 STR ": ";
                 p]))

  method private get_arg_post_value
                   (postconditions:
                      annotated_xpredicate_t list * annotated_xpredicate_t list)
                   (args:xpr_t list)
                   (returnvalue:variable_t)
                   (returntype:typ) =
    let rval =
      match postconditions with
      | (l, []) ->
         List.fold_left (fun acc (pc, _) ->
             match acc with
             | Some _ -> acc
             | _ ->
                match pc with
                | XRelationalExpr
                  (Eq, ReturnValue, ArgValue(ParFormal n,ArgNoOffset))
                  | XRelationalExpr
                      (Eq, ArgValue(ParFormal n, ArgNoOffset), ReturnValue) ->
                   let tmpProvider = (fun () -> env#mk_num_temp) in
                   let cstProvider =
                     (fun (n:numerical_t) -> env#mk_num_constant n) in
                   let arg = List.nth args (n-1) in
                   Some (xpr2numexpr tmpProvider cstProvider arg)
                | XTainted (ReturnValue, lb, ub) ->
                   let xlb = match lb with
                     | Some (NumConstant n) -> Some (XConst (IntConst n))
                     | _ -> None in
                   let xub = match ub with
                     | Some (NumConstant n) -> Some (XConst (IntConst n))
                     | _ -> None in
                   let cmd = make_c_cmd SKIP in
                   let taintval =
                     env#mk_tainted_value returnvalue xlb xub returntype in
                   Some (cmd, NUM_VAR taintval)
                | _ -> None) None l
      | _ -> None in
    match rval with
    | Some (c, r) -> (c, r)
    | _ ->
       match returntype with
       | TPtr  (t, _) ->
          let basevar = env#mk_base_address_value returnvalue NoOffset t in
          (make_c_cmd SKIP, NUM_VAR basevar)
       | _ ->
          (make_c_cmd SKIP, NUM_VAR  returnvalue)

  method private get_post_assert
                   (postconditions:
                      annotated_xpredicate_t list * annotated_xpredicate_t list)
                   (fname:string)
                   (_fvid:int)
                   (rvar:variable_t)
                   (args:xpr_t list) =
    let tmpProvider = (fun () -> env#mk_num_temp) in
    let cstProvider = (fun (n:numerical_t) -> env#mk_num_constant n) in
    let get_assert x =
      let (code, bExp) = xpr2boolexpr tmpProvider cstProvider x in
      [code; make_c_cmd (make_assert bExp)] in
    let make_post_assert (pc,_) =
      match pc with
      | XNonNegative ReturnValue ->
         get_assert (XOp (XGe, [XVar rvar; int_constant_expr 0]))
      | XRelationalExpr (op,ReturnValue,NumConstant x) ->
         get_assert (XOp (binop_to_xop op, [XVar rvar; num_constant_expr x]))
      | XRelationalExpr (op, NumConstant x, ReturnValue) ->
         get_assert (XOp (binop_to_xop op, [num_constant_expr x; XVar rvar]))
      | XRelationalExpr (Eq,ReturnValue,ArgValue(ParFormal n,ArgNoOffset))
        | XRelationalExpr (Eq,ArgValue(ParFormal n,ArgNoOffset),ReturnValue) ->
         let arg = List.nth args (n-1) in
         let (code,x) = xpr2numexpr tmpProvider cstProvider arg in
         [code; make_c_cmd (ASSIGN_NUM (rvar, x))]
      | XRelationalExpr (op,ReturnValue,ArgValue(ParFormal n,ArgNoOffset)) ->
         let arg = List.nth args (n-1) in
         get_assert (XOp (binop_to_xop op, [XVar rvar; arg]))
      | XRelationalExpr (op,ArgValue(ParFormal n,ArgNoOffset),ReturnValue) ->
         let arg = List.nth args (n-1) in
         get_assert (XOp (binop_to_xop op, [arg; XVar rvar]))
      | XRelationalExpr (Lt,
                         ReturnValue,
                         ByteSize(ArgValue(ParFormal n,ArgNoOffset))) ->
         let arg = List.nth args (n-1) in
         let msg =
           LBLOCK [
               STR env#get_functionname;
               STR " : ";
               STR fname;
               STR ": less-than-size : ";
               pr_expr arg] in
         begin
           match arg with
           | XVar v when env#is_memory_address v ->
              let memref = env#get_memory_reference v in
              begin
                match memref#get_base with
                | CStackAddress stackvar when env#is_local_variable stackvar ->
                   let (vinfo,offset) = env#get_local_variable stackvar in
                   begin
                     match (vinfo.vtype, offset) with
                     | (TArray (_, Some len, _), NoOffset) ->
                        let b = exp_translator#translate_exp context len in
                        get_assert (XOp (XLt, [XVar rvar; b]))
                     | _ -> []
                   end
                | _ ->
                   begin
                     chlog#add "unused scalar postconditions" msg;
                     []
                   end
              end
           | _ ->
              begin
                chlog#add "unused scalar postconditions" msg;
                []
              end
         end
      | _ ->
         begin
           chlog#add
             "unused scalar postconditions"
             (LBLOCK [
                  STR env#get_functionname;
                  STR " : ";
                  STR fname;
                  STR ": ";
                  STR (xpredicate_tag pc)]);
           []
         end in
    let make l = List.concat (List.map make_post_assert l) in
    match postconditions with
    | ([], []) -> make_c_nop ()
    | (pl, []) -> make_c_cmd_block (make pl)
    | (pl, el) -> make_c_branch [make pl; make el]

  method private get_postconditions (fname:string) =
    get_postconditions env#get_functionname (Some fname) context

  method private get_sideeffects
                   (fname:string)
                   (fvid:int)
                   (fnargs:exp list)
                   (fnxargs: (xpr_t option) list) =
    let rec compose_offset base offset =
      match base with
      | NoOffset -> offset
      | Field (fuse, NoOffset) -> Field (fuse,offset)
      | Field (fuse, foffset) -> Field (fuse, compose_offset foffset offset)
      | Index _ ->
         begin
           ch_error_log#add
             "compose offset"
             (LBLOCK [
                  STR "base: ";
                  offset_to_pretty base;
                  STR "; offset: ";
                  offset_to_pretty offset]);
           NoOffset
         end in
    let rec assign_se_struct arg baseoffset comp rhs =
      List.fold_left (fun acc f ->
          let foffset = Field ((f.fname, f. fckey), NoOffset)  in
          let offset = compose_offset baseoffset foffset in
          let lhs = exp_translator#translate_lhs context (Mem arg, offset) in
          let assign = make_c_cmd  (ASSIGN_NUM (lhs, NUM_VAR rhs)) in
          let subassigns =
            match fenv#get_type_unrolled f.ftype with
            | TComp (ckey, _) ->
               let comp = fenv#get_comp ckey in
               assign_se_struct arg offset comp rhs
            | _ -> []  in
          (assign :: subassigns) @ acc) [] comp.cfields in

    match get_sideeffects env#get_functionname (Some fname) context with
    | [] ->
       let argabstracts =
         List.fold_left (fun acc arg ->
             match arg with
             | AddrOf lval | StartOf lval ->
                let v = exp_translator#translate_lhs context lval in
                let _ =
                  log_diagnostics_result
                    ~tag:"abstract memory variables"
                    ~msg:env#get_functionname
                    __FILE__ __LINE__
                    [p2s v#toPretty] in
                (make_c_cmd (ABSTRACT_VARS [v])) :: acc
             | _ -> acc) [] fnargs in
       make_c_cmd_block argabstracts
    | l ->
       let assignments =
         List.fold_left (fun acc (se, _) ->
             match se with
             | XBlockWrite (ArgValue (ParFormal n,ArgNoOffset), _) ->
                let vinfo = fdecls#get_varinfo_by_vid fvid in
                let arg = List.nth fnargs (n - 1) in
                let lhs =
                  exp_translator#translate_lhs context (Mem arg,NoOffset) in
                if lhs#isTmp then
                  let memoryvars = env#get_memory_variables in
                  let _ =
                    log_diagnostics_result
                      ~tag:"abstract memory variables"
                      ~msg:env#get_functionname
                      __FILE__ __LINE__
                      (List.map (fun v -> p2s v#toPretty) memoryvars) in
                  [CCMD (ABSTRACT_VARS memoryvars)]
                else
                  let ty = fenv#get_type_unrolled (env#get_variable_type lhs) in
                  let sevar =
                    env#mk_function_sideeffect_value
                      location context vinfo fnxargs n ty in
                  let bwvar = env#mk_byte_sequence sevar None in
                  let assign = make_c_cmd  (ASSIGN_NUM (lhs, NUM_VAR bwvar)) in
                  let subassigns =
                    match ty with
                    | TComp (ckey, _) ->
                       let comp = fenv#get_comp ckey in
                       assign_se_struct arg NoOffset comp bwvar
                    | _ ->
                       [] in
                  assign :: subassigns

             | XFormattedInput (ArgValue (ParFormal n, ArgNoOffset)) ->
                let (assignments, _) =
                  List.fold_left (fun (acc, i) arg ->
                      let vinfo = fdecls#get_varinfo_by_vid fvid in
                      let ty =
                        match fenv#get_type_unrolled (type_of_exp fdecls arg) with
                        | TPtr (t, _) -> t
                        | t ->
                           begin
                             ch_error_log#add
                               "input format argument"
                               (LBLOCK [
                                    STR "Unexpected type for argument ";
                                    INT i;
                                    STR ": ";
                                    typ_to_pretty t]);
                             TInt (IInt, [])
                           end in
                      let sevar =
                        env#mk_function_sideeffect_value
                          location context vinfo fnxargs i ty in
                      let (xoptlb, xoptub) =
                        match ty with
                        | TInt (ik,[]) ->
                           (Some (num_constant_expr (get_safe_lowerbound ik)),
                            Some (num_constant_expr (get_safe_upperbound ik)))
                        | _ -> (None,None) in
                      let taintedvar =
                        env#mk_tainted_value sevar xoptlb xoptub ty in
                      match arg with
                      | AddrOf lval | StartOf lval ->
                         let v = exp_translator#translate_lhs context lval in
                         let assign = ASSIGN_NUM (v, NUM_VAR taintedvar) in
                         ((make_c_cmd assign) :: acc,i+1)
                      | _ ->
                         let v = exp_translator#translate_exp context arg in
                         match v with
                         | XVar v ->
                            if env#is_memory_address v then
                              let memaddress = env#get_memory_reference v in
                              if memaddress#is_stack_reference then
                                let stackvar = memaddress#get_stack_address_var in
                                let assign =
                                  ASSIGN_NUM (stackvar, NUM_VAR taintedvar) in
                                ((make_c_cmd assign) :: acc, i+1)
                              else if memaddress#is_global_reference then
                                let globalvar =
                                  memaddress#get_global_address_var in
                                let assign =
                                  ASSIGN_NUM (globalvar, NUM_VAR taintedvar) in
                                ((make_c_cmd assign) :: acc, i+1)
                              else
                                (acc, i+1)
                            else
                              (acc, i+1)
                         | _ -> (acc, i+1)) ([], n) fnargs in
                assignments @ acc
             | _ -> acc) [] l in
       make_c_cmd_block assignments

end


(* --------------------------------------------------------------------------
   The symbolic call translator creates semantics for three conditions:
   - initialization of variables

   1. Initialization

   Variables can be set to initialized by the call translator in two ways:
   a) by assignment to the return value: x = f(..), in which case x is
      assigned the symbol assignedAt@<line>, similar to regular assignment
   b) by side effect to a passed pointer variable: f(x), in which case
      *x is assigned the symbol assignedAt@<line>@by<f>.
      Assignment by side effect is derived from the function summary of f
   -------------------------------------------------------------------------- *)

class sym_call_translator_t
        (env:c_environment_int)
        (_orakel:orakel_int)
        (exp_translator:exp_translator_int):call_translator_int =
object (self)

  val mutable context = mk_program_context ()
  val fdecls = env#get_fdecls
  val mutable location = unknown_location

  method translate
           (ctxt:program_context_int)
           (loc:location)
           (lhs:lval option)
           (f:exp)
           (args:exp list) =
    let _ = context <- ctxt in
    let _ = location <- loc in
    match f with
    | Lval (Var (fname,fvid), NoOffset) ->                (* direct call *)
       let fnargs = List.map (exp_translator#translate_exp ctxt) args in
       let sideeffect = self#get_sideeffect fname fvid args fnargs in
       let postconditions = self#get_postconditions fname args fnargs in
       let callop =
         make_c_cmd
           (OPERATION
              { op_name = new symbol_t ~atts:[fname] "call";
                op_args = [] }) in
       let rcode =
         match lhs with
         | None -> []
         | Some lval ->
            let rvar = exp_translator#translate_lhs context lval in
            if rvar#isTmp then
              let memoryvars = env#get_memory_variables in
              let _ =
                log_diagnostics_result
                  ~tag:"abstract memory variables"
                  ~msg:env#get_functionname
                  __FILE__ __LINE__
                  (List.map (fun v -> p2s v#toPretty) memoryvars) in
              [make_c_cmd (ABSTRACT_VARS memoryvars)]
            else
              let ty = fenv#get_type_unrolled (env#get_variable_type rvar)  in
              match ty with
              | TComp _ ->
                 let memoryvars = env#get_memory_variables_with_base rvar in
                 let _ =
                   log_diagnostics_result
                     ~tag:"abstract memory variables"
                     ~msg:env#get_functionname
                     __FILE__ __LINE__
                     (List.map (fun v -> p2s v#toPretty) memoryvars) in
                 [make_c_cmd (ABSTRACT_VARS memoryvars)]
              | _ ->
                  let atts = ["rv:"; fname] in
                  let sym =
                    new symbol_t ~atts ("assignedAt#" ^ (string_of_int loc.line)) in
                  [make_c_cmd (ASSIGN_SYM (rvar, SYM sym))] in
       callop :: (sideeffect @ postconditions @ rcode)
    | _ ->                                             (* indirect call *)
       let callop =
         make_c_cmd
           (OPERATION
              { op_name =
                  new symbol_t ~atts:[p2s (exp_to_pretty f)] "indirect call";
                op_args = [] }) in
       let rcode =
         match lhs with
         | None -> []
         | Some lval ->
            let rvar = exp_translator#translate_lhs context lval in
            let atts = ["indirect-call-rv:"; p2s (exp_to_pretty f)] in
            let sym =
              new symbol_t ~atts ("assignedAt#" ^ (string_of_int loc.line)) in
            [make_c_cmd (ASSIGN_SYM (rvar, SYM sym))] in
       callop :: rcode

  method private get_postconditions
                   (fname:string) (args:exp list) (_fnargs:xpr_t list) =
    let (pcs, _epcs) =
      get_postconditions env#get_functionname (Some fname) context in
    List.concat
      (List.map (fun (pc, _) ->
           match pc with
           | XInitializedRange (base, len) ->
              let basevar =
                match base with
                | ArgValue (ParFormal n, ArgNoOffset) ->
                   let arg = List.nth args (n-1) in
                   begin
                     match arg with
                     |CastE (_, StartOf (Var (_vname, vid), offset))
                      | CastE (_, AddrOf (Var (_vname, vid), offset)) ->
                        let vinfo = env#get_varinfo vid in
                        Some (env#mk_program_var vinfo offset SYM_VAR_TYPE)
                     | CastE (_, Lval (Var (_vname, vid), offset)) ->
                        let vinfo = env#get_varinfo vid in
                        Some (env#mk_program_var vinfo offset SYM_VAR_TYPE)
                     | _ -> None
                   end
                | _ -> None in
              let lenvalue =
                match len with
                | ArgValue (ParFormal n, ArgNoOffset) ->
                   let arg = List.nth args (n-1) in
                   begin
                     match arg with
                     | Const (CInt (i64,_,_))
                       | CastE (_, Const (CInt (i64, _, _))) ->
                        Some (mkNumericalFromString (Int64.to_string i64))
                     | _ -> None
                   end
                | NumConstant n -> Some n
                | _ -> None in
              begin
                match (basevar,lenvalue) with
                | (Some v, Some l) ->
                   [make_c_cmd
                      (ASSIGN_SYM (v, SYM (new symbol_t ~atts:[fname; l#toString]
                                             "initialized-range")))]
                | _ -> []
              end
           | _ -> []) pcs)

  method private get_freed_exp_indices args sideeffects=
    List.fold_left (fun acc (se, _) ->
        match acc with
        | None -> None
        | _ ->
           match se with
           | XPreservesAllMemoryX l ->
              let args =
                List.map (fun t ->
                    match t with
                    | ArgValue (ParFormal n,ArgNoOffset) ->
                       Some (List.nth args (n-1))
                    | _ -> None) l in
              if List.for_all
                   (fun a -> match a with Some _ -> true | _ -> false) args then
                Some (List.map (fun a ->
                    match a with
                    | Some a -> cd#index_exp a
                    | _ -> raise (CCHFailure (STR "Internal error"))) args)
              else
                None
           | _ -> acc) (Some []) sideeffects

  method private get_sideeffect
                   (fname:string)
                   (fvid:int)
                   (args:exp list)
                   (fnargs:xpr_t list) =
    let vinfo = fdecls#get_varinfo_by_vid fvid in
    let sideeffects = get_sideeffects env#get_functionname (Some fname) context in
    let (sitevars,xsitevars) = env#get_site_call_vars context in
    let fnzargs = List.map (fun _ -> None) fnargs in
    let zsevar =
      env#mk_function_sideeffect_value
        location context vinfo fnzargs 0 (TVoid []) in
    let xexpindices = self#get_freed_exp_indices args sideeffects in
    let xexpindices = match xexpindices with Some l -> l | _ -> [] in
    let sitesym =
      new symbol_t
        ~atts:((string_of_int location.line)
               :: (List.map string_of_int xexpindices))
        ~seqnr:zsevar#getName#getSeqNumber fname in
    let entrysym = env#get_p_entry_sym in
    let sitevarassigns =
      make_c_cmd_block (List.map (fun sitevar ->
          make_c_cmd (ASSIGN_SYM (sitevar, SYM entrysym))) sitevars) in
    let xsitevarassigns =
      make_c_branch
        ([(List.map (fun xsitevar ->
               make_c_cmd (ASSIGN_SYM (xsitevar, SYM sitesym))) xsitevars)]
         @ [[make_c_cmd SKIP]]) in
    let rec compose_offset base offset =
      match base with
      | NoOffset -> offset
      | Field (fuse, NoOffset) -> Field (fuse,offset)
      | Field (fuse, foffset) -> Field (fuse, compose_offset foffset offset)
      | Index _ ->
         begin
           ch_error_log#add
             "compose offset"
             (LBLOCK [
                  STR "base: ";
                  offset_to_pretty base;
                  STR "; offset: ";
                  offset_to_pretty offset]);
           NoOffset
         end in
    let rec cancel_se_struct arg baseoffset comp  =
      List.fold_left (fun acc f ->
          let foffset = Field ((f.fname,f.fckey),NoOffset)  in
          let offset = compose_offset baseoffset foffset in
          let lhs = exp_translator#translate_lhs context (Mem arg,offset) in
          if lhs#isTmp then
            let memoryvars = env#get_memory_variables in
            let _ =
              log_diagnostics_result
                ~tag:"abstract memory variables"
                ~msg:env#get_functionname
                __FILE__ __LINE__
                (List.map (fun v -> p2s v#toPretty) memoryvars) in
            [ make_c_cmd (ABSTRACT_VARS memoryvars)]
          else
            let cancel = make_c_cmd (ABSTRACT_VARS [lhs]) in
            let _ =
              log_diagnostics_result
                ~tag:"abstract memory variables"
                ~msg:env#get_functionname
                __FILE__ __LINE__
                [p2s lhs#toPretty] in
            let subcancels =
              match fenv#get_type_unrolled f.ftype with
              | TComp (ckey,_) ->
                 let comp = fenv#get_comp ckey in
                 cancel_se_struct arg offset comp
              | _ -> []  in
            (cancel :: subcancels) @ acc) [] comp.cfields in
    let seeffects =
    List.concat
      (List.map (fun (se,_) ->
           match se with
           | XBlockWrite (ArgValue (ParFormal n, ArgNoOffset), _) ->
              let arg = List.nth args (n - 1) in
              let lhs = exp_translator#translate_lhs context (Mem arg,NoOffset) in
              if lhs#isTmp  then
                let memoryvars = env#get_memory_variables in
                let _ =
                  log_diagnostics_result
                    ~tag:"abstract memory variables"
                    ~msg:env#get_functionname
                    __FILE__ __LINE__
                    (List.map (fun v -> p2s v#toPretty) memoryvars) in
                [make_c_cmd (ABSTRACT_VARS memoryvars)]
              else
                let ty = fenv#get_type_unrolled (env#get_variable_type lhs)  in
                let cancel = make_c_cmd  (ABSTRACT_VARS [lhs]) in
                let _ =
                  log_diagnostics_result
                    ~tag:"abstract memory variables"
                    ~msg:env#get_functionname
                    __FILE__ __LINE__
                    [p2s lhs#toPretty] in
                let subcancels =
                  match ty with
                  | TComp (ckey, _) ->
                     let comp = fenv#get_comp ckey in
                     cancel_se_struct arg NoOffset comp
                  | _ ->
                     [] in
                cancel :: subcancels

           | XFormattedInput (ArgValue (ParFormal n, ArgNoOffset)) ->
              let (assignments, _) =
                List.fold_left (fun (acc, i) arg ->
                    match arg with
                    | AddrOf lval | StartOf lval ->
                       let v = exp_translator#translate_lhs context lval in
                       let sym =
                         new symbol_t
                           ("assignedAt#" ^ (string_of_int location.line)) in
                       let assign = ASSIGN_SYM (v, SYM sym) in
                       ((make_c_cmd assign) :: acc, i+1)
                    | _ ->
                       let v = exp_translator#translate_exp context arg in
                       match v with
                       | XVar v ->
                          if env#is_memory_address v then
                            let memaddress = env#get_memory_reference v in
                            if memaddress#is_stack_reference then
                              let stackvar = memaddress#get_stack_address_var in
                              let sym =
                                new symbol_t
                                  ("assignedAt#" ^ (string_of_int location.line)) in
                              let assign = ASSIGN_SYM (stackvar, SYM sym) in
                              ((make_c_cmd assign) :: acc, i+1)
                            else if memaddress#is_global_reference then
                              let globalvar = memaddress#get_global_address_var in
                              let sym =
                                new symbol_t
                                  ("assignedAt#" ^ (string_of_int location.line)) in
                              let assign = ASSIGN_SYM (globalvar, SYM sym) in
                              ((make_c_cmd assign) :: acc, i+1)
                            else
                              (acc, i+1)
                          else
                            (acc, i+1)
                       | _ ->  (acc, i+1)) ([], n) args in
              assignments
           | XInitialized (ArgAddressedValue (
                               ArgValue (ParFormal n, ArgNoOffset),
                               ArgFieldOffset (s, ArgNoOffset))) ->
              let arg = List.nth args (n-1) in
              begin
                match arg with
                | AddrOf (Var (_vname, vid), NoOffset)
                  | CastE (_, AddrOf (Var (_vname,vid),NoOffset)) ->
                   let vinfo = fdecls#get_varinfo_by_vid vid in
                   begin
                     match vinfo.vtype with
                     | TComp (ckey,_) ->
                        let v =
                          env#mk_program_var
                            vinfo (Field ((s,ckey),NoOffset)) SYM_VAR_TYPE in
                        let atts = ["se:"; fname] in
                        let sym =
                          new symbol_t
                            ~atts ("assignedAt#" ^ (string_of_int location.line)) in
                        [make_c_cmd (ASSIGN_SYM (v, SYM sym))]
                     | _ -> []
                   end
                | _ -> []
              end
           | XInitializedRange (base, len) ->
              let basevar =
                match base with
                | ArgValue (ParFormal n, ArgNoOffset) ->
                   let arg = List.nth args (n-1) in
                   begin
                     match arg with
                     | CastE (_, StartOf (Var (_vname, vid), offset)) ->
                        let vinfo = env#get_varinfo vid in
                        Some (env#mk_program_var vinfo offset SYM_VAR_TYPE)
                     | CastE (_, Lval (Var (_vname,vid), offset)) ->
                        let vinfo = env#get_varinfo vid in
                        Some (env#mk_program_var vinfo offset SYM_VAR_TYPE)
                     | _ -> None
                   end
                | _ -> None in
              let lenvalue =
                match len with
                | ArgValue (ParFormal n, ArgNoOffset) ->
                   let arg = List.nth args (n-1) in
                   begin
                     match arg with
                     | Const (CInt (i64,_,_))
                       | CastE (_, Const (CInt (i64, _, _))) ->
                        Some (Int64.to_int i64)
                     | _ -> None
                   end
                | _ -> None in
              begin
                match (basevar,lenvalue) with
                | (Some v, Some l) ->
                   [make_c_cmd
                      (ASSIGN_SYM (
                           v,
                           SYM (new symbol_t
                                  ~atts:[fname; string_of_int l]
                                  "initialized-range")))]
                | _ -> []
              end
           | _ -> []) sideeffects) in
    sitevarassigns :: xsitevarassigns :: seeffects

end


class sym_pointersets_call_translator_t
        (env:c_environment_int)
        (orakel:orakel_int)
        (exp_translator:exp_translator_int):call_translator_int =
object (self)

  val mutable context = mk_program_context ()
  val fdecls = env#get_fdecls
  val mutable location = unknown_location
  val memregmgr = env#get_variable_manager#memregmgr

  method translate
           (ctxt:program_context_int)
           (loc:location)
           (lhs:lval option)
           (f:exp)
           (args:exp list) =
    let _ = context <- ctxt in
    let _ = location <- loc in
    try
      match f with
      | Lval (Var (fname,fvid), NoOffset) ->          (* direct call *)
         let fnargs = List.map (exp_translator#translate_exp ctxt) args in
         let sideeffects = self#get_sideeffects fname loc fvid args in
         let callop =
           make_c_cmd
             (OPERATION
                { op_name = new symbol_t ~atts:[fname] "call";
                  op_args = [] }) in
         if call_does_not_return env#get_functionname (Some fname) context  then
           let _ =
             chlog#add
               "call does not return"
               (LBLOCK [STR env#get_functionname; STR ": "; STR fname]) in
           [make_c_cmd (ASSERT FALSE)]
         else
           let rcode = match lhs with
             | None -> []
             | Some lval ->
                match type_of_lval fdecls lval with
                | TPtr _ ->
                   let rvar = exp_translator#translate_lhs context lval in
                   self#get_post_assigns fname fvid rvar fnargs
                | _ -> [] in
           (callop :: rcode) @ sideeffects
      | _ ->                                         (* indirect call *)
         let callop =
           make_c_cmd
             (OPERATION
                { op_name = new symbol_t ~atts:[p2s (exp_to_pretty f)]
                              "indirect call";
                  op_args = [] }) in
         [callop]
    with
    | CCHFailure p ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Error in translating call: ";
                 exp_to_pretty f;
                 STR ": ";
                 p]))

  method private get_post_assigns
                   (fname:string)
                   (fvid:int)
                   (rvar:variable_t)
                   (args:xpr_t list) =
    let vinfo = fdecls#get_varinfo_by_vid fvid in
    let fnxargs = List.map (orakel#get_external_value context) args in
    let frVar = env#mk_function_return_value location context vinfo fnxargs in
    let region = memregmgr#mk_external_region_sym frVar in
    let defaultassign () =
      let assign = make_c_cmd (ASSIGN_SYM (rvar, SYM region)) in
      let nullsym = memregmgr#mk_null_sym region#getSeqNumber in
      let nullassign = make_c_cmd (ASSIGN_SYM (rvar, SYM nullsym)) in
      [make_c_branch [[assign]; [nullassign]]] in
    let summary = get_function_summary fname in
    match summary with
    | Some summary ->
       let postassigns =
         self#get_summary_post_assigns fname summary rvar region frVar args in
       begin
         match postassigns with
         | Some assigns -> assigns
         | _ -> defaultassign ()
       end
    | _ -> defaultassign ()

  method private get_summary_post_assigns
                   (fname:string)
                   (summary:function_summary_t)
                   (rvar:variable_t)               (* local return variable *)
                   (region:symbol_t)
                   (frVar:variable_t)              (* symbolic return value *)
                   (fnargs:xpr_t list) =
    let hasnull =
      List.exists (fun (pc, _) ->
          match pc with XNull ReturnValue -> true | _ -> false)
        summary.fs_error_postconditions in
    let notnull =
      List.exists (fun (pc, _) ->
          match pc with XNotNull ReturnValue -> true | _ -> false)
        summary.fs_postconditions in
    let bufptr =
      List.fold_left (fun acc (pc,_) ->
          match acc with
          | Some _ -> acc
          | _ ->
             match pc with
             | XBuffer (ReturnValue, ArgValue (ParFormal n, ArgNoOffset)) ->
                Some  (List.nth fnargs (n-1))
             | XBuffer (ReturnValue, _) ->
                Some random_constant_expr
             | _ -> acc) None summary.fs_postconditions in

    let newmemory =
      List.exists (fun (pc, _) ->
          match pc with
          | XNewMemory ReturnValue -> true
          | _ -> false) summary.fs_postconditions in

    let argreturn =
      List.fold_left (fun acc (pc, _) ->
          match acc with
          | Some _ -> acc
          | _ ->
             match pc with
             | XRelationalExpr
               (Eq, ReturnValue, ArgValue (ParFormal n, ArgNoOffset))
               | XRelationalExpr
                   (Eq,
                    Region(ReturnValue),
                    Region(ArgValue (ParFormal n, ArgNoOffset))) ->
                let arg = List.nth fnargs (n-1) in
                begin
                  match arg with
                  | XVar v -> Some (SYM_VAR v)
                  | _ -> acc
                end
             (* | XExternalStateValue (ReturnValue, ExternalState name) ->
                let lhs = env#mk_external_state_variable name SYM_VAR_TYPE in
                let regions = orakel#get_regions context (XVar lhs) in
                let basevars =
                  List.map (fun r ->
                      let memreg = memregmgr#get_memory_region r#getSeqNumber in
                      memreg#get_memory_base) regions in
                acc *)
             | _ -> acc) None summary.fs_postconditions in

    let with_null_branch cmd =
      let nullsym = memregmgr#mk_null_sym region#getSeqNumber in
      let nullassign = make_c_cmd (ASSIGN_SYM (rvar, SYM nullsym)) in
      [make_c_branch [[cmd]; [nullassign]]] in

    match (bufptr,newmemory) with         (* TBD: redo memory regions *)
    | (Some _size, true) ->
       let memsym =
         if newmemory then
           memregmgr#mk_external_region_sym frVar
         else
           raise
             (CCHFailure
                (LBLOCK [
                     STR "Unexpected type of allocation by ";
                     STR "library function ";
                     STR fname])) in
       let memassign = make_c_cmd (ASSIGN_SYM (rvar, SYM memsym)) in
       Some (if hasnull then with_null_branch memassign else [memassign])
    | _ ->
       match argreturn with
       | Some arg ->
          let argassign = make_c_cmd (ASSIGN_SYM (rvar, arg)) in
          Some (if hasnull then with_null_branch argassign else [argassign])
       | _ ->
          if notnull then
            let defassign = make_c_cmd (ASSIGN_SYM (rvar, SYM region)) in
            Some (if hasnull then with_null_branch defassign else [defassign])
          else
            let pcs =
              summary.fs_postconditions @ summary.fs_error_postconditions in
            begin
              (match pcs with
               | [] -> ()
               | _ ->
                  chlog#add
                    "unused region postconditions"
                    (LBLOCK [
                         STR fname;
                         STR " @ ";
                         INT location.line;
                         STR ": ";
                         pretty_print_list
                           pcs (fun (pc,_) -> STR (xpredicate_tag pc))
                           "[" "," "]"]));
              None
            end

  method private get_sideeffects
                   (fname:string)
                   (_loc: location)
                   (_fvid:int)
                   (args:exp list) =
    let sideeffects = get_sideeffects env#get_functionname (Some fname) context in
    let rec compose_offset base offset =
      match base with
      | NoOffset -> offset
      | Field (fuse, NoOffset) -> Field (fuse,offset)
      | Field (fuse, foffset) -> Field (fuse, compose_offset foffset offset)
      | Index _ ->
         begin
           ch_error_log#add
             "compose offset"
             (LBLOCK [
                  STR "base: ";
                  offset_to_pretty base;
                  STR "; offset: ";
                  offset_to_pretty offset]);
           NoOffset
         end in
    let rec cancel_se_struct arg baseoffset comp  =
      List.fold_left (fun acc f ->
          let foffset = Field ((f.fname,f.fckey), NoOffset)  in
          let offset = compose_offset baseoffset foffset in
          let lhs = exp_translator#translate_lhs context (Mem arg, offset) in
          if lhs#isTmp then
            let memoryvars = env#get_memory_variables in
            let _ =
              log_diagnostics_result
                ~tag:"abstract memory variables"
                ~msg:env#get_functionname
                __FILE__ __LINE__
                (List.map (fun v -> p2s v#toPretty) memoryvars) in
            [make_c_cmd (ABSTRACT_VARS memoryvars)]
          else
            let cancel = make_c_cmd (ABSTRACT_VARS [lhs]) in
            let _ =
              log_diagnostics_result
                ~tag:"abstract memory variables"
                ~msg:env#get_functionname
                __FILE__ __LINE__
                [p2s lhs#toPretty] in
            let subcancels =
              match fenv#get_type_unrolled f.ftype with
              | TComp (ckey,_) ->
                 let comp = fenv#get_comp ckey in
                 cancel_se_struct arg offset comp
              | _ -> []  in
            (cancel :: subcancels) @ acc) [] comp.cfields in
    let seeffects =
      List.concat
        (List.map (fun (se,_) ->
             match se with
             | XBlockWrite (ArgValue (ParFormal n, ArgNoOffset), _) ->
                let arg = List.nth args (n - 1) in
                let lhs =
                  exp_translator#translate_lhs context (Mem arg, NoOffset) in
                if lhs#isTmp then
                  let memoryvars = env#get_memory_variables in
                  let _ =
                    log_diagnostics_result
                      ~tag:"abstract memory variables"
                      ~msg:env#get_functionname
                      __FILE__ __LINE__
                      (List.map (fun v -> p2s v#toPretty) memoryvars) in
                  [make_c_cmd (ABSTRACT_VARS memoryvars)]
                else
                  let ty = fenv#get_type_unrolled (env#get_variable_type lhs) in
                  let cancel = make_c_cmd (ABSTRACT_VARS [lhs]) in
                  let _ =
                    log_diagnostics_result
                      ~tag:"abstract memory variables"
                      ~msg:env#get_functionname
                      __FILE__ __LINE__
                      [p2s lhs#toPretty] in
                  let subcancels =
                    match ty with
                    | TComp (ckey, _) ->
                       let comp = fenv#get_comp ckey in
                       cancel_se_struct arg NoOffset comp
                    | _ ->
                       [] in
                  cancel :: subcancels
             | XInitializesExternalState (ExternalState name,
                                          ArgValue (ParFormal n, ArgNoOffset)) ->
                let arg = List.nth args (n - 1) in
                let effects =
                  match arg with
                  | CastE (_, Const (CInt (i64, _, _)))
                       when (Int64.compare i64 Int64.zero) = 0 -> []
                  | _ ->
                     let xarg = exp_translator#translate_exp context arg in
                     let lhs = env#mk_external_state_variable name SYM_VAR_TYPE in
                     (match xarg with
                      | XVar v ->
                         let sym = memregmgr#mk_stack_region_sym v in
                         [make_c_cmd (ASSIGN_SYM (lhs, SYM sym))]
                      | XConst (SymSet [s]) ->
                         [make_c_cmd (ASSIGN_SYM (lhs, SYM s))]
                      | _ -> []) in
                effects

             | _ -> []) sideeffects) in
         seeffects
end


class stateset_call_translator_t
        (env:c_environment_int)
        (_orakel:orakel_int)
        (exp_translator:exp_translator_int):call_translator_int =
object (self)

  val mutable context = mk_program_context ()
  val fdecls = env#get_fdecls
  val mutable location = unknown_location
  val memregmgr = env#get_variable_manager#memregmgr

  method translate
           (ctxt:program_context_int)
           (loc:location)
           (lhs:lval option)
           (f:exp)
           (args:exp list) =
    let _ = context <- ctxt in
    let _ = location <- loc in
    let tmpProvider = fun () -> env#mk_sym_temp in
    let cstProvider = fun (n:numerical_t) -> env#mk_num_constant n in
    match f with
    | Lval (Var (fname,fvid),NoOffset) ->
       let vinfo = fdecls#get_varinfo_by_vid fvid in
       let fnargs = List.map (exp_translator#translate_exp ctxt) args in
       let fnxargs = List.map (fun x -> Some x) fnargs in
       let frVar = env#mk_function_return_value location context vinfo fnxargs in
       let argassigns =
         List.map (fun x ->
             let tmp = env#mk_num_temp in
             let (rhscode, numexp) = xpr2numexpr tmpProvider cstProvider x in
             let assign = make_c_cmd (ASSIGN_NUM (tmp, numexp)) in
             (tmp, [rhscode; assign])) fnargs in
       let argtmpvars = List.map fst argassigns in
       let argassigns = List.concat (List.map snd argassigns) in
       let callop =
         make_c_cmd
           (OPERATION
              { op_name = new symbol_t ~atts:[fname] "call";
                op_args =
                  List.map (fun v -> (v#getName#getBaseName, v, READ))
                    argtmpvars }) in
      let callop = make_c_cmd_block [callop] in
      let rcode =
        match lhs with
        | None -> []
        | Some lval ->
           let rvar = exp_translator#translate_lhs context lval in
           let assign = make_c_cmd (ASSIGN_SYM (rvar, SYM_VAR frVar)) in
           let postconditions = self#get_postconditions fname in
           let postassert =
             self#get_post_assert postconditions fname fvid rvar fnargs in
           [assign; postassert] in
      let assertfail =
        if is_assert_fail_function fname then
          make_c_cmd (ASSERT FALSE)
        else
          make_c_nop () in
      let sideeffects = self#get_sideeffects fname fvid args fnxargs in
      argassigns @ [callop; assertfail; sideeffects] @ rcode
    | _ -> []

  method private get_post_assert
                   (postconditions:annotated_xpredicate_t list * annotated_xpredicate_t list)
                   (fname:string)
                   (_fvid:int)
                   (rvar:variable_t)
                   (_args:xpr_t list) =
    let make_post_assert (pc,_) =
      match pc with
      | XPolicyValue (ReturnValue,pname,optname) ->
         let _ =
           chlog#add
             "initialize policy value"
             (LBLOCK [
                  STR env#get_functionname;
                  STR ": ";
                  STR fname;
                  STR ", policy: ";
                  STR pname]) in
         [make_c_cmd
            (DOMAIN_OPERATION
               (["state sets"],
                { op_name = new symbol_t "initialize" ~atts:[pname];
                  op_args = [(rvar#getName#getBaseName, rvar, READ)] }))]
         @ (match optname with
            | Some tname ->
               [make_c_cmd
                  (DOMAIN_OPERATION
                     ( ["state sets"],
                       { op_name = new symbol_t tname ~atts:[pname];
                         op_args = [(rvar#getName#getBaseName, rvar, READ)] }))]
            | _ -> [])
      | _ -> [] in
    let make l = List.concat (List.map make_post_assert l) in
    match postconditions with
    | (pl, _) ->     (* ignore error postconditions for now *)
       make_c_cmd_block (make pl)

  method private get_sideeffects
                   (fname:string)
                   (_fvid:int)
                   (_fnargs:exp list)
                   (fnxargs: (xpr_t option) list) =
    let cmds =
      match get_function_summary fname with
      | Some summary ->
         List.concat
           (List.map (fun (se,_) ->
                match se with
                | XPolicyTransition
                  (ArgValue (ParFormal n,ArgNoOffset),policyname,transitionname) ->
                   let xarg = List.nth fnxargs (n-1) in
                   begin
                     match xarg with
                     | Some (XVar v) when not v#isTmp ->
                        let _ =
                          chlog#add
                            "perform policy transition"
                            (LBLOCK [
                                 STR env#get_functionname;
                                 STR ": ";
                                 STR fname;
                                 STR ", policy: ";
                                 STR policyname;
                                 STR ", transition: ";
                                 STR transitionname;
                                 STR ", variable: ";
                                 v#toPretty]) in
                        [make_c_cmd
                            (DOMAIN_OPERATION
                               ( ["state sets"],
                                 { op_name =
                                     new symbol_t transitionname ~atts:[policyname];
                                   op_args = [(v#getName#getBaseName, v, READ)] }))]
                     | _ -> []
                   end
                | _ -> []) summary.fs_sideeffects)
      | _ -> [] in
    make_c_cmd_block cmds

  method private get_postconditions (fname:string) =
    get_postconditions env#get_functionname (Some fname) context

end


let get_num_call_translator = new num_call_translator_t

let get_sym_call_translator = new sym_call_translator_t

let get_valueset_call_translator = new valueset_call_translator_t

let get_sym_pointersets_call_translator = new sym_pointersets_call_translator_t

let get_stateset_call_translator = new stateset_call_translator_t

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024-2025  Aarno Labs LLC

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
open CHTraceResult

(* xprlib *)
open XprTypes
open XprUtil
open Xsimplify

(* bchlib *)
open BCHBCFiles
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHCPURegisters
open BCHDoubleword
open BCHFloc
open BCHFtsParameter
open BCHFunctionInfo
open BCHFunctionInterface
open BCHLibTypes
open BCHLocation
open BCHTypeConstraintUtil

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm *)
open BCHARMOpcodeRecords
open BCHARMTypes

module TR = CHTraceResult

let p2s = CHPrettyUtil.pretty_to_string


let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("FnARMTypeConstraints:" ^ tag) msg


class arm_fn_type_constraints_t
        (store: type_constraint_store_int)
        (fn: arm_assembly_function_int): arm_fn_type_constraints_int =
object (self)

  val faddrdw = fn#get_address
  val faddr = fn#get_address#to_hex_string
  val finfo = get_function_info fn#get_address
  val env = (get_function_info fn#get_address)#env
  val fndata = BCHFunctionData.functions_data#get_function fn#get_address

  method record_type_constraints =
    let fintf = finfo#get_summary#get_function_interface in
    begin
      record_function_interface_type_constraints store faddr fintf;
      fn#itera
        (fun _baddr block ->
          block#itera
            (fun ctxtiaddr instr ->
              self#record_instr_type_constraints ctxtiaddr instr))
    end

  method private record_instr_type_constraints
                   (iaddr: ctxt_iaddress_t) (instr: arm_assembly_instruction_int) =
    let loc = ctxt_string_to_location faddrdw iaddr in
    let floc = get_floc loc in
    let rewrite_expr (x: xpr_t): xpr_t =
      let x = floc#inv#rewrite_expr x in
      simplify_xpr x in

    let get_regvar_type_annotation (): btype_t option =
      if fndata#has_regvar_type_annotation loc#i then
        TR.tfold
          ~ok:(fun t -> Some t)
          ~error:(fun e ->
            begin
              log_error_result __FILE__ __LINE__ e;
              None
            end)
          (fndata#get_regvar_type_annotation loc#i)
      else
        None in

    let get_stackvar_type_annotation (offset: int): btype_t option =
      if fndata#has_stackvar_type_annotation offset then
        TR.tfold
          ~ok:(fun t -> Some t)
          ~error:(fun e ->
            begin
              log_error_result __FILE__ __LINE__ e;
              None
            end)
          (fndata#get_stackvar_type_annotation offset)
      else
        None in

    let rdef_pairs_to_pretty (pairs: (symbol_t * symbol_t) list) =
      pretty_print_list
        pairs
        (fun (s1, s2) ->
          LBLOCK [STR "("; s1#toPretty; STR ", "; s2#toPretty; STR ")"])
        "[" "; " "]" in

    let get_intvalue_type_constant (i: int): type_constant_t =
      match mk_intvalue_type_constant i with
      | Some tc -> tc
      | _ ->
         let (sg, si) =
           if i < 0 then
             if i > (-128) then (Signed, 8)
             else if i > (-BCHDoubleword.e15) then (Signed, 16)
             else if i > (-BCHDoubleword.e31) then (Signed, 32)
             else (Signed, 64)
         else
           if i < 128 then (SignedNeutral, 8)
           else if i < BCHDoubleword.e15 then (SignedNeutral, 16)
           else if i < BCHDoubleword.e31 then (SignedNeutral, 32)
           else if i = 0xffffffff then (Signed, 32)
           else (SignedNeutral, 64) in
         TyTInt (sg, si) in

    let get_variable_rdefs (v: variable_t): symbol_t list =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = floc#varinv#get_var_reaching_defs symvar in
      (match varinvs with
       | [vinv] -> vinv#get_reaching_defs
       | _ ->
          List.concat (List.map (fun vinv -> vinv#get_reaching_defs) varinvs)) in

    let get_variable_rdefs_r (v_r: variable_t traceresult): symbol_t list =
      TR.tfold_default get_variable_rdefs [] v_r in

    let get_variable_defuses (v: variable_t): symbol_t list =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = floc#varinv#get_var_def_uses symvar in
      (match varinvs with
       | [vinv] -> vinv#get_def_uses
       | _ -> []) in

    let has_exit_use (v: variable_t): bool =
      let defuses = get_variable_defuses v in
      List.exists (fun s -> s#getBaseName = "exit") defuses in

    let has_exit_use_r (v_r: variable_t traceresult): bool =
      TR.tfold_default has_exit_use false v_r in

    (*
    let getopt_initial_argument_value (x: xpr_t): (register_t * int) option =
      match (rewrite_expr x) with
      | XVar v when floc#f#env#is_initial_arm_argument_value v ->
         Some (TR.tget_ok (floc#f#env#get_initial_register_value_register v), 0)
      | XOp (XPlus, [XVar v; XConst (IntConst n)])
           when floc#f#env#is_initial_arm_argument_value v ->
         Some
           (TR.tget_ok (floc#f#env#get_initial_register_value_register v),
            n#toInt)
      | _ -> None in
     *)

    (*
    let getopt_initial_argument_value_r
          (x_r: xpr_t traceresult): (register_t * int) option =
      TR.tfold_default getopt_initial_argument_value None x_r in
     *)

    let getopt_stackaddress (x: xpr_t): int option =
      match (rewrite_expr x) with
      | XOp (xop, [XVar v; XConst (IntConst n)])
           when floc#f#env#is_initial_register_value v ->
         let optoffset =
           match xop with
           | XMinus when n#toInt > 0 -> Some n#toInt
           | XPlus when n#toInt < 0 -> Some n#neg#toInt
           | _ -> None in
         log_tfold
           (log_error "getopt_stackaddress" "invalid register")
           ~ok:(fun reg ->
             match (optoffset, reg) with
              | (Some n, ARMRegister ARSP) -> Some n
              | _ -> None)
           ~error:(fun _ -> None)
           (floc#f#env#get_initial_register_value_register v)
      | _ -> None in

    let getopt_stackaddress_r (x_r: xpr_t traceresult): int option =
      TR.tfold_default getopt_stackaddress None x_r in

    let getopt_global_address (x: xpr_t): doubleword_int option =
      match (rewrite_expr x) with
      | XConst (IntConst num) ->
         TR.tfold_default
           (fun dw ->
             if elf_header#is_code_address dw then None else Some dw)
           None
           (numerical_to_doubleword num)
      | _ ->
         None in

    let getopt_global_address_r (x_r: xpr_t traceresult): doubleword_int option =
      TR.tfold_default getopt_global_address None x_r in

    let log_subtype_constraint
          (linenumber: int)
          (kind: string)
          (ty1: type_term_t)
          (ty2: type_term_t) =
      log_diagnostics_result
        ~tag:(kind ^ " subtype constraint")
        __FILE__
        linenumber
        [(p2s floc#l#toPretty) ^ ": "
         ^ (type_term_to_string ty1)
         ^ " <: "
         ^ (type_term_to_string ty2)] in

    let log_type_constraint
          (linenumber: int) (kind: string) (tc: type_constraint_t) =
      log_diagnostics_result
        ~tag:(kind ^ " type constraint")
        __FILE__
        linenumber
        [(p2s floc#l#toPretty) ^ ": " ^ (type_constraint_to_string tc)] in

    let log_no_type_constraint
          (linenumber: int) (kind: string) (ty: btype_t) =
      log_diagnostics_result
        ~tag:("type resolution unsuccessful for " ^ kind)
        __FILE__
        linenumber
        [(p2s floc#l#toPretty) ^ ": " ^ (btype_to_string ty)] in

    let log_subtype_rule_disabled
          (linenumber: int) (name: string) (ty1: type_term_t) (ty2: type_term_t) =
      log_diagnostics_result
        ~tag:("typing rule " ^ name ^ " disabled")
        __FILE__
        linenumber
        [(p2s floc#l#toPretty) ^ ": "
         ^ (type_term_to_string ty1)
         ^ " <: "
         ^ (type_term_to_string ty2)] in

    let log_type_constraint_rule_disabled
          (linenumber: int) (name: string) (tc: type_constraint_t) =
      log_diagnostics_result
        ~tag:("typing rule " ^ name ^ " disabled")
        __FILE__
        linenumber
        [(p2s floc#l#toPretty) ^ ": " ^ (type_constraint_to_string tc)] in

    let operand_is_zero (op: arm_operand_int): bool =
      (* Returns true if the value of the operand is known to be zero at
         this location. This result is primarily intended to avoid spurious
         typing relationships in cases where the compiler 'knows' that the value
         is zero, and may use it as an alternate for the the immediate value zero
         in certain instructions, like ADD, MOV, or SUB. *)
      TR.tfold_default
        (fun v ->
          match v with
          | XConst (IntConst n) -> n#equal numerical_zero
          | _ -> false)
        false
        (TR.tmap rewrite_expr (op#to_expr floc)) in

    let operand_is_zero_in_cc_context
          (cc: arm_opcode_cc_t) (op: arm_operand_int): bool =
      match cc with
      | ACCAlways -> operand_is_zero op
      | _ when instr#is_condition_covered -> operand_is_zero op
      | _ when is_cond_conditional cc && floc#has_test_expr ->
         TR.tfold_default
           (fun xx ->
             let txpr = floc#get_test_expr in
             let tcond = rewrite_expr txpr in
             (match tcond with
              | XOp (XEq, [XVar vr; XConst (IntConst n)]) ->
                 let subst v =
                   if v#equal vr then XConst (IntConst n) else XVar vr in
                 let result = simplify_xpr (substitute_expr subst xx) in
                 (match result with
                  | XConst (IntConst n) -> n#equal numerical_zero
                  | _ -> operand_is_zero op)
              | _ -> operand_is_zero op))
           (operand_is_zero op)
           (TR.tmap rewrite_expr (op#to_expr floc))
      | _ -> operand_is_zero op in

    let regvar_type_introduction (mnem: string) (op: arm_operand_int) =
      if op#is_register then
        (match get_regvar_type_annotation () with
         | Some t ->
            let reg = op#to_register in
            let tv_z = mk_reglhs_typevar reg faddr iaddr in
            let opttc = mk_btype_constraint tv_z t in
            let rule = mnem ^ "-rvintro" in
            (match opttc with
             | Some tc ->
                begin
                  log_type_constraint __LINE__ rule tc;
                  store#add_constraint faddr iaddr rule tc
                end
             | _ -> ())
         | _ -> ())
      else
        ch_error_log#add
          "regvar-type-introduction"
          (LBLOCK [STR faddr; STR ":"; STR iaddr; STR ": ";
                   op#toPretty; STR " is not a register"]) in

    let regvar_linked_to_exit (mnem: string) (op: arm_operand_int) =
      if op#is_register then
        (if op#get_register = AR0 && (has_exit_use_r (op#to_variable floc)) then
           let reg = op#to_register in
           let tv_z = mk_reglhs_typevar reg faddr iaddr in
           let fvar = add_return_capability (mk_function_typevar faddr) in
           let tt_z = mk_vty_term tv_z in
           let fterm = mk_vty_term fvar in
           let rule = mnem ^ "-exituse" in
           if fndata#is_typing_rule_enabled iaddr rule then
             begin
               log_subtype_constraint __LINE__ rule tt_z fterm;
               store#add_subtype_constraint faddr iaddr rule tt_z fterm
             end
           else
             log_subtype_rule_disabled __LINE__ rule tt_z fterm)
      else
        () in

    match instr#get_opcode with

    | Add (_, _, rd, rn, rm, _) ->
       begin
         (regvar_type_introduction "ADD" rd);
         (regvar_linked_to_exit "ADD" rd);

         (* Heuristic: if a small number (taken here as < 256) is added to
            a register value it is assumed that the value in the destination
            register has the same type as the value in the source register.

            The case where the value of the source register is known to be zero
            is excluded, because this construct, rd = rn (=0) + imm, is often
            used as an alternate for MOV rd, #imm, in which case the type of
            the source value may be entirely unrelated to the type of
            the destination value (giving rise to very hard to diagnose typing
            errors)

            This heuristic also fails when applied to pointers to access
            different fields in a struct. Although this case is not so common,
            (ARM allows offsets to be specified as part of memory accesses),
            it does happen (it has been observed), and hence this heuristic
            is disabled for now, until we have a way to explicitly exclude
            this case.*)
         (if rm#is_immediate
             && (rm#to_numerical#toInt < 256)
             && (not (operand_is_zero rn)) then
            let rdreg = rd#to_register in
            let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
            let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
            let rnreg = rn#to_register in
            if rn#is_sp_register || rd#is_sp_register then
              (* no information to be gained from stack pointer manipulations *)
              ()
            else
              List.iter (fun rnsym ->
                  let rnaddr = rnsym#getBaseName in
                  let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
                  let rntypeterm = mk_vty_term rntypevar in
                  let lhstypeterm = mk_vty_term lhstypevar in
                  let rule = "ADD-c" in
                  if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
                    begin
                      log_subtype_constraint __LINE__ rule rntypeterm lhstypeterm;
                      store#add_subtype_constraint
                        faddr iaddr rule rntypeterm lhstypeterm
                    end
                  else
                    log_subtype_rule_disabled __LINE__ rule rntypeterm lhstypeterm
                ) rndefs);

         (match getopt_global_address_r (rn#to_expr floc) with
          | Some gaddr ->
             if rm#is_register
                && BCHConstantDefinitions.is_in_global_arrayvar gaddr then
               (match (BCHConstantDefinitions.get_arrayvar_base_offset gaddr) with
                | Some _ ->
                   let rmdefs = get_variable_rdefs_r (rm#to_variable floc) in
                   let rmreg = rm#to_register in
                   List.iter (fun rmsym ->
                       let rmaddr = rmsym#getBaseName in
                       let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
                       let tyc = mk_int_type_constant Unsigned 32 in
                       let rmtypeterm = mk_vty_term rmtypevar in
                       let ctypeterm = mk_cty_term tyc in
                       let rule = "ADD-global" in
                       if fndata#is_typing_rule_enabled
                            ~rdef:(Some rmaddr) iaddr rule then
                         begin
                           log_subtype_constraint
                             __LINE__ rule rmtypeterm ctypeterm;
                           store#add_subtype_constraint
                             faddr iaddr rule rmtypeterm ctypeterm
                         end
                       else
                         log_subtype_rule_disabled __LINE__ rule rmtypeterm ctypeterm
                     ) rmdefs
                | _ -> ())
             else
               ()
          | _ -> ())

       end

    | ArithmeticShiftRight (_, _, rd, rn, rm, _) when rm#is_immediate ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rnreg = rn#to_register in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       begin
         (regvar_type_introduction "ASR" rd);
         (regvar_linked_to_exit "ASR" rd);

         (* ASR results in a signed integer *)
         (let tc = mk_int_type_constant Signed 32 in
          let tctypeterm = mk_cty_term tc in
          let lhstypeterm = mk_vty_term lhstypevar in
          let rule = "ASR-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tctypeterm lhstypeterm;
              store#add_subtype_constraint faddr iaddr rule tctypeterm lhstypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tctypeterm lhstypeterm);

         (* ASR is applied to a signed integer *)
         (List.iter (fun rnrdef ->
              let rnaddr = rnrdef#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
              let tyc = mk_int_type_constant Signed 32 in
              let tctypeterm = mk_cty_term tyc in
              let rntypeterm = mk_vty_term rntypevar in
              let rule = "ASR-rdef" in
              if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
                begin
                  log_subtype_constraint __LINE__ rule tctypeterm rntypeterm;
                  store#add_subtype_constraint faddr iaddr rule tctypeterm rntypeterm
                end
              else
                log_subtype_rule_disabled __LINE__ rule tctypeterm rntypeterm
            ) rndefs)
       end

    | BitwiseAnd (_, _, rd, rn, _, _) ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       begin
         (regvar_type_introduction "AND" rd);
         (regvar_linked_to_exit "AND" rd);

         List.iter (fun rnsym ->
             let rnaddr = rnsym#getBaseName in
             let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
             let rntypeterm = mk_vty_term rntypevar in
             let lhstypeterm = mk_vty_term lhstypevar in
             let rule = "AND-rdef" in
             if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
               begin
                 log_subtype_constraint __LINE__ rule rntypeterm lhstypeterm;
                 store#add_subtype_constraint faddr iaddr rule rntypeterm lhstypeterm
               end
             else
               log_subtype_rule_disabled __LINE__ rule rntypeterm lhstypeterm
           ) rndefs
       end

    | BitwiseNot(_, _, rd, rm, _) when rm#is_immediate ->
       let rmval = rm#to_numerical#toInt in
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let tyc = get_intvalue_type_constant rmval in
       begin
         (regvar_type_introduction "MVN" rd);
         (regvar_linked_to_exit "MVN" rd);

         (* destination is an integer type *)
         (let tctypeterm = mk_cty_term tyc in
          let lhstypeterm = mk_vty_term lhstypevar in
          let rule = "MVN-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tctypeterm lhstypeterm;
              store#add_subtype_constraint faddr iaddr rule tctypeterm lhstypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tctypeterm lhstypeterm)
       end

    | BitwiseNot (_, _, rd, rm, _) ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rmdefs = get_variable_rdefs_r (rm#to_variable floc) in
       let rmreg = rm#to_register in
       begin
         (regvar_type_introduction "MVN" rd);
         (regvar_linked_to_exit "MVN" rd);

         (List.iter (fun rmsym ->
              let rmaddr = rmsym#getBaseName in
              let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
              let rmtypeterm = mk_vty_term rmtypevar in
              let lhstypeterm = mk_vty_term lhstypevar in
              let rule = "MVN-rdef" in
              if fndata#is_typing_rule_enabled ~rdef:(Some rmaddr) iaddr rule then
                begin
                  log_subtype_constraint __LINE__ rule rmtypeterm lhstypeterm;
                  store#add_subtype_constraint faddr iaddr rule rmtypeterm lhstypeterm
                end
              else
                log_subtype_rule_disabled __LINE__ rule rmtypeterm lhstypeterm
            ) rmdefs)
       end

    | BitwiseOr (_, _, rd, rn, rm, _) when rm#is_immediate ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       begin
         (regvar_type_introduction "ORR" rd);
         (regvar_linked_to_exit "ORR" rd);

         List.iter (fun rnsym ->
             let rnaddr = rnsym#getBaseName in
             let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
             let rntypeterm = mk_vty_term rntypevar in
             let lhstypeterm = mk_vty_term lhstypevar in
             let rule = "ORR-rdef" in
             if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
               begin
                 log_subtype_constraint __LINE__ rule rntypeterm lhstypeterm;
                 store#add_subtype_constraint faddr iaddr rule rntypeterm lhstypeterm
               end
             else
               log_subtype_rule_disabled __LINE__ rule rntypeterm lhstypeterm
           ) rndefs
       end

    | Branch _ ->
       (* no type information gained *)
       ()

    | BranchLink _ | BranchLinkExchange _
         when floc#has_call_target && floc#get_call_target#is_signature_valid ->
       let log_error (msg: string) =
         mk_tracelog_spec
           ~tag:"BranchLink type constraints" (iaddr ^ ": " ^ msg) in
       let callargs = floc#get_call_arguments in
       let (rvreg, rtype) =
         let fintf = floc#get_call_target#get_function_interface in
         let rtype = get_fts_returntype fintf in
         let rtype = if is_void_pointer rtype then t_ptrto t_uchar else rtype in
         let reg =
           if is_float rtype then
             let regtype =
               if is_float_float rtype then
                 XSingle
               else if is_float_double rtype then
                 XDouble
               else
                 XQuad in
             register_of_arm_extension_register
               ({armxr_type = regtype; armxr_index = 0})
           else
             register_of_arm_register AR0 in
         (reg, rtype) in
       begin
         (* add constraint for return value *)
         (if not (is_void rtype) then
            let typevar = mk_reglhs_typevar rvreg faddr iaddr in
            match get_regvar_type_annotation () with
            | Some t ->
               let opttc = mk_btype_constraint typevar t in
               let rule = "BL-rvintro" in
               (match opttc with
                | Some tc ->
                   begin
                     log_type_constraint __LINE__ rule tc;
                     store#add_constraint faddr iaddr rule tc
                   end
                | _ ->
                   begin
                     log_no_type_constraint __LINE__ rule t;
                     ()
                   end)
            | _ ->
               let opttc = mk_btype_constraint typevar rtype in
               let rule = "BL-sig-rv" in
               match opttc with
               | Some tc ->
                  if fndata#is_typing_rule_enabled iaddr rule then
                    begin
                      log_type_constraint __LINE__ rule tc;
                      store#add_constraint faddr iaddr rule tc
                    end
                  else
                    log_type_constraint_rule_disabled __LINE__ rule tc
               | _ ->
                  begin
                    log_no_type_constraint __LINE__ rule rtype;
                    ()
                  end);

         (* add constraints for argument values *)
         List.iter (fun (p, x) ->
             let ptype = get_parameter_type p in
             begin
               (if is_register_parameter p then
                  let regarg = TR.tget_ok (get_register_parameter_register p) in
                  let regstr = BCHCPURegisters.register_to_string regarg in
                  let pvar = floc#f#env#mk_register_variable regarg in
                  let rdefs = get_variable_rdefs pvar in
                  if not (is_unknown_type ptype) then
                    List.iter (fun rdsym ->
                        let typevar =
                          mk_reglhs_typevar regarg faddr rdsym#getBaseName in
                        let opttc = mk_btype_constraint typevar ptype in
                        let rule = "BL-sig-regarg" in
                          match opttc with
                          | Some tc ->
                             if fndata#is_typing_rule_enabled
                                  ~rdef:(Some regstr) iaddr rule then
                               begin
                                 log_type_constraint __LINE__ rule tc;
                                 store#add_constraint faddr iaddr rule tc
                               end
                             else
                               log_type_constraint_rule_disabled __LINE__ rule tc
                          | _ ->
                             begin
                               log_no_type_constraint __LINE__ rule ptype;
                               ()
                             end) rdefs
                  else
                    ()

                else if is_stack_parameter p then
                  let rule = "BL-sig-stackarg" in
                  (log_tfold_default
                     (log_error
                        ("Unable to retrieve stack offset from "
                         ^ (fts_parameter_to_string p)))
                     (fun p_offset ->
                       (log_tfold_default
                          (log_error "Unable to get current stack pointer offset")
                          (fun sp_offset ->
                            let arg_offset =
                              (sp_offset#add (mkNumerical p_offset))#neg in
                            let typevar =
                              mk_localstack_lhs_typevar
                                arg_offset#toInt faddr iaddr in
                            let opttc = mk_btype_constraint typevar ptype in
                            match opttc with
                            | Some tc ->
                               if fndata#is_typing_rule_enabled iaddr rule then
                                 begin
                                   log_type_constraint __LINE__ rule tc;
                                   store#add_constraint faddr iaddr rule tc
                                 end
                               else
                                 log_type_constraint_rule_disabled __LINE__ rule tc
                            | _ -> ())
                          ()
                          (floc#get_singleton_stackpointer_offset)))
                     ()
                     (get_stack_parameter_offset p))

                else
                  ());

               (match getopt_stackaddress x with
                | None -> ()
                | Some offset ->
                   let lhstypevar =
                     mk_localstack_lhs_typevar offset faddr iaddr in
                   match get_stackvar_type_annotation offset with
                   | Some t ->
                      let opttc = mk_btype_constraint lhstypevar t in
                      let rule = "BL-svintro" in
                      (match opttc with
                       | Some tc ->
                          begin
                            log_type_constraint __LINE__ rule tc;
                            store#add_constraint faddr iaddr rule tc
                          end
                       | _ -> ())
                   | _ ->
                      if is_pointer ptype then
                        let eltype = ptr_deref ptype in
                        let atype = t_array eltype 1 in
                        let opttc = mk_btype_constraint lhstypevar atype in
                        let rule = "BL-sig-stackarg" in
                        match opttc with
                        | Some tc ->
                           if fndata#is_typing_rule_enabled iaddr rule then
                             begin
                               log_type_constraint __LINE__ rule tc;
                               store#add_constraint faddr iaddr rule tc
                             end
                           else
                             log_type_constraint_rule_disabled __LINE__ rule tc
                        | _ -> ())
             end
           ) callargs

       end

    | Compare (_, rn, rm, _) when rm#is_immediate ->
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       let immval = rm#to_numerical#toInt in
       if immval = 0 then
         ()
       else
         List.iter (fun rnsym ->
             let rnaddr = rnsym#getBaseName in
             let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
             let immtypeconst = get_intvalue_type_constant immval in
             let rntypeterm = mk_vty_term rntypevar in
             let immtypeterm = mk_cty_term immtypeconst in
             let rule = "CMP-rdef" in
             if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
               begin
                 log_subtype_constraint __LINE__ rule rntypeterm immtypeterm;
                 store#add_subtype_constraint faddr iaddr rule rntypeterm immtypeterm
               end
             else
               log_subtype_rule_disabled __LINE__ rule rntypeterm immtypeterm
           ) rndefs

    | Compare (_, rn, rm, _) when rm#is_register ->
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rmdefs = get_variable_rdefs_r (rm#to_variable floc) in
       let rnreg = rn#to_register in
       let rmreg = rm#to_register in
       let pairs = CHUtil.xproduct rndefs rmdefs in
       begin
         chlog#add
           "type constraints: compare"
           (LBLOCK [
                STR iaddr; STR " (register):"; rdef_pairs_to_pretty pairs]);
         (List.iter (fun (rnsym, rmsym) ->
              let rnaddr = rnsym#getBaseName in
              let rmaddr = rmsym#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
              let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
              let rntypeterm = mk_vty_term rntypevar in
              let rmtypeterm = mk_vty_term rmtypevar in
              let rule = "CMP-rdef" in
              if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
                if fndata#is_typing_rule_enabled ~rdef:(Some rmaddr) iaddr rule then
                  begin
                    log_subtype_constraint __LINE__ rule rntypeterm rmtypeterm;
                    store#add_subtype_constraint
                      faddr iaddr rule rntypeterm rmtypeterm
                  end
                else
                  log_subtype_rule_disabled __LINE__ rule rntypeterm rmtypeterm
              else
                log_subtype_rule_disabled __LINE__ rule rntypeterm rmtypeterm
            ) pairs);
       end

    | LoadRegister (_, rt, rn, rm, memop, _) when rm#is_immediate ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin
         (regvar_type_introduction "LDR" rt);
         (regvar_linked_to_exit "LDR" rt);

         (* loaded type may be known *)
         (let xmem_r = memop#to_expr floc in
          let xrmem_r =
            TR.tmap (fun x -> simplify_xpr (floc#inv#rewrite_expr x)) xmem_r in
          let xtype_r = TR.tbind floc#get_xpr_type xrmem_r in
          let rule = "LDR-memop-tc" in
          TR.titer
            ~ok:(fun t ->
              let opttc = mk_btype_constraint rttypevar t in
              (match opttc with
               | Some tc ->
                  if fndata#is_typing_rule_enabled iaddr rule then
                    begin
                      log_type_constraint __LINE__ rule tc;
                      store#add_constraint faddr iaddr rule tc
                    end
                  else
                    log_type_constraint_rule_disabled __LINE__ rule tc
               | _ -> ()))
            ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
            xtype_r);

         (* LDR rt, [rn, rm] :  X_rndef.load <: X_rt *)
         (let xrdef = get_variable_rdefs_r (rn#to_variable floc) in
          let rnreg = rn#to_register in
          let offset = rm#to_numerical#toInt in
          begin

            (if rn#is_pc_register then
               ()
             else
               List.iter (fun rdsym ->
                   let ldaddr = rdsym#getBaseName in
                   let rdtypevar = mk_reglhs_typevar rnreg faddr ldaddr in
                   let rdtypevar = add_load_capability ~offset rdtypevar in
                   let rdtypeterm = mk_vty_term rdtypevar in
                   let rttypeterm = mk_vty_term rttypevar in
                   let rule = "LDR-load" in
                   if fndata#is_typing_rule_enabled
                        ~rdef:(Some ldaddr) iaddr rule then
                     begin
                       log_subtype_constraint __LINE__ rule rdtypeterm rttypeterm;
                       store#add_subtype_constraint
                         faddr iaddr rule rdtypeterm rttypeterm
                     end
                   else
                     log_subtype_rule_disabled __LINE__ rule rdtypeterm rttypeterm
                 ) xrdef);

            (* if the address to load from is the address of a global struct field,
            assign the type of that field to the destination register. *)
            (match getopt_global_address_r (memop#to_address floc) with
             | Some gaddr ->
                if BCHConstantDefinitions.is_in_global_structvar gaddr then
                  match (BCHConstantDefinitions.get_structvar_base_offset gaddr) with
                  | Some (_, Field ((fname, fckey), NoOffset)) ->
                     let compinfo = bcfiles#get_compinfo fckey in
                     let finfo = get_compinfo_field compinfo fname in
                     let finfotype = resolve_type finfo.bftype in
                     (match finfotype with
                      | Error _ -> ()
                      | Ok finfotype ->
                         let lhstype =
                           if is_struct_type finfotype then
                             let subcinfo =
                               get_struct_type_compinfo finfotype in
                             get_compinfo_scalar_type_at_offset subcinfo 0
                           else
                             Some finfotype in
                         (match lhstype with
                          | Some ty ->
                             let opttc = mk_btype_constraint rttypevar ty in
                             let rule = "LDR-struct-field" in
                             (match opttc with
                              | Some tc ->
                                 if fndata#is_typing_rule_enabled iaddr rule then
                                   begin
                                     log_type_constraint __LINE__ rule tc;
                                     store#add_constraint faddr iaddr rule tc
                                   end
                                 else
                                   log_type_constraint_rule_disabled __LINE__ rule tc
                              | _ -> ())
                          | _ ->
                             chlog#add
                               "global struct var type constraint"
                               (LBLOCK [
                                    STR iaddr;
                                    STR ": ";
                                    STR compinfo.bcname;
                                    STR ": unable to obtain field type"])))
                  | Some (dw, boffset) ->
                     let _ =
                       chlog#add
                         "global struct var type constraint"
                         (LBLOCK [
                              STR iaddr;
                              STR ": ";
                              dw#toPretty;
                              STR " with offset ";
                              offset_to_pretty boffset]) in
                     ()
                  | _ -> ()
                else
                  ()
             | _ -> ());

            (* if the value loaded is the start address of a global array,
            assign that array type to the destination register. *)
            (match getopt_global_address_r (memop#to_expr floc) with
             | Some gaddr ->
                if BCHConstantDefinitions.is_in_global_arrayvar gaddr then
                  (match (BCHConstantDefinitions.get_arrayvar_base_offset gaddr) with
                   | Some (_, offset, bty) ->
                      (match offset with
                       | Index (Const (CInt (i64, _, _)), NoOffset) ->
                          let cindex = mkNumericalFromInt64 i64 in
                          if cindex#equal numerical_zero then
                            let opttc = mk_btype_constraint rttypevar bty in
                            let rule = "LDR-array" in
                            (match opttc with
                             | Some tc ->
                                if fndata#is_typing_rule_enabled iaddr rule then
                                  begin
                                    log_type_constraint __LINE__ rule tc;
                                    store#add_constraint faddr iaddr rule tc
                                  end
                                else
                                  log_type_constraint_rule_disabled __LINE__ rule tc
                             | _ -> ())
                          else
                            ()
                       | _ ->
                          chlog#add
                            "global array var"
                            (LBLOCK [
                                 STR iaddr;
                                 STR ": ";
                                 gaddr#toPretty;
                                 STR ", ";
                                 offset_to_pretty offset
                      ]))
                   | _ -> ())
             | _ -> ());

            (match getopt_stackaddress_r (memop#to_address floc) with
             | None -> ()
             | Some offset ->
                let rhstypevar = mk_localstack_lhs_typevar offset faddr iaddr in
                let rhstypeterm = mk_vty_term rhstypevar in
                let rttypeterm = mk_vty_term rttypevar in
                let rule = "LDR-stack-addr" in
                if fndata#is_typing_rule_enabled iaddr rule then
                  begin
                    log_subtype_constraint
                      __LINE__ rule rhstypeterm rttypeterm;
                    store#add_subtype_constraint
                      faddr iaddr rule rhstypeterm rttypeterm
                  end
                else
                  log_subtype_rule_disabled __LINE__ rule rhstypeterm rttypeterm)
          end)
       end

    | LoadRegisterByte (_, rt, rn, rm, _, _) when rm#is_immediate ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin
         (regvar_type_introduction "LDRB" rt);
         (regvar_linked_to_exit "LDRB" rt);

         (* LDRB rt, [rn, rm] :  X_rndef.load <: X_rt *)
         (if rn#is_sp_register then
            ()
          else
            let xrdefs = get_variable_rdefs_r (rn#to_variable floc) in
            let rnreg = rn#to_register in
            let offset = rm#to_numerical#toInt in
            List.iter (fun rdsym ->
                let ldaddr = rdsym#getBaseName in
                let rdtypevar = mk_reglhs_typevar rnreg faddr ldaddr in
                let rdtypevar = add_load_capability ~offset ~size:1 rdtypevar in
                let rdtypeterm = mk_vty_term rdtypevar in
                let rttypeterm = mk_vty_term rttypevar in
                let rule = "LDRB-load" in
                if fndata#is_typing_rule_enabled ~rdef:(Some ldaddr) iaddr rule then
                  begin
                    log_subtype_constraint __LINE__ rule rdtypeterm rttypeterm;
                    store#add_subtype_constraint
                      faddr iaddr rule rdtypeterm rttypeterm
                  end
                else
                  log_subtype_rule_disabled __LINE__ rule rdtypeterm rttypeterm
              ) xrdefs);

         (* LDRB rt, ...  : X_rt <: integer type *)
         (let tc = mk_int_type_constant Unsigned 8 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          let rule = "LDRB-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tctypeterm rttypeterm;
              store#add_subtype_constraint faddr iaddr rule tctypeterm rttypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tctypeterm rttypeterm)

       end

    | LoadRegisterByte (_, rt, _, _, _, _) ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin
         (regvar_type_introduction "LDRB" rt);
         (regvar_linked_to_exit "LDRB" rt);

         (* LDRB rt, ...  : X_rt <: integer type *)
         (let tc = mk_int_type_constant SignedNeutral 8 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          let rule = "LDRB-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tctypeterm rttypeterm;
              store#add_subtype_constraint faddr iaddr rule tctypeterm rttypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tctypeterm rttypeterm)

       end

    | LoadRegisterHalfword (_, rt, rn, rm, memop, _) when rm#is_immediate ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin
         (regvar_type_introduction "LDRH" rt);
         (regvar_linked_to_exit "LDRH" rt);

         (* loaded type may be known *)
         (let xmem_r = memop#to_expr floc in
          let xrmem_r =
            TR.tmap (fun x -> simplify_xpr (floc#inv#rewrite_expr x)) xmem_r in
          let xtype_r = TR.tbind floc#get_xpr_type xrmem_r in
          TR.titer
            ~ok:(fun t ->
              let opttc = mk_btype_constraint rttypevar t in
              let rule = "LDRH-memop-tc" in
              (match opttc with
               | Some tc ->
                  if fndata#is_typing_rule_enabled iaddr rule then
                    begin
                      log_type_constraint __LINE__ rule tc;
                      store#add_constraint faddr iaddr rule tc
                    end
                  else
                    log_type_constraint_rule_disabled __LINE__ rule tc
               | _ -> ()))
            ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
            xtype_r);

         (* LDRH rt, [rn, rm] :  X_rndef.load <: X_rt *)
         (let xrdef = get_variable_rdefs_r (rn#to_variable floc) in
          let rnreg = rn#to_register in
          let offset = rm#to_numerical#toInt in
          List.iter (fun rdsym ->
              let ldaddr = rdsym#getBaseName in
              let rdtypevar = mk_reglhs_typevar rnreg faddr ldaddr in
              let rdtypevar = add_load_capability ~offset ~size:2 rdtypevar in
              let rdtypeterm = mk_vty_term rdtypevar in
              let rttypeterm = mk_vty_term rttypevar in
              let rule = "LDRH-load" in
              if fndata#is_typing_rule_enabled ~rdef:(Some ldaddr) iaddr rule then
                begin
                  log_subtype_constraint __LINE__ rule rdtypeterm rttypeterm;
                  store#add_subtype_constraint faddr iaddr rule rdtypeterm rttypeterm
                end
              else
                log_subtype_rule_disabled __LINE__ rule rdtypeterm rttypeterm
            ) xrdef)
       end

    | LoadRegisterHalfword (_, rt, _, _, _, _) ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin
         (regvar_type_introduction "LDRH" rt);
         (regvar_linked_to_exit "LDRH" rt);

       (* LDRH rt, ...  : X_rt <: integer type *)
         (let tc = mk_int_type_constant SignedNeutral 16 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          let rule = "LDRH-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tctypeterm rttypeterm;
              store#add_subtype_constraint faddr iaddr rule tctypeterm rttypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tctypeterm rttypeterm)
       end

    | LogicalShiftLeft (_, _, rd, rn, rm, _) when rm#is_immediate ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rnreg = rn#to_register in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       begin
         (regvar_type_introduction "LSL" rd);
         (regvar_linked_to_exit "LSL" rd);

         (* LSL results in an unsigned integer *)
         (let tc = mk_int_type_constant Unsigned 32 in
          let tcterm = mk_cty_term tc in
          let lhstypeterm = mk_vty_term lhstypevar in
          let rule = "LSL-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tcterm lhstypeterm;
              store#add_subtype_constraint faddr iaddr rule tcterm lhstypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tcterm lhstypeterm);

         (* LSL is applied to an unsigned integer *)
         (let rule = "LSL-rdef" in
          List.iter (fun rnrdef ->
              let rnaddr = rnrdef#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
              let tyc = mk_int_type_constant Unsigned 32 in
              let tctypeterm = mk_cty_term tyc in
              let rntypeterm = mk_vty_term rntypevar in
              if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
                begin
                  log_subtype_constraint __LINE__ rule tctypeterm rntypeterm;
                  store#add_subtype_constraint faddr iaddr rule tctypeterm rntypeterm
                end
              else
                log_subtype_rule_disabled __LINE__ rule tctypeterm rntypeterm
            ) rndefs)
       end

    | LogicalShiftRight (_, _, rd, rn, rm, _) when rm#is_immediate ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rnreg = rn#to_register in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       begin
         (regvar_type_introduction "LSR" rd);
         (regvar_linked_to_exit "LSR" rd);

         (* LSR results in an unsigned integer *)
         (let tc = mk_int_type_constant Unsigned 32 in
          let tcterm = mk_cty_term tc in
          let lhstypeterm = mk_vty_term lhstypevar in
          let rule = "LSR-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tcterm lhstypeterm;
              store#add_subtype_constraint faddr iaddr rule tcterm lhstypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tcterm lhstypeterm);

         (* LSR is applied to an unsigned integer *)
         (List.iter (fun rnrdef ->
              let rnaddr = rnrdef#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
              let tyc = mk_int_type_constant Unsigned 32 in
              let tctypeterm = mk_cty_term tyc in
              let rntypeterm = mk_vty_term rntypevar in
              let rule = "LSR-rdef" in
              if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
                begin
                  log_subtype_constraint __LINE__ rule tctypeterm rntypeterm;
                  store#add_subtype_constraint faddr iaddr rule tctypeterm rntypeterm
                end
              else
                log_subtype_rule_disabled __LINE__ rule tctypeterm rntypeterm
            ) rndefs)

       end

    | Move (_, _, rd, rm, _, _) when rm#is_immediate ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       begin
         (regvar_type_introduction "MOV" rd);
         (regvar_linked_to_exit "MOV" rd);

         (let rmval = rm#to_numerical#toInt in
          (* 0 provides no information about the type *)
          if rmval = 0 then
            ()
          else
            let tyc = get_intvalue_type_constant rmval in
            let lhstypeterm = mk_vty_term lhstypevar in
            let tctypeterm = mk_cty_term tyc in
            let rule = "MOV-c" in
            if fndata#is_typing_rule_enabled iaddr rule then
              begin
                log_subtype_constraint __LINE__ rule tctypeterm lhstypeterm;
                store#add_subtype_constraint faddr iaddr rule tctypeterm lhstypeterm
              end
            else
              log_subtype_rule_disabled __LINE__ rule tctypeterm lhstypeterm)
       end

    | Move (_, _, rd, rm, _, _) when rd#get_register = rm#get_register ->
    (* exclude to avoid spurious rdefs to get involved *)
       ()

    (* Move x, y  ---  x := y  --- Y <: X *)
    | Move (_, c, rd, rm, _, _) when rm#is_register ->
       let _xrm_r = rm#to_expr floc in
       let rdreg = rd#to_register in
       begin
         (regvar_type_introduction "MOV" rd);
         (regvar_linked_to_exit "MOV" rd);

         (* use reaching defs *)
         (let rmreg = rm#to_register in
          if operand_is_zero_in_cc_context c rm then
            (* This case is excluded, because the move from a register
               that contains zero can be done as a substitute for the
               move of an immediate value, without any relationships in
               types between the source and destination register. It is
               often used by compilers as a convenience, if the register
               is known to have the value zero at this point. *)
            ()
          else
            let rmvar_r = rm#to_variable floc in
            let rmrdefs = get_variable_rdefs_r rmvar_r in
            let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
            let rule = "MOV-rdef" in
            List.iter (fun rmrdef ->
                let rmaddr = rmrdef#getBaseName in
                let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
                let rmtypeterm = mk_vty_term rmtypevar in
                let lhstypeterm = mk_vty_term lhstypevar in
                if fndata#is_typing_rule_enabled ~rdef:(Some rmaddr) iaddr rule then
                  begin
                    log_subtype_constraint __LINE__ rule rmtypeterm lhstypeterm;
                    store#add_subtype_constraint
                      faddr iaddr rule rmtypeterm lhstypeterm
                  end
                else
                  log_subtype_rule_disabled __LINE__ rule rmtypeterm lhstypeterm
              ) rmrdefs)
       end

    | Pop (_, _, rl, _) when rl#includes_pc ->
       let fsig = finfo#get_summary#get_function_interface.fintf_type_signature in
       let _ =
         chlog#add
           "POP-function-signature"
           (LBLOCK [STR (btype_to_string fsig.fts_returntype)]) in
       let rtype = fsig.fts_returntype in
       (match rtype with
        | TVoid _ -> ()
        | _ ->
           let reg = register_of_arm_register AR0 in
           let typevar = mk_reglhs_typevar reg faddr iaddr in

           begin
             (* use function return type *)
             (let opttc = mk_btype_constraint typevar rtype in
              let rule = "POP-sig-rv" in
              match opttc with
              | Some tc ->
                 if fndata#is_typing_rule_enabled iaddr rule then
                   begin
                     log_type_constraint __LINE__ rule tc;
                     store#add_constraint faddr iaddr rule tc
                   end
                 else
                   log_type_constraint_rule_disabled __LINE__ rule tc
              | _ ->
                 begin
                   log_no_type_constraint __LINE__ rule rtype;
                   ()
                 end);

             (* propagate via reaching defs *)
             (let r0var = floc#env#mk_arm_register_variable AR0 in
              let r0defs = get_variable_rdefs r0var in
              let rule = "POP-rdef" in
              List.iter (fun r0def ->
                  let r0addr = r0def#getBaseName in
                  let r0typevar = mk_reglhs_typevar reg faddr r0addr in
                  let r0typeterm = mk_vty_term r0typevar in
                  let lhstypeterm = mk_vty_term typevar in
                  if fndata#is_typing_rule_enabled ~rdef:(Some r0addr) iaddr rule then
                    begin
                      log_subtype_constraint __LINE__ rule r0typeterm lhstypeterm;
                      store#add_subtype_constraint
                        faddr iaddr rule r0typeterm lhstypeterm
                    end
                  else
                    log_subtype_rule_disabled __LINE__ rule r0typeterm lhstypeterm
                ) r0defs)
             end)

    | Push _
      | Pop _ ->
       (* no type information gained *)
       ()

    | ReverseSubtract (_, _, rd, _, rm, _) when rm#is_register ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rmdefs = get_variable_rdefs_r (rm#to_variable floc) in
       let rmreg = rm#to_register in
       begin
         (regvar_type_introduction "RSB" rd);
         (regvar_linked_to_exit "RSB" rd);

         (let rule = "RSB-rdef" in
          List.iter (fun rmsym ->
              let rmaddr = rmsym#getBaseName in
              let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
              let rmtypeterm = mk_vty_term rmtypevar in
              let lhstypeterm = mk_vty_term lhstypevar in
              if fndata#is_typing_rule_enabled ~rdef:(Some rmaddr) iaddr rule then
                begin
                  log_subtype_constraint __LINE__ rule rmtypeterm lhstypeterm;
                  store#add_subtype_constraint faddr iaddr rule rmtypeterm lhstypeterm
                end
              else
                log_subtype_rule_disabled __LINE__ rule rmtypeterm lhstypeterm
            ) rmdefs);
       end

    | SignedMultiplyLong (_, _, rdlo, rdhi, rn, rm) ->
       let rdloreg = rdlo#to_register in
       let lhslotypevar = mk_reglhs_typevar rdloreg faddr iaddr in
       let rdhireg = rdhi#to_register in
       let lhshitypevar = mk_reglhs_typevar rdhireg faddr iaddr in
       let rnreg = rn#to_register in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rmreg = rm#to_register in
       let rmdefs = get_variable_rdefs_r (rm#to_variable floc) in

       let tc = mk_int_type_constant Signed 32 in
       let tctypeterm = mk_cty_term tc in
       let lhslotypeterm = mk_vty_term lhslotypevar in
       let lhshitypeterm = mk_vty_term lhshitypevar in
       let rule1 = "SMULL-def-lhs" in
       let rule2 = "SMULL-rdef" in
       begin

         (if fndata#is_typing_rule_enabled iaddr rule1 then
            begin
              log_subtype_constraint __LINE__ rule1 tctypeterm lhslotypeterm;
              store#add_subtype_constraint faddr iaddr rule1 tctypeterm lhslotypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule1 tctypeterm lhslotypeterm);

         (if fndata#is_typing_rule_enabled iaddr rule1 then
            begin
              log_subtype_constraint __LINE__ rule1 tctypeterm lhshitypeterm;
              store#add_subtype_constraint faddr iaddr rule1 tctypeterm lhshitypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule1 tctypeterm lhshitypeterm);

         (List.iter (fun rnrdef ->
              let rnaddr = rnrdef#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
              let rntypeterm = mk_vty_term rntypevar in
              if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule2 then
                begin
                  log_subtype_constraint __LINE__ rule2 tctypeterm rntypeterm;
                  store#add_subtype_constraint faddr iaddr rule2 tctypeterm rntypeterm
                end
              else
                log_subtype_rule_disabled __LINE__ rule2 tctypeterm rntypeterm
            ) rndefs);

         (List.iter (fun rmrdef ->
              let rmaddr = rmrdef#getBaseName in
              let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
              let rmtypeterm = mk_vty_term rmtypevar in
              if fndata#is_typing_rule_enabled ~rdef:(Some rmaddr) iaddr rule2 then
                begin
                  log_subtype_constraint __LINE__ rule2 tctypeterm rmtypeterm;
                  store#add_subtype_constraint faddr iaddr rule2 tctypeterm rmtypeterm
                end
              else
                log_subtype_rule_disabled __LINE__ rule2 tctypeterm rmtypeterm
            ) rmdefs)
       end

    (* Store x in y  ---  *y := x  --- X <: Y.store *)
    | StoreRegister (_, rt, rn, rm, memvarop, _) when rm#is_immediate ->
       let rnrdefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       let offset = rm#to_numerical#toInt in
       let rtrdefs = get_variable_rdefs_r (rt#to_variable floc) in
       let rtreg = rt#to_register in
       let xaddr_r = memvarop#to_address floc in
       begin

         (match getopt_stackaddress_r xaddr_r with
          | None -> ()
          | Some spoffset ->
             let lhstypevar = mk_localstack_lhs_typevar spoffset faddr iaddr in
             begin

               (* propagate src register type from rdefs *)
               (let rtreg = rt#to_register in
                let rtvar_r = rt#to_variable floc in
                let rtrdefs = get_variable_rdefs_r rtvar_r in
                let rule = "STR-rdef" in
                List.iter (fun rtrdef ->
                    let rtaddr = rtrdef#getBaseName in
                    let rttypevar = mk_reglhs_typevar rtreg faddr rtaddr in
                    let rttypeterm = mk_vty_term rttypevar in
                    let lhstypeterm = mk_vty_term lhstypevar in
                    if fndata#is_typing_rule_enabled
                         ~rdef:(Some rtaddr) iaddr rule then
                      begin
                        log_subtype_constraint
                          __LINE__ rule rttypeterm lhstypeterm;
                        store#add_subtype_constraint
                          faddr iaddr rule rttypeterm lhstypeterm
                      end
                    else
                      log_subtype_rule_disabled __LINE__ rule rttypeterm lhstypeterm
                  ) rtrdefs);

               (* import type from stackvar-introductions *)
               (match get_stackvar_type_annotation offset with
                | None -> ()
                | Some t ->
                   let lhstypevar =
                     mk_localstack_lhs_typevar offset faddr iaddr in
                   let opttc = mk_btype_constraint lhstypevar t in
                   let rule = "STR-svintro" in
                   (match opttc with
                    | Some tc ->
                       begin
                         log_type_constraint __LINE__ rule tc;
                         store#add_constraint faddr iaddr rule tc
                       end
                    | _ ->
                       log_no_type_constraint __LINE__ rule t))
             end);

         (let rule = "STR-store" in
          if rn#is_sp_register then
            ()
          else
            List.iter (fun rndsym ->
                let straddr = rndsym#getBaseName in
                let rntypevar = mk_reglhs_typevar rnreg faddr straddr in
                let rntypevar = add_store_capability ~size:4 ~offset rntypevar in
                List.iter (fun rtdsym ->
                    let rtdloc = rtdsym#getBaseName in
                    let rttypevar = mk_reglhs_typevar rtreg faddr rtdloc in
                    let rttypeterm = mk_vty_term rttypevar in
                    let rntypeterm = mk_vty_term rntypevar in
                    if fndata#is_typing_rule_enabled
                         ~rdef:(Some rtdloc) iaddr rule then
                      begin
                        log_subtype_constraint __LINE__ rule rttypeterm rntypeterm;
                        store#add_subtype_constraint
                          faddr iaddr rule rttypeterm rntypeterm
                      end
                    else
                      log_subtype_rule_disabled __LINE__ rule rttypeterm rntypeterm
                  ) rtrdefs) rnrdefs);

         (* type of destination memory location may be known *)
         (let vmem_r = memvarop#to_variable floc in
          let vtype_r = TR.tbind floc#get_variable_type vmem_r in
          let rule = "STR-memop-tc" in
          TR.titer
            ~ok:(fun t ->
              List.iter (fun rtdsym ->
                  let rtdloc = rtdsym#getBaseName in
                  let rttypevar = mk_reglhs_typevar rtreg faddr rtdloc in
                  let opttc = mk_btype_constraint rttypevar t in
                  match opttc with
                  | Some tc ->
                     if fndata#is_typing_rule_enabled iaddr rule then
                       begin
                         log_type_constraint __LINE__ rule tc;
                         store#add_constraint faddr iaddr rule tc
                       end
                     else
                       log_type_constraint_rule_disabled __LINE__ rule tc
                  | _ -> ()) rtrdefs)
            ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
            vtype_r)

       end

    | StoreRegisterByte (_, rt, rn, rm, _memvarop, _) when rm#is_immediate ->
       let rnrdefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       let offset = rm#to_numerical#toInt in
       let rtrdefs = get_variable_rdefs_r (rt#to_variable floc) in
       let rtreg = rt#to_register in
       begin

         (* STRB rt, ...  : X_rt <: integer type *)
         (let rtreg = rt#to_register in
          let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
          let tc = mk_int_type_constant SignedNeutral 8 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          let rule = "STRB-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tctypeterm rttypeterm;
              store#add_subtype_constraint faddr iaddr rule tctypeterm rttypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tctypeterm rttypeterm);

         (let rule = "STRB-rdef" in
          List.iter (fun rndsym ->
              let straddr = rndsym#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr straddr in
              let rntypevar = add_load_capability ~size:1 ~offset rntypevar in
              List.iter (fun rtdsym ->
                  let rtdloc = rtdsym#getBaseName in
                  let rttypevar = mk_reglhs_typevar rtreg faddr rtdloc in
                  let rttypeterm = mk_vty_term rttypevar in
                  let rntypeterm = mk_vty_term rntypevar in
                  if fndata#is_typing_rule_enabled
                       ~rdef:(Some straddr) iaddr rule then
                    if fndata#is_typing_rule_enabled
                         ~rdef:(Some rtdloc) iaddr rule then
                      begin
                        log_subtype_constraint __LINE__ rule rttypeterm rntypeterm;
                        store#add_subtype_constraint
                          faddr iaddr rule rttypeterm rntypeterm
                      end
                    else
                      log_subtype_rule_disabled __LINE__ rule rttypeterm rntypeterm
                  else
                    log_subtype_rule_disabled __LINE__ rule rttypeterm rntypeterm
                ) rtrdefs
            ) rnrdefs)

       end

    | StoreRegisterByte (_, rt, _, _, _, _) ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin

         (* STRB rt, ...  : X_rt <: integer type *)
         (let tc = mk_int_type_constant SignedNeutral 8 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          let rule = "STRB-def-lhs" in
          if fndata#is_typing_rule_enabled iaddr rule then
            begin
              log_subtype_constraint __LINE__ rule tctypeterm rttypeterm;
              store#add_subtype_constraint faddr iaddr rule tctypeterm rttypeterm
            end
          else
            log_subtype_rule_disabled __LINE__ rule tctypeterm rttypeterm)

       end

    | Subtract (_, _, rd, rn, rm, _, _) ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       begin
         (regvar_type_introduction "SUB" rd);
         (regvar_linked_to_exit "SUB" rd);

         (* Note: Does not take into consideration the possibility of the
            subtraction of two pointers *)
         (if rm#is_immediate && (rm#to_numerical#toInt = 0) then
            ()
          else if rd#is_sp_register && rn#is_sp_register then
            (* no type information to be gained from stackpointer manipulations *)
            ()
          else
            let rule = "SUB-rdef" in
            List.iter (fun rnsym ->
                let rnaddr = rnsym#getBaseName in
                let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
                let rntypeterm = mk_vty_term rntypevar in
                let lhstypeterm = mk_vty_term lhstypevar in
                if fndata#is_typing_rule_enabled ~rdef:(Some rnaddr) iaddr rule then
                  begin
                    log_subtype_constraint __LINE__ rule rntypeterm lhstypeterm;
                    store#add_subtype_constraint
                      faddr iaddr rule rntypeterm lhstypeterm
                  end
                else
                  log_subtype_rule_disabled __LINE__ rule rntypeterm lhstypeterm
              ) rndefs);

       end

    | UnsignedBitFieldExtract (_, rd, rn) ->
       begin
         (regvar_type_introduction "UBFX" rd);
         (regvar_linked_to_exit "UBFX" rd);

         (match rn#get_kind with
          | ARMRegBitSequence (r, _, _) ->
             let rnreg = register_of_arm_register r in
             let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
             begin
               (List.iter (fun rnrdef ->
                    let rnaddr = rnrdef#getBaseName in
                    let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
                    let tyc = mk_int_type_constant Unsigned 32 in
                    let tctypeterm = mk_cty_term tyc in
                    let rntypeterm = mk_vty_term rntypevar in
                    let rule = "UBFX-rdef" in
                    if fndata#is_typing_rule_enabled
                         ~rdef:(Some rnaddr) iaddr rule then
                      begin
                        log_subtype_constraint __LINE__ rule tctypeterm rntypeterm;
                        store#add_subtype_constraint
                          faddr iaddr rule tctypeterm rntypeterm
                      end
                    else
                      log_subtype_rule_disabled __LINE__ rule tctypeterm rntypeterm
                  ) rndefs)
             end
          | _ -> ())
       end

    | UnsignedExtendHalfword (_, rd, _, _) ->
       let rdreg = rd#to_register in
       let rdtypevar = mk_reglhs_typevar rdreg faddr iaddr in
       begin
         (regvar_type_introduction "UXTH" rd);
         (regvar_linked_to_exit "UXTH" rd);

         (let opttc = mk_btype_constraint rdtypevar t_short in
          let rule = "UBFX-def-lhs" in
          (match opttc with
           | Some tc ->
              if fndata#is_typing_rule_enabled iaddr rule then
                begin
                  log_type_constraint __LINE__ rule tc;
                  store#add_constraint faddr iaddr rule tc
                end
              else
                log_type_constraint_rule_disabled __LINE__ rule tc
           | _ -> ()));
       end

    | opc ->
       log_diagnostics_result
         ~tag:"type constraints not yet implemented"
         __FILE__ __LINE__
         [(p2s floc#l#toPretty) ^ ": " ^ (arm_opcode_to_string opc)]

end


let  mk_arm_fn_type_constraints
       (store: type_constraint_store_int)
       (fn: arm_assembly_function_int): arm_fn_type_constraints_int =
  begin
    store#reset;
    new arm_fn_type_constraints_t store fn
  end

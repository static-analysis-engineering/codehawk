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
       | _ -> []) in

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

    let getopt_initial_argument_value_r
          (x_r: xpr_t traceresult): (register_t * int) option =
      TR.tfold_default getopt_initial_argument_value None x_r in

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

    match instr#get_opcode with

    | Add (_, _, rd, rn, rm, _) ->
       let xrn_r = rn#to_expr floc in
       begin

         (match get_regvar_type_annotation () with
          | Some t ->
            let rdreg = rd#to_register in
            let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
            let opttc = mk_btype_constraint lhstypevar t in
            (match opttc with
             | Some tc ->
                begin
                  log_type_constraint __LINE__ "ADD-rvintro" tc;
                  store#add_constraint tc
                end
             | _ -> ())
          | _ -> ());

         (if rm#is_immediate && (rm#to_numerical#toInt < 256) then
            let rdreg = rd#to_register in
            let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
            let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
            let rnreg = rn#to_register in
            List.iter (fun rnsym ->
                let rnaddr = rnsym#getBaseName in
                let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
                let rntypeterm = mk_vty_term rntypevar in
                let lhstypeterm = mk_vty_term lhstypevar in
                begin
                  log_subtype_constraint __LINE__ "ADD-imm" rntypeterm lhstypeterm;
                  store#add_subtype_constraint rntypeterm lhstypeterm
                end) rndefs);

         (match getopt_global_address_r (rn#to_expr floc) with
          | Some gaddr ->
             if BCHConstantDefinitions.is_in_global_arrayvar gaddr then
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
                       begin
                         log_subtype_constraint
                           __LINE__ "ADD-global" rmtypeterm ctypeterm;
                         store#add_subtype_constraint rmtypeterm ctypeterm
                       end) rmdefs
                | _ -> ())
             else
               ()
          | _ -> ());

         (match getopt_initial_argument_value_r xrn_r with
          | Some (reg, _) ->
             let ftvar = mk_function_typevar faddr in
             let ftvar = add_freg_param_capability reg ftvar in
             let rdreg = rd#to_register in
             let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
             let fttypeterm = mk_vty_term ftvar in
             let lhstypeterm = mk_vty_term lhstypevar in
             begin
               log_subtype_constraint
                 __LINE__ "ADD-lhs-init" fttypeterm lhstypeterm;
               store#add_subtype_constraint fttypeterm lhstypeterm
             end
          | _ -> ())
       end

    | ArithmeticShiftRight (_, _, rd, rn, rm, _) when rm#is_immediate ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rnreg = rn#to_register in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       begin

         (* ASR results in a signed integer *)
         (let tc = mk_int_type_constant Signed 32 in
          let tctypeterm = mk_cty_term tc in
          let lhstypeterm = mk_vty_term lhstypevar in
          begin
            log_subtype_constraint __LINE__ "ASR-lhs" tctypeterm lhstypeterm;
            store#add_subtype_constraint tctypeterm lhstypeterm
          end);

         (* ASR is applied to a signed integer *)
         (List.iter (fun rnrdef ->
              let rnaddr = rnrdef#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
              let tyc = mk_int_type_constant Signed 32 in
              let tctypeterm = mk_cty_term tyc in
              let rntypeterm = mk_vty_term rntypevar in
              begin
                log_subtype_constraint __LINE__ "ASR-rhs" tctypeterm rntypeterm;
                store#add_subtype_constraint tctypeterm rntypeterm
              end) rndefs)
       end

    | BitwiseAnd (_, _, rd, rn, _, _) ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       begin

         List.iter (fun rnsym ->
             let rnaddr = rnsym#getBaseName in
             let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
             let rntypeterm = mk_vty_term rntypevar in
             let lhstypeterm = mk_vty_term lhstypevar in
             begin
               log_subtype_constraint __LINE__ "AND-rdef-1" rntypeterm lhstypeterm;
               store#add_subtype_constraint rntypeterm lhstypeterm
             end) rndefs
       end

    | BitwiseNot(_, _, rd, rm, _) when rm#is_immediate ->
       let rmval = rm#to_numerical#toInt in
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let tyc = get_intvalue_type_constant rmval in
       begin

         (* destination is an integer type *)
         (let tctypeterm = mk_cty_term tyc in
          let lhstypeterm = mk_vty_term lhstypevar in
          begin
            log_subtype_constraint __LINE__ "MVN" tctypeterm lhstypeterm;
            store#add_subtype_constraint tctypeterm lhstypeterm
          end)

       end

    | BitwiseNot (_, _, rd, rm, _) ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rmdefs = get_variable_rdefs_r (rm#to_variable floc) in
       let rmreg = rm#to_register in
       begin
         List.iter (fun rmsym ->
             let rmaddr = rmsym#getBaseName in
             let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
             let rmtypeterm = mk_vty_term rmtypevar in
             let lhstypeterm = mk_vty_term lhstypevar in
             begin
               log_subtype_constraint __LINE__ "MVN-rdef" rmtypeterm lhstypeterm;
               store#add_subtype_constraint rmtypeterm lhstypeterm
             end) rmdefs
       end

    | BitwiseOr (_, _, rd, rn, _, _) ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       begin

         List.iter (fun rnsym ->
             let rnaddr = rnsym#getBaseName in
             let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
             let rntypeterm = mk_vty_term rntypevar in
             let lhstypeterm = mk_vty_term lhstypevar in
             begin
               log_subtype_constraint __LINE__ "AND-rdef-1" rntypeterm lhstypeterm;
               store#add_subtype_constraint rntypeterm lhstypeterm
             end) rndefs
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
               (match opttc with
                | Some tc ->
                   begin
                     log_type_constraint __LINE__ "BL-rv-intro" tc;
                     store#add_constraint tc
                   end
                | _ ->
                   begin
                     log_no_type_constraint __LINE__ "BL-rv-intro" t;
                     ()
                   end)
            | _ ->
               let opttc = mk_btype_constraint typevar rtype in
               match opttc with
               | Some tc ->
                  begin
                    log_type_constraint __LINE__ "BL-rv" tc;
                    store#add_constraint tc
                  end
               | _ ->
                  begin
                    log_no_type_constraint __LINE__ "BL-rv" rtype;
                    ()
                  end);

         (* add constraints for argument values *)
         List.iter (fun (p, x) ->
             let ptype = get_parameter_type p in
             begin
               (if is_register_parameter p then
                  let regarg = TR.tget_ok (get_register_parameter_register p) in
                  let pvar = floc#f#env#mk_register_variable regarg in
                  let rdefs = get_variable_rdefs pvar in
                  if not (is_unknown_type ptype) then
                    List.iter (fun rdsym ->
                        let typevar =
                          mk_reglhs_typevar regarg faddr rdsym#getBaseName in
                        let opttc = mk_btype_constraint typevar ptype in
                        match opttc with
                        | Some tc ->
                           begin
                             log_type_constraint __LINE__ "BL-reg-arg" tc;
                             store#add_constraint tc
                           end
                        | _ ->
                           begin
                             log_no_type_constraint __LINE__ "BL-reg-arg" ptype;
                             ()
                           end) rdefs
                  else
                    ()

                else if is_stack_parameter p then
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
                               begin
                                 log_type_constraint __LINE__ "BL-stack-arg" tc;
                                 store#add_constraint tc
                               end
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
                      (match opttc with
                       | Some tc ->
                          begin
                            log_type_constraint __LINE__ "BL-stack-vintro" tc;
                            store#add_constraint tc
                          end
                       | _ -> ())
                   | _ ->
                      if is_pointer ptype then
                        let eltype = ptr_deref ptype in
                        let atype = t_array eltype 1 in
                        let opttc = mk_btype_constraint lhstypevar atype in
                        match opttc with
                        | Some tc ->
                           begin
                             log_type_constraint __LINE__ "BL-reg-arg" tc;
                             store#add_constraint tc
                           end
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
             begin
               log_subtype_constraint __LINE__ "CMP-imm" rntypeterm immtypeterm;
               store#add_subtype_constraint rntypeterm immtypeterm
             end) rndefs

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
              begin
                log_subtype_constraint __LINE__ "CMP-reg" rntypeterm rmtypeterm;
                store#add_subtype_constraint rntypeterm rmtypeterm
              end) pairs);

         (let xrn_r = rn#to_expr floc in
          match getopt_initial_argument_value_r xrn_r with
          | Some (reg, _) ->
             let ftvar = mk_function_typevar faddr in
             let ftvar = add_freg_param_capability reg ftvar in
             List.iter (fun rmsym ->
                 let rmaddr = rmsym#getBaseName in
                 let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
                 let ftterm = mk_vty_term ftvar in
                 let rmtypeterm = mk_vty_term rmtypevar in
                 begin
                   log_subtype_constraint __LINE__ "CMP-reg-init" ftterm rmtypeterm;
                   store#add_subtype_constraint ftterm rmtypeterm
                 end) rmdefs
          | _ -> ());

         (let xrm_r = rm#to_expr floc in
          match getopt_initial_argument_value_r xrm_r with
          | Some (reg, _) ->
             let ftvar = mk_function_typevar faddr in
             let ftvar = add_freg_param_capability reg ftvar in
             List.iter (fun rnsym ->
                 let rnaddr = rnsym#getBaseName in
                 let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
                 let ftterm = mk_vty_term ftvar in
                 let rntypeterm = mk_vty_term rntypevar in
                 begin
                   log_subtype_constraint __LINE__ "CMP-reg-init" ftterm rntypeterm;
                   store#add_subtype_constraint ftterm rntypeterm
                 end) rndefs
          | _ -> ())
       end

    | LoadRegister (_, rt, rn, rm, memop, _) when rm#is_immediate ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin

         (* variable introduction for lhs with type *)
         (match get_regvar_type_annotation () with
          | Some t ->
             let opttc = mk_btype_constraint rttypevar t in
             (match opttc with
              | Some tc ->
                 begin
                   log_type_constraint __LINE__ "LDR-rvintro" tc;
                   store#add_constraint tc
                 end
              | _ -> ())
          | _ -> ());

         (* loaded type may be known *)
         (let xmem_r = memop#to_expr floc in
          let xrmem_r =
            TR.tmap (fun x -> simplify_xpr (floc#inv#rewrite_expr x)) xmem_r in
          let xtype_r = TR.tbind floc#get_xpr_type xrmem_r in
          TR.titer
            ~ok:(fun t ->
              let opttc = mk_btype_constraint rttypevar t in
              (match opttc with
               | Some tc ->
                  begin
                    log_type_constraint __LINE__ "LDR-var" tc;
                    store#add_constraint tc
                  end
               | _ -> ()))
            ~error:(fun e -> log_error_result __FILE__ __LINE__ e)
            xtype_r);

         (* LDR rt, [rn, rm] :  X_rndef.load <: X_rt *)
         (let xrdef = get_variable_rdefs_r (rn#to_variable floc) in
          let rnreg = rn#to_register in
          let offset = rm#to_numerical#toInt in
          List.iter (fun rdsym ->
              let ldaddr = rdsym#getBaseName in
              let rdtypevar = mk_reglhs_typevar rnreg faddr ldaddr in
              let rdtypevar = add_load_capability ~offset rdtypevar in
              let rdtypeterm = mk_vty_term rdtypevar in
              let rttypeterm = mk_vty_term rttypevar in
              begin
                log_subtype_constraint __LINE__ "LDR-imm-off" rdtypeterm rttypeterm;
                store#add_subtype_constraint rdtypeterm rttypeterm
              end) xrdef);

         (match TR.tmap rewrite_expr (memop#to_expr floc) with
          | Error _ -> ()
          | Ok (XVar v) ->
             (match floc#f#env#get_variable_type v with
              | Some ty ->
                 let opttc = mk_btype_constraint rttypevar ty in
                 (match opttc with
                  | Some tc ->
                     begin
                       log_type_constraint __LINE__ "LDR-memop" tc;
                       store#add_constraint tc
                     end
                  | _ -> ())
              | _ -> ())
          | _ -> ());

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
                          (match opttc with
                           | Some tc ->
                              begin
                                log_type_constraint __LINE__ "LDR-struct-field" tc;
                                store#add_constraint tc
                              end
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
                         (match opttc with
                          | Some tc ->
                             begin
                               log_type_constraint __LINE__ "LDR-array" tc;
                               store#add_constraint tc
                             end
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
             begin
               log_subtype_constraint
                 __LINE__ "LDR-stack-addr" rhstypeterm rttypeterm;
               store#add_subtype_constraint rhstypeterm rttypeterm
             end)
       end

    | LoadRegisterByte (_, rt, rn, rm, _, _) when rm#is_immediate ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin

         (match get_regvar_type_annotation () with
          | Some t ->
            let rtreg = rt#to_register in
            let lhstypevar = mk_reglhs_typevar rtreg faddr iaddr in
            let opttc = mk_btype_constraint lhstypevar t in
            (match opttc with
             | Some tc ->
                begin
                  log_type_constraint __LINE__ "LDRB-rvintro" tc;
                  store#add_constraint tc
                end
             | _ -> ())
          | _ -> ());

         (* LDRB rt, [rn, rm] :  X_rndef.load <: X_rt *)
         (let xrdefs = get_variable_rdefs_r (rn#to_variable floc) in
          let rnreg = rn#to_register in
          let offset = rm#to_numerical#toInt in
          List.iter (fun rdsym ->
              let ldaddr = rdsym#getBaseName in
              let rdtypevar = mk_reglhs_typevar rnreg faddr ldaddr in
              let rdtypevar = add_load_capability ~offset ~size:1 rdtypevar in
              let rdtypeterm = mk_vty_term rdtypevar in
              let rttypeterm = mk_vty_term rttypevar in
              begin
                log_subtype_constraint __LINE__ "LDRB-imm-off" rdtypeterm rttypeterm;
                store#add_subtype_constraint rdtypeterm rttypeterm
              end) xrdefs);

         (* LDRB rt, ...  : X_rt <: integer type *)
         (let tc = mk_int_type_constant Unsigned 8 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          begin
            log_subtype_constraint __LINE__ "LDRB-lhs-byte" tctypeterm rttypeterm;
            store#add_subtype_constraint tctypeterm rttypeterm
          end)

       end

    | LoadRegisterByte (_, rt, _, _, _, _) ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin

         (* LDRB rt, ...  : X_rt <: integer type *)
         (let tc = mk_int_type_constant SignedNeutral 8 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          begin
            log_subtype_constraint __LINE__ "LDRB-lhs-byte" tctypeterm rttypeterm;
            store#add_subtype_constraint tctypeterm rttypeterm
          end)

       end

    | LoadRegisterHalfword (_, rt, rn, rm, memop, _) when rm#is_immediate ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin

         (* loaded type may be known *)
         (let xmem_r = memop#to_expr floc in
          let xrmem_r =
            TR.tmap (fun x -> simplify_xpr (floc#inv#rewrite_expr x)) xmem_r in
          let xtype_r = TR.tbind floc#get_xpr_type xrmem_r in
          TR.titer
            ~ok:(fun t ->
              let opttc = mk_btype_constraint rttypevar t in
              (match opttc with
               | Some tc ->
                  begin
                    log_type_constraint __LINE__ "LDRH-var" tc;
                    store#add_constraint tc
                  end
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
              begin
                log_subtype_constraint __LINE__ "LDRH-imm-off" rdtypeterm rttypeterm;
                store#add_subtype_constraint rdtypeterm rttypeterm
              end) xrdef)
       end

    | LoadRegisterHalfword (_, rt, _, _, _, _) ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin

       (* LDRH rt, ...  : X_rt <: integer type *)
         (let tc = mk_int_type_constant SignedNeutral 16 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          begin
            log_subtype_constraint __LINE__ "LDRB-lhs-byte" tctypeterm rttypeterm;
            store#add_subtype_constraint tctypeterm rttypeterm
          end)

       end

    | LogicalShiftLeft (_, _, rd, rn, rm, _) when rm#is_immediate ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rnreg = rn#to_register in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in

       (* LSL results in an unsigned integer *)
       (let tc = mk_int_type_constant Unsigned 32 in
        let tcterm = mk_cty_term tc in
        let lhstypeterm = mk_vty_term lhstypevar in
        begin
          log_subtype_constraint __LINE__ "LSL-lhs" tcterm lhstypeterm;
          store#add_subtype_constraint tcterm lhstypeterm
        end);

       (* LSL is applied to an unsigned integer *)
       (List.iter (fun rnrdef ->
            let rnaddr = rnrdef#getBaseName in
            let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
            let tyc = mk_int_type_constant Unsigned 32 in
            let tctypeterm = mk_cty_term tyc in
            let rntypeterm = mk_vty_term rntypevar in
            begin
              log_subtype_constraint __LINE__ "LSL-rhs" tctypeterm rntypeterm;
              store#add_subtype_constraint tctypeterm rntypeterm
            end) rndefs)

    | LogicalShiftRight (_, _, rd, rn, rm, _) when rm#is_immediate ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rnreg = rn#to_register in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in

       (* LSR results in an unsigned integer *)
       (let tc = mk_int_type_constant Unsigned 32 in
        let tcterm = mk_cty_term tc in
        let lhstypeterm = mk_vty_term lhstypevar in
        begin
          log_subtype_constraint __LINE__ "LSR-lhs" tcterm lhstypeterm;
          store#add_subtype_constraint tcterm lhstypeterm
        end);

       (* LSR is applied to an unsigned integer *)
       (List.iter (fun rnrdef ->
            let rnaddr = rnrdef#getBaseName in
            let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
            let tyc = mk_int_type_constant Unsigned 32 in
            let tctypeterm = mk_cty_term tyc in
            let rntypeterm = mk_vty_term rntypevar in
            begin
              log_subtype_constraint __LINE__ "LSR-rhs" tctypeterm rntypeterm;
              store#add_subtype_constraint tctypeterm rntypeterm
            end) rndefs)

    | Move (_, _, rd, rm, _, _) when rm#is_immediate ->
       let rmval = rm#to_numerical#toInt in
       (* 0 provides no information about the type *)
       if rmval = 0 then
         ()
       else
         let rdreg = rd#to_register in
         let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
         let tyc = get_intvalue_type_constant rmval in
         let lhstypeterm = mk_vty_term lhstypevar in
         let tctypeterm = mk_cty_term tyc in
         begin
           log_subtype_constraint __LINE__ "MOV-imm" tctypeterm lhstypeterm;
           store#add_subtype_constraint tctypeterm lhstypeterm
         end

    | Move (_, _, rd, rm, _, _) when rd#get_register = rm#get_register ->
    (* exclude to avoid spurious rdefs to get involved *)
       ()

    (* Move x, y  ---  x := y  --- Y <: X *)
    | Move (_, _, rd, rm, _, _) when rm#is_register ->
       let xrm_r = rm#to_expr floc in
       let rdreg = rd#to_register in
       let rdtypevar = mk_reglhs_typevar rdreg faddr iaddr in
       begin

         (* variable introduction for lhs with type *)
         (match get_regvar_type_annotation () with
          | Some t ->
             let opttc = mk_btype_constraint rdtypevar t in
             (match opttc with
              | Some tc ->
                 begin
                   log_type_constraint __LINE__ "MOV-rvintro" tc;
                   store#add_constraint tc
                 end
              | _ -> ())
          | _ -> ());

         (* propagate function argument type *)
         (match getopt_initial_argument_value_r xrm_r with
          | Some (rmreg, off) when off = 0 ->
             let rhstypevar = mk_function_typevar faddr in
             let rhstypevar = add_freg_param_capability rmreg rhstypevar in
             let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
             let rhstypeterm = mk_vty_term rhstypevar in
             let lhstypeterm = mk_vty_term lhstypevar in
             begin
               log_subtype_constraint
                 __LINE__ "MOV-reg-init" rhstypeterm lhstypeterm;
               store#add_subtype_constraint rhstypeterm lhstypeterm
             end
          | _ -> ());

         (* propagate function return type *)
         (if rd#get_register = AR0 && (has_exit_use_r (rd#to_variable floc)) then
            let regvar = mk_reglhs_typevar rdreg faddr iaddr in
            let fvar = mk_function_typevar faddr in
            let fvar = add_return_capability fvar in
            let regterm = mk_vty_term regvar in
            let fterm = mk_vty_term fvar in
            begin
              log_subtype_constraint __LINE__ "MOV-freturn" regterm fterm;
              store#add_subtype_constraint regterm fterm
            end);

         (* use reaching defs *)
         (let rmreg = rm#to_register in
          let rmvar_r = rm#to_variable floc in
          let rmrdefs = get_variable_rdefs_r rmvar_r in
          let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
          List.iter (fun rmrdef ->
              let rmaddr = rmrdef#getBaseName in
              if rmaddr != "init" then
                let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
                let rmtypeterm = mk_vty_term rmtypevar in
                let lhstypeterm = mk_vty_term lhstypevar in
                begin
                  log_subtype_constraint __LINE__ "MOV-reg" rmtypeterm lhstypeterm;
                  store#add_subtype_constraint rmtypeterm lhstypeterm
                end) rmrdefs)
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
              match opttc with
              | Some tc ->
                 begin
                   log_type_constraint __LINE__ "POP-rv" tc;
                   store#add_constraint tc
                 end
              | _ ->
                 begin
                   log_no_type_constraint __LINE__ "POP-rv" rtype;
                   ()
                 end);

             (* propagate via reaching defs *)
             (let r0var = floc#env#mk_arm_register_variable AR0 in
              let r0defs = get_variable_rdefs r0var in
              List.iter (fun r0def ->
                  let r0addr = r0def#getBaseName in
                  if r0addr != "init" then
                    let r0typevar = mk_reglhs_typevar reg faddr r0addr in
                    let r0typeterm = mk_vty_term r0typevar in
                    let lhstypeterm = mk_vty_term typevar in
                    begin
                      log_subtype_constraint
                        __LINE__ "POP-R0-rdef" r0typeterm lhstypeterm;
                      store#add_subtype_constraint r0typeterm lhstypeterm
                    end) r0defs)
             end)

    | Push _
      | Pop _ ->
       (* no type information gained *)
       ()

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
       begin
         store#add_subtype_constraint tctypeterm lhslotypeterm;
         store#add_subtype_constraint tctypeterm lhshitypeterm;

         (List.iter (fun rnrdef ->
              let rnaddr = rnrdef#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
              let rntypeterm = mk_vty_term rntypevar in
              store#add_subtype_constraint tctypeterm rntypeterm) rndefs);

         (List.iter (fun rmrdef ->
              let rmaddr = rmrdef#getBaseName in
              let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
              let rmtypeterm = mk_vty_term rmtypevar in
              store#add_subtype_constraint tctypeterm rmtypeterm) rmdefs)
       end

    (* Store x in y  ---  *y := x  --- X <: Y.store *)
    | StoreRegister (_, rt, rn, rm, memvarop, _) when rm#is_immediate ->
       let rnrdefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       let offset = rm#to_numerical#toInt in
       let rtrdefs = get_variable_rdefs_r (rt#to_variable floc) in
       let rtreg = rt#to_register in
       let xaddr_r = memvarop#to_address floc in
       let xrt_r = rt#to_expr floc in
       begin

         (match getopt_stackaddress_r xaddr_r with
          | None -> ()
          | Some offset ->
             let lhstypevar = mk_localstack_lhs_typevar offset faddr iaddr in
             begin
               (* propagate function argument type *)
               (match getopt_initial_argument_value_r xrt_r with
                | Some (rtreg, off) when off = 0 ->
                   let rhstypevar = mk_function_typevar faddr in
                   let rhstypevar = add_freg_param_capability rtreg rhstypevar in
                   let rhstypeterm = mk_vty_term rhstypevar in
                   let lhstypeterm = mk_vty_term lhstypevar in
                   begin
                     log_subtype_constraint
                       __LINE__ "STR-funarg" rhstypeterm lhstypeterm;
                     store#add_subtype_constraint rhstypeterm lhstypeterm
                   end
                | _ -> ());

               (* propagate src register type from rdefs *)
               (let rtreg = rt#to_register in
                let rtvar_r = rt#to_variable floc in
                let rtrdefs = get_variable_rdefs_r rtvar_r in
                List.iter (fun rtrdef ->
                    let rtaddr = rtrdef#getBaseName in
                    if rtaddr != "init" then
                      let rttypevar = mk_reglhs_typevar rtreg faddr rtaddr in
                      let rttypeterm = mk_vty_term rttypevar in
                      let lhstypeterm = mk_vty_term lhstypevar in
                      begin
                        log_subtype_constraint
                          __LINE__ "STR-imm-off" rttypeterm lhstypeterm;
                        store#add_subtype_constraint rttypeterm lhstypeterm
                      end) rtrdefs);

                 (* import type from stackvar-introductions *)
                 (match get_stackvar_type_annotation offset with
                  | None -> ()
                  | Some t ->
                     let lhstypevar =
                       mk_localstack_lhs_typevar offset faddr iaddr in
                     let opttc = mk_btype_constraint lhstypevar t in
                     (match opttc with
                      | Some tc ->
                         begin
                           log_type_constraint __LINE__ "STR-stack-vintro" tc;
                           store#add_constraint tc
                         end
                      | _ -> ()))
             end);

         (List.iter (fun rndsym ->
              let straddr = rndsym#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr straddr in
              let rntypevar = add_load_capability ~size:4 ~offset rntypevar in
              List.iter (fun rtdsym ->
                  let rtdloc = rtdsym#getBaseName in
                  let rttypevar = mk_reglhs_typevar rtreg faddr rtdloc in
                  let rttypeterm = mk_vty_term rttypevar in
                  let rntypeterm = mk_vty_term rntypevar in
                  begin
                    log_subtype_constraint
                      __LINE__ "STR-imm-off" rttypeterm rntypeterm;
                    store#add_subtype_constraint rttypeterm rntypeterm
                  end) rtrdefs) rnrdefs)
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
          begin
            log_subtype_constraint __LINE__ "STRB-rhs-byte" tctypeterm rttypeterm;
            store#add_subtype_constraint tctypeterm rttypeterm
          end);

         (List.iter (fun rndsym ->
              let straddr = rndsym#getBaseName in
              let rntypevar = mk_reglhs_typevar rnreg faddr straddr in
              let rntypevar = add_load_capability ~size:1 ~offset rntypevar in
              List.iter (fun rtdsym ->
                  let rtdloc = rtdsym#getBaseName in
                  let rttypevar = mk_reglhs_typevar rtreg faddr rtdloc in
                  let rttypeterm = mk_vty_term rttypevar in
                  let rntypeterm = mk_vty_term rntypevar in
                  begin
                    log_subtype_constraint
                      __LINE__"STRB-imm-off" rttypeterm rntypeterm;
                    store#add_subtype_constraint rttypeterm rntypeterm
                  end) rtrdefs) rnrdefs)

       end

    | StoreRegisterByte (_, rt, _, _, _, _) ->
       let rtreg = rt#to_register in
       let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
       begin

         (* STRB rt, ...  : X_rt <: integer type *)
         (let tc = mk_int_type_constant SignedNeutral 8 in
          let tctypeterm = mk_cty_term tc in
          let rttypeterm = mk_vty_term rttypevar in
          begin
            log_subtype_constraint __LINE__ "STRB-rhs-byte" tctypeterm rttypeterm;
            store#add_subtype_constraint tctypeterm rttypeterm
          end)

       end

    | Subtract (_, _, rd, rn, _, _, _) ->
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let rndefs = get_variable_rdefs_r (rn#to_variable floc) in
       let rnreg = rn#to_register in
       begin

         (* Note: Does not take into consideration the possibility of the
            subtraction of two pointers *)
         List.iter (fun rnsym ->
             let rnaddr = rnsym#getBaseName in
             let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
             let rntypeterm = mk_vty_term rntypevar in
             let lhstypeterm = mk_vty_term lhstypevar in
             begin
               log_subtype_constraint __LINE__ "SUB-rdef-1" rntypeterm lhstypeterm;
               store#add_subtype_constraint rntypeterm lhstypeterm
             end) rndefs;

         (* propagate function return type *)
         (if rd#get_register = AR0 && (has_exit_use_r (rd#to_variable floc)) then
            let regvar = mk_reglhs_typevar rdreg faddr iaddr in
            let fvar = mk_function_typevar faddr in
            let fvar = add_return_capability fvar in
            let regterm = mk_vty_term regvar in
            let fterm = mk_vty_term fvar in
            begin
              log_subtype_constraint __LINE__ "SUB-freturn" regterm fterm;
              store#add_subtype_constraint regterm fterm
            end);

       end

    | UnsignedBitFieldExtract (_, _, rn) ->
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
                  begin
                    log_subtype_constraint __LINE__ "UBFX-rhs" tctypeterm rntypeterm;
                    store#add_subtype_constraint tctypeterm rntypeterm
                  end) rndefs)
           end
        | _ -> ())

    | UnsignedExtendHalfword (_, rd, _, _) ->
       let rdreg = rd#to_register in
       let rdtypevar = mk_reglhs_typevar rdreg faddr iaddr in
       begin
         (match get_regvar_type_annotation () with
          | Some t ->
             let opttc = mk_btype_constraint rdtypevar t in
             (match opttc with
              | Some tc ->
                 begin
                   log_type_constraint __LINE__ "UXTH-rvintro" tc;
                   store#add_constraint tc
                 end
              | _ ->
                 let opttc = mk_btype_constraint rdtypevar t_short in
                 (match opttc with
                  | Some tc -> store#add_constraint tc
                  | _ -> ())
             )
          | _ ->
             let opttc = mk_btype_constraint rdtypevar t_short in
             (match opttc with
              | Some tc -> store#add_constraint tc
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

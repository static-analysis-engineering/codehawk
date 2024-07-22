(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open XprUtil
open Xsimplify

(* bchlib *)
open BCHBasicTypes
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
open BCHSystemInfo
open BCHTypeConstraintStore
open BCHTypeConstraintUtil

(* bchlibarm *)
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMTypes

module TR = CHTraceResult

let x2p = xpr_formatter#pr_expr


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

  method record_type_constraints =
    let fintf = finfo#get_summary#get_function_interface in
    begin
      record_function_interface_type_constraints store faddr fintf;
      fn#itera
        (fun baddr block ->
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
    let rdefs_to_pretty (syms: symbol_t list) =
      pretty_print_list syms (fun s -> s#toPretty) "[" "; " "]" in

    let rdef_pairs_to_pretty (pairs: (symbol_t * symbol_t) list) =
      pretty_print_list
        pairs
        (fun (s1, s2) ->
          LBLOCK [STR "("; s1#toPretty; STR ", "; s2#toPretty; STR ")"])
        "[" "; " "]" in

    let get_intvalue_type_constant ?(signed=true) (i: int): type_constant_t =
      match mk_intvalue_type_constant i with
      | Some tc -> tc
      | _ when signed -> mk_int_type_constant IInt
      | _ -> mk_int_type_constant IUInt in

    let get_variable_rdefs (v: variable_t): symbol_t list =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = floc#varinv#get_var_reaching_defs symvar in
      (match varinvs with
       | [vinv] -> vinv#get_reaching_defs
       | _ -> []) in

    let get_variable_defuses (v: variable_t): symbol_t list =
      let symvar = floc#f#env#mk_symbolic_variable v in
      let varinvs = floc#varinv#get_var_def_uses symvar in
      (match varinvs with
       | [vinv] -> vinv#get_def_uses
       | _ -> []) in

    let has_exit_use (v: variable_t): bool =
      let defuses = get_variable_defuses v in
      List.exists (fun s -> s#getBaseName = "exit") defuses in

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

    match instr#get_opcode with

    | BitwiseNot(_, _, rd, rm, _) when rm#is_immediate ->
       let rmval = rm#to_numerical#toInt in
       let rdreg = rd#to_register in
       let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
       let intkind = if rmval = 0 then IInt else IUInt in
       let tyc = mk_int_type_constant intkind in
       store#add_subtype_constraint (mk_cty_term tyc) (mk_vty_term lhstypevar)

    | BranchLink _
         when floc#has_call_target && floc#get_call_target#is_signature_valid ->
       let callargs = floc#get_call_arguments in
       let (rvreg, rtype) =
         let fintf = floc#get_call_target#get_function_interface in
         let rtype = get_fts_returntype fintf in
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
            let opttc = mk_btype_constraint typevar rtype in
            match opttc with
            | Some tc -> store#add_constraint  tc
            | _ -> ());

         (* add constraints for argument values *)
         List.iter (fun (p, x) ->
             if is_register_parameter p then
               let regarg = TR.tget_ok (get_register_parameter_register p) in
               let pvar = floc#f#env#mk_register_variable regarg in
               let rdefs = get_variable_rdefs pvar in
               let ptype = get_parameter_type p in
               begin
                 (if not (is_unknown_type ptype) then
                    List.iter (fun rdsym ->
                        let typevar =
                          mk_reglhs_typevar regarg faddr rdsym#getBaseName in
                        let opttc = mk_btype_constraint typevar ptype in
                        match opttc with
                        | Some tc -> store#add_constraint tc
                        | _ -> ()) rdefs);

                 (match getopt_stackaddress x with
                  | None -> ()
                  | Some offset ->
                     let lhstypevar =
                       mk_localstack_lhs_typevar offset faddr iaddr in
                     if is_pointer ptype then
                       let eltype = ptr_deref ptype in
                       let atype = t_array eltype 1 in
                       let opttc = mk_btype_constraint lhstypevar atype in
                       match opttc with
                       | Some tc -> store#add_constraint tc
                       | _ -> ())
               end
           ) callargs

       end

    | Compare (_, rn, rm, _) when rm#is_immediate ->
       let rndefs = get_variable_rdefs (rn#to_variable floc) in
       let rnreg = rn#to_register in
       let immval = rm#to_numerical#toInt in
       if immval = 0 then
         ()
       else
         let _ =
           chlog#add
             "type constraints: compare"
             (LBLOCK [STR iaddr; STR " (immediate): "; rdefs_to_pretty rndefs]) in
         List.iter (fun rnsym ->
             let rnaddr = rnsym#getBaseName in
             let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
             let immtypeconst = get_intvalue_type_constant immval in
             store#add_subtype_constraint
               (mk_vty_term rntypevar) (mk_cty_term immtypeconst)) rndefs

    | Compare (_, rn, rm, _) when rm#is_register ->
       let rndefs = get_variable_rdefs (rn#to_variable floc) in
       let rmdefs = get_variable_rdefs (rm#to_variable floc) in
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
              store#add_subtype_constraint
                (mk_vty_term rntypevar) (mk_vty_term rmtypevar)) pairs);
         (let xrn = rn#to_expr floc in
          match getopt_initial_argument_value xrn with
          | Some (reg, _) ->
             let ftvar = mk_function_typevar faddr in
             let ftvar = add_freg_param_capability reg ftvar in
             List.iter (fun rmsym ->
                 let rmaddr = rmsym#getBaseName in
                 let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
                 store#add_subtype_constraint
                   (mk_vty_term ftvar) (mk_vty_term rmtypevar)) rmdefs
          | _ -> ());
         (let xrm = rm#to_expr floc in
          match getopt_initial_argument_value xrm with
          | Some (reg, _) ->
             let ftvar = mk_function_typevar faddr in
             let ftvar = add_freg_param_capability reg ftvar in
             List.iter (fun rnsym ->
                 let rnaddr = rnsym#getBaseName in
                 let rntypevar = mk_reglhs_typevar rnreg faddr rnaddr in
                 store#add_subtype_constraint
                   (mk_vty_term ftvar) (mk_vty_term rntypevar)) rndefs
          | _ -> ())
       end

    | LoadRegister (_, rt, rn, rm, memop, _) when rm#is_immediate ->
       begin
         (* LDR rt, [rn, rm] :  X_rndef.load <: X_rt *)
         (let xrdef = get_variable_rdefs (rn#to_variable floc) in
          let rtreg = rt#to_register in
          let rnreg = rn#to_register in
          let offset = rm#to_numerical#toInt in
          List.iter (fun rdsym ->
              let ldaddr = rdsym#getBaseName in
              let rdtypevar = mk_reglhs_typevar rnreg faddr ldaddr in
              let rdtypevar = add_load_capability ~offset rdtypevar in
              let rttypevar = mk_reglhs_typevar rtreg faddr iaddr in
              store#add_subtype_constraint
                (mk_vty_term rdtypevar) (mk_vty_term rttypevar)) xrdef);

       end

    (* Move x, y  ---  x := y  --- Y <: X *)
    | Move (_, _, rd, rm, _, _) ->
       let xrm = rm#to_expr floc in
       let rdreg = rd#to_register in
       begin
         (* propagate function argument type *)
         (match getopt_initial_argument_value xrm with
          | Some (rmreg, off) when off = 0 ->
             let rhstypevar = mk_function_typevar faddr in
             let rhstypevar = add_freg_param_capability rmreg rhstypevar in
             let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
             store#add_subtype_constraint
               (mk_vty_term rhstypevar) (mk_vty_term lhstypevar)
          | _ -> ());

         (* propagate function return type *)
         (if rd#get_register = AR0 then
            let regvar = mk_reglhs_typevar rdreg faddr iaddr in
            if has_exit_use (rd#to_variable floc) then
              let fvar = mk_function_typevar faddr in
              let fvar = add_return_capability fvar in
              store#add_subtype_constraint
                (mk_vty_term regvar) (mk_vty_term fvar)
            else
              ());

         (* use constant-value type *)
         (if rm#is_immediate then
            let rmval = rm#to_numerical#toInt in
            if rmval = 0 then
              ()
            else
              let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
              let tyc = get_intvalue_type_constant rmval in
              store#add_subtype_constraint
                (mk_cty_term tyc) (mk_vty_term lhstypevar));

         (* use reaching defs *)
         (if rm#is_register then
            let rmreg = rm#to_register in
            let rmvar = rm#to_variable floc in
            let rmrdefs = get_variable_rdefs rmvar in
            let lhstypevar = mk_reglhs_typevar rdreg faddr iaddr in
            List.iter (fun rmrdef ->
                let rmaddr = rmrdef#getBaseName in
                if rmaddr != "init" then
                  let rmtypevar = mk_reglhs_typevar rmreg faddr rmaddr in
                  store#add_subtype_constraint
                    (mk_vty_term rmtypevar) (mk_vty_term lhstypevar)) rmrdefs)
       end

    | _ -> ()


end


let  mk_arm_fn_type_constraints
       (store: type_constraint_store_int)
       (fn: arm_assembly_function_int): arm_fn_type_constraints_int =
  new arm_fn_type_constraints_t store fn

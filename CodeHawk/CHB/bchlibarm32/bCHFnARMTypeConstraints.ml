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

(* chutil *)
open CHLogger

(* xprlib *)
open XprToPretty
open XprTypes
open Xsimplify
   
(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHDoubleword
open BCHFloc
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation
open BCHSystemInfo
open BCHTypeConstraintStore
   
(* bchlibarm *)
open BCHARMOpcodeRecords
open BCHARMTypes

module TR = CHTraceResult

let x2p = xpr_formatter#pr_expr          


let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("FnARMTypeConstraints:" ^ tag) msg


class arm_fn_type_constraints_t
        (store: type_constraint_store_int)
        (fn: arm_assembly_function_int): arm_fn_type_constraints_int =
object (self)

  val faddr = fn#get_address
  val finfo = get_function_info fn#get_address
  val env = (get_function_info fn#get_address)#env

  method record_type_constraints =
    fn#itera
      (fun baddr block ->
        block#itera
          (fun ctxtiaddr instr ->
            self#record_instr_type_constraints ctxtiaddr instr))

  method private record_instr_type_constraints
                   (iaddr: ctxt_iaddress_t) (instr: arm_assembly_instruction_int) =
    let loc = ctxt_string_to_location faddr iaddr in
    let floc = get_floc loc in
    let rewrite_expr (x: xpr_t): xpr_t =
      let x = floc#inv#rewrite_expr x in
      simplify_xpr x in
    let rewrite_expr_loc (x: xpr_t) (floci: floc_int) =
      let x = floci#inv#rewrite_expr x in
      simplify_xpr x in
    let rewrite_test_expr (csetter: ctxt_iaddress_t) (x: xpr_t) =
      let testloc = ctxt_string_to_location floc#fa csetter in
      let testfloc = get_floc testloc in
      let rec expand x =
        match x with
        | XVar v when testfloc#env#is_symbolic_value v ->
           expand (TR.tget_ok (testfloc#env#get_symbolic_value_expr v))
        | XOp (op,l) -> XOp (op, List.map expand l)
        | _ -> x in
      let xpr = testfloc#inv#rewrite_expr x in
      simplify_xpr (expand xpr) in
    let is_return_value (x: xpr_t) =
      match (rewrite_expr x) with
      | XVar v -> floc#f#env#is_return_value v
      | _ -> false in
    
    let get_calltarget_from_callsite (callsite: ctxt_iaddress_t) =
      let siteloc = ctxt_string_to_location faddr callsite in
      let sitefloc = get_floc siteloc in
      let instr = fn#get_instruction siteloc#i in
      match instr#get_opcode with
      | BranchLink (_, tgt) when tgt#is_absolute_address ->
         Some tgt#get_absolute_address
      | BranchLink _ | BranchLinkExchange _ when sitefloc#has_call_target ->
         let calltarget = sitefloc#get_call_target#get_target in
         (match calltarget with
          | AppTarget dw -> Some dw
          | _ -> None)
      | _ -> None in
    
    let get_calltarget (x: xpr_t) =
      match (rewrite_expr x) with
      | XVar v when floc#env#is_return_value v ->
         log_tfold
           (log_error "record_instr_type_constraints" "invalid call site")
         ~ok:(fun callsite ->
           let siteloc = ctxt_string_to_location faddr callsite in
           let sitefloc = get_floc loc in
           let instr = fn#get_instruction siteloc#i in
           let _ =
             chlog#add "callsite instr" instr#toPretty in
           (match instr#get_opcode with
            | BranchLink (_, tgt) when tgt#is_absolute_address ->
               Some tgt#get_absolute_address
            | BranchLink _ | BranchLinkExchange _ when sitefloc#has_call_target ->
               let calltarget = sitefloc#get_call_target#get_target in
               (match calltarget with
                | AppTarget dw -> Some dw
                | _ -> None)
            | _ -> None))
         ~error:(fun _ -> None)
         (floc#env#get_call_site v)
      | _ -> None in
      
    let get_intvalue_type_constant (x: xpr_t): type_constant_t option =
      match (rewrite_expr x) with
      | XConst (IntConst n) -> mk_intvalue_type_constant n#toInt
      | _ -> None in
    
    let is_zero (x: xpr_t) =
      match (rewrite_expr x) with
      | XConst (IntConst n) -> n#equal numerical_zero
      | _ -> false in

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

    let get_optreturn_caps (x: xpr_t):
          (doubleword_int * type_cap_label_t list) option =
      match (rewrite_expr x) with
      | XVar v ->
         (match floc#f#env#get_optreturn_value_capabilities v with
          | Some (callsite, caps) ->
             let optcalltgt = get_calltarget_from_callsite callsite in
             (match optcalltgt with
              | Some dw -> Some (dw, caps)
              | _ -> None)
          | _ -> None)
      | _ -> None in               

    let is_initial_memory_value (x: xpr_t) =
      match (rewrite_expr x) with
      | XVar v -> floc#f#env#is_initial_memory_value v
      | _ -> false in

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

    let get_rdef (xpr: xpr_t) =
      match (rewrite_expr xpr) with
      | XVar v
        | XOp (XXlsh, [XVar v])
        | XOp (XXlsb, [XVar v])
        | XOp (XXbyte, [_; XVar v])
        | XOp (XLsr, [XVar v; _])
        | XOp (XLsl, [XVar v; _]) ->
         let symvar = floc#f#env#mk_symbolic_variable v in
         floc#varinv#get_var_reaching_defs symvar
      | _ -> [] in

    let set_optrdef_type
          ~(op: arm_operand_int)
          ~(rdefs: symbol_t list)
          ~(is_load: bool)
          ~(size: int)
          ~(offset: int) =
      match List.map (fun d -> d#getBaseName) rdefs with
      | [iaddr1; iaddr2] ->
         let loc1 = ctxt_string_to_location faddr iaddr1 in
         let loc2 = ctxt_string_to_location faddr iaddr2 in
         let floc1 = get_floc loc1 in
         let floc2 = get_floc loc2 in
         let instr1 = fn#get_instruction loc1#i in
         let instr2 = fn#get_instruction loc2#i in
         (match (instr1#get_opcode, instr2#get_opcode) with
          | (Add (_, _, rd1, rn1, rm1, _),
             Add (_, _, rd2, rn2, rm2, _))
               when rd1#get_register = op#get_register
                    && rd2#get_register = op#get_register
                    && rn2#get_register = op#get_register
                    && rm2#is_immediate
                    && rm2#to_numerical#toInt = size ->
             let xrn1 = rn1#to_expr floc1 in
             let xrm1 = rm1#to_expr floc1 in
             let res1 = XOp (XPlus, [xrn1; xrm1]) in
             let rres1 = rewrite_expr_loc res1 floc1 in
             (match getopt_initial_argument_value rres1 with
              | Some (reg, off) ->
                 let offset = offset + off in
                 let typevar =
                   if is_load then
                     mk_regparam_load_array_typevar ~size ~offset faddr reg
                   else
                     mk_regparam_store_array_typevar ~size ~offset faddr reg in
                 store#add_var_constraint typevar
              | _ -> ())
          | _ -> ())
      | _ -> () in
    
    let get_initial_memory_value_variable (x: xpr_t) =
      try
        match (rewrite_expr x) with
        | XVar v ->
           Some (floc#f#env#varmgr#get_initial_memory_value_variable v)
        | _ -> None
      with
      | _ -> None in
    
    match instr#get_opcode with

    | Branch (c, _, _)
         when is_cond_conditional c && floc#has_test_expr ->
       let txpr = floc#get_test_expr in
       let csetter = floc#f#get_associated_cc_setter floc#cia in
       let tcond = rewrite_test_expr csetter txpr in
       (match tcond with
        | XOp ((XEq | XNe), [x1; x2]) ->
           let opttypevar =
             if is_return_value x1 then
               (match get_calltarget x1 with
                | Some dw -> Some (mk_function_return_typevar dw)
                | _ -> None)
             else
               match getopt_initial_argument_value x1 with
               | Some (reg, 0) -> Some (mk_regparam_typevar faddr reg)
               | _ ->
                  match get_optreturn_caps x2 with
                  | Some (dw, caps) ->
                     Some (mk_function_return_typevar dw)
                  | _ -> None in
           (match opttypevar with
            | Some typevar ->
               if is_zero x2 then
                 store#add_zerocheck_constraint typevar
               else
                 (match get_intvalue_type_constant x2 with
                  | Some tycst -> store#add_cv_subtype_constraint tycst typevar
                  | _ -> store#add_var_constraint typevar)
            | _ -> ())
        | _ -> ())

    | BranchLink (_, tgt)
         when floc#has_call_target && floc#get_call_target#is_signature_valid ->
       let args = List.map snd floc#get_call_arguments in
       let args = List.map rewrite_expr args in
       let regargs =
         match List.length(args) with
         | 0 -> []
         | 1 -> [AR0]
         | 2 -> [AR0; AR1]
         | 3 -> [AR0; AR1; AR2]
         | _ -> [AR0; AR1; AR2; AR3] in
       let registers = List.map register_of_arm_register regargs in
       let args =
         if (List.length args ) > 4 then
           match args with
           | a1 :: a2 :: a3 :: a4 :: _ -> [a1; a2; a3; a4]
           | _ -> args
         else
           args in
       let tgtaddr = tgt#get_absolute_address in
       List.iter2 (fun par arg ->
           let typevar2 = mk_regparam_typevar tgtaddr par in
           match getopt_initial_argument_value arg with
           | Some (reg, 0) ->
              let typevar1 = mk_regparam_typevar faddr reg in
              store#add_subtype_constraint typevar1 typevar2
           | _ ->
              if is_return_value arg then
                (match get_calltarget arg with
                 | Some dw ->
                    let typevar1 = mk_function_return_typevar dw in
                    store#add_subtype_constraint typevar1 typevar2
                 | _ -> ())
              else
                (match get_intvalue_type_constant arg with
                 | Some tycst ->
                    store#add_cv_subtype_constraint tycst typevar2
                 | _ ->
                    (match getopt_stackaddress arg with
                     | Some offset ->
                        let typevar1 = mk_stackaddress_typevar faddr offset in
                        store#add_subtype_constraint typevar1 typevar2
                     | _ -> ()))) registers args

    | LoadRegister (_, _, rn, rm, memop, _) when rm#is_immediate ->
       let xrn = rn#to_expr floc in
       (match getopt_initial_argument_value xrn with
        | Some (reg, off) ->
           let offset = rm#to_numerical#toInt + off in
           let typevar = mk_regparam_load_typevar ~offset faddr reg in
           store#add_var_constraint typevar
        | _ ->
           if is_return_value xrn then
             (match get_calltarget xrn with
              | Some dw ->
                 let offset = rm#to_numerical#toInt in
                 let typevar = mk_function_return_load_typevar ~offset dw in
                 store#add_var_constraint typevar
              | _ -> ())
           else if memop#is_literal_address then
             let addr = memop#get_literal_address in
             let typevar = mk_data_address_load_typevar addr in
             store#add_var_constraint typevar
           else
             ())

    | LoadRegisterByte (_, _, rn, rm, _, _) when rm#is_immediate ->
       let xrn = rn#to_expr floc in
       (match getopt_initial_argument_value xrn with
        | Some (reg, off) ->
           let offset = rm#to_numerical#toInt + off in
           let typevar = mk_regparam_load_typevar ~size:1 ~offset faddr reg in
           store#add_var_constraint typevar
        | _ ->
           if is_return_value xrn then
             (match get_calltarget xrn with
              | Some dw ->
                 let offset = rm#to_numerical#toInt in
                 let typevar =
                   mk_function_return_load_typevar ~size:1 ~offset dw in
                 store#add_var_constraint typevar
              | _ -> ())
           else
             let rdefinv = get_rdef xrn in
             match rdefinv with
             | [vinv] ->
                let rdefs = vinv#get_reaching_defs in
                set_optrdef_type
                  ~op:rn
                  ~rdefs
                  ~is_load:true ~size:1
                  ~offset:rm#to_numerical#toInt
             | _ -> ())
                

    | LoadRegisterHalfword (_, _, rn, rm, _, _) when rm#is_immediate ->
       let xrn = rn#to_expr floc in
       (match getopt_initial_argument_value xrn with
        | Some (reg, off) ->
           let offset = rm#to_numerical#toInt + off in
           let typevar = mk_regparam_load_typevar ~size:2 ~offset faddr reg in
           store#add_var_constraint typevar
        | _ ->
           if is_return_value xrn then
             (match get_calltarget xrn with
              | Some dw ->
                 let offset = rm#to_numerical#toInt in
                 let typevar =
                   mk_function_return_load_typevar ~size: 2 ~offset dw in
                 store#add_var_constraint typevar
              | _ -> ())
           else
             ())

    | StoreRegister (_, rt, rn, rm, _, _) when rm#is_immediate ->
       let xrn = rn#to_expr floc in
       (match getopt_initial_argument_value xrn with
        | Some (reg, off) ->
           let offset = rm#to_numerical#toInt + off in
           let typevar = mk_regparam_store_typevar ~offset faddr reg in
           let xrt = rt#to_expr floc in
           (match get_intvalue_type_constant xrt with
            | Some tycst -> store#add_cv_subtype_constraint tycst typevar
            | _ -> store#add_var_constraint typevar)
        | _ ->
           if is_return_value xrn then
             (match get_calltarget xrn with
              | Some dw ->
                 let offset = rm#to_numerical#toInt in
                 let typevar = mk_function_return_store_typevar ~offset dw in
                 let xrt = rt#to_expr floc in
                 (match get_intvalue_type_constant xrt with
                  | Some tycst -> store#add_cv_subtype_constraint tycst typevar
                  | _ -> store#add_var_constraint typevar)
              | _ -> ())
           else
             ())

    | StoreRegisterByte (_, rt, rn, rm, _, _) when rm#is_immediate ->
       let xrn = rn#to_expr floc in
       (match getopt_initial_argument_value xrn with
        | Some (reg, off) ->
           let offset = rm#to_numerical#toInt + off in
           let typevar = mk_regparam_store_typevar ~size:1 ~offset faddr reg in
           let xrt = rt#to_expr floc in
           (match get_intvalue_type_constant xrt with
            | Some tycst -> store#add_cv_subtype_constraint tycst typevar
            | _ -> store#add_var_constraint typevar)
        | _ ->
           if is_return_value xrn then
             (match get_calltarget xrn with
              | Some dw ->
                 let offset = rm#to_numerical#toInt in
                 let typevar =
                   mk_function_return_store_typevar ~size:1 ~offset dw in
                 let xrt = rt#to_expr floc in
                 (match get_intvalue_type_constant xrt with
                  | Some tycst -> store#add_cv_subtype_constraint tycst typevar
                  | _ -> store#add_var_constraint typevar)
              | _ -> ())
           else
             let xrt = rt#to_expr floc in
             match getopt_initial_argument_value xrt with
             | Some (reg, 0) ->
                let typevar = mk_regparam_typevar faddr reg in
                store#add_var_constraint typevar
             | _ -> ())
       
    | StoreRegisterHalfword (_, rt, rn, rm, _, _) when rm#is_immediate ->
       let xrn = rn#to_expr floc in
       (match getopt_initial_argument_value xrn with
        | Some (reg, off) ->
           let offset = rm#to_numerical#toInt + off in
           let typevar = mk_regparam_store_typevar ~size:2 ~offset faddr reg in
           let xrt = rt#to_expr floc in
           (match get_intvalue_type_constant xrt with
            | Some tycst -> store#add_cv_subtype_constraint tycst typevar
            | _ -> store#add_var_constraint typevar)
        | _ ->
           if is_return_value xrn then
             (match get_calltarget xrn with
              | Some dw ->
                 let offset = rm#to_numerical#toInt in
                 let typevar =
                   mk_function_return_store_typevar ~size:2 ~offset dw in
                 let xrt = rt#to_expr floc in
                 (match get_intvalue_type_constant xrt with
                  | Some tycst -> store#add_cv_subtype_constraint tycst typevar
                  | _ -> store#add_var_constraint typevar)
              | _ -> ())
           else
             ())

    | StoreRegister (_, rt, _, _, mem, _) ->
       let xaddr = mem#to_address floc in
       let xrt = rt#to_expr floc in
       (match xaddr with
        | XConst (IntConst n) ->
           let dw = TR.tget_ok (numerical_to_doubleword n) in
           let typevar = mk_data_address_store_typevar dw in
           begin
             store#add_var_constraint typevar;
             (match get_intvalue_type_constant xrt with
              | Some tycst ->
                 store#add_cv_subtype_constraint tycst (mk_gvar_type_var dw)
              | _ -> ())
           end
        | _ -> ())
    | _ -> ()
                               

end


let  mk_arm_fn_type_constraints
       (store: type_constraint_store_int)
       (fn: arm_assembly_function_int): arm_fn_type_constraints_int =
  new arm_fn_type_constraints_t store fn

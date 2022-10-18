(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHPretty
open CHCommon
open CHNumerical
open CHLanguage
open CHUtils

(* chutil *)
open CHLogger

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open XprUtil
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHCallTarget
open BCHCodegraph
open BCHCPURegisters
open BCHDoubleword
open BCHFloc
open BCHFtsParameter
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummary
open BCHLibTypes
open BCHLocation
open BCHMemoryReference
open BCHSpecializations
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities
open BCHVariable
open BCHVariableType

(* bchlibarm32 *)
open BCHARMAssemblyBlock
open BCHARMAssemblyFunction
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMCHIFSystem
open BCHARMCodePC
open BCHARMConditionalExpr
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMTypes
open BCHDisassembleARM

module B = Big_int_Z
module LF = CHOnlineCodeSet.LanguageFactory

let valueset_domain = "valuesets"
let x2p = xpr_formatter#pr_expr
let cmd_to_pretty = CHLanguage.command_to_pretty 0

let make_code_label ?src ?modifier (address:ctxt_iaddress_t) =
  let name =
    if address = "exit" || address = "?" then
      "exit"
    else
      "pc_" ^ address in
  let atts = match modifier with
    | Some s -> [s]
    | _ -> [] in
  let atts =
    if address = "?" then
      "unresolved-jump" :: atts
    else
      atts in
  let atts = match src with
    | Some s -> s#to_fixed_length_hex_string :: atts | _ -> atts in
  ctxt_string_to_symbol name ~atts address

let get_invariant_label ?(bwd=false) (loc:location_int) =
  if bwd then
    ctxt_string_to_symbol "bwd-invariant" loc#ci
  else
    ctxt_string_to_symbol "invariant" loc#ci


let make_instruction_operation
      ?(atts=[])
      (opname: string)
      (address: string)
      (op_args: (string * variable_t * arg_mode_t) list) =
  let op_name = new symbol_t ~atts:(address :: atts) opname in
  OPERATION {op_name = op_name; op_args = op_args}


let package_transaction
      (finfo:function_info_int) (label:symbol_t) (cmds:cmd_t list) =
  let cmds =
    List.filter
      (fun cmd -> match cmd with SKIP -> false | _ -> true) cmds in
  let cnstAssigns = finfo#env#end_transaction in
  TRANSACTION (label, LF.mkCode (cnstAssigns @ cmds), None)


let make_conditional_predicate
      ~(condinstr: arm_assembly_instruction_int)
      ~(testinstr: arm_assembly_instruction_int)
      ~(condloc: location_int)
      ~(testloc: location_int) =
  let (frozenvars, optxpr) =
    arm_conditional_expr
      ~condopc:condinstr#get_opcode
      ~testopc:testinstr#get_opcode
      ~condloc:condloc
      ~testloc:testloc in
  (frozenvars, optxpr)


let make_instr_local_tests
    ~(condinstr:arm_assembly_instruction_int)
    ~(testinstr:arm_assembly_instruction_int)
    ~(condloc:location_int)
    ~(testloc:location_int) =
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
  let env = testfloc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let (frozenVars, optboolxpr) =
    if is_opcode_conditional testinstr#get_opcode then
      let finfo = testfloc#f in
      let faddr = testfloc#fa in
      if finfo#has_associated_cc_setter testloc#ci then
        let testtestiaddr = finfo#get_associated_cc_setter testloc#ci in
        let testtestloc = ctxt_string_to_location faddr testtestiaddr in
        let testtestaddr = testtestloc#i in
        let testtestinstr = !arm_assembly_instructions#at_address testtestaddr in
        let _ =
          chlog#add
            "conditional conditional test"
            (LBLOCK [
                 testfloc#l#toPretty;
                 STR ": ";
                 STR (arm_opcode_to_string testinstr#get_opcode);
                 STR " with setter ";
                 STR (arm_opcode_to_string testtestinstr#get_opcode)]) in
        arm_conditional_conditional_expr
          ~condopc:condinstr#get_opcode
          ~testopc: testinstr#get_opcode
          ~testtestopc: testtestinstr#get_opcode
          ~condloc
          ~testloc
          ~testtestloc
      else
        arm_conditional_expr
          ~condopc:condinstr#get_opcode
          ~testopc:testinstr#get_opcode
          ~condloc
          ~testloc
    else
      arm_conditional_expr
        ~condopc:condinstr#get_opcode
        ~testopc:testinstr#get_opcode
        ~condloc
        ~testloc in
(*  let (frozenVars, optboolxpr) =
    arm_conditional_expr
      ~condopc:condinstr#get_opcode
      ~testopc:testinstr#get_opcode
      ~condloc
      ~testloc in *)
  let convert_to_chif expr =
    let (cmds,bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ [ASSERT bxpr] in
  let convert_to_assert expr  =
    let vars = variables_in_expr expr in
    let varssize = List.length vars in
    let xprs =
      if varssize = 1 then
	let var = List.hd vars in
	let extxprs = condfloc#inv#get_external_exprs var in
	let extxprs =
          List.map (fun e -> substitute_expr (fun v -> e) expr) extxprs in
	expr :: extxprs
      else if varssize = 2 then
	let varlist = vars in
	let var1 = List.nth varlist 0 in
	let var2 = List.nth varlist 1 in
	let extxprs1 = condfloc#inv#get_external_exprs var1 in
	let extxprs2 = condfloc#inv#get_external_exprs var2 in
	let xprs = List.concat
	  (List.map
	     (fun e1 ->
	       List.map
		 (fun e2 ->
		   substitute_expr
                     (fun w -> if w#equal var1 then e1 else e2) expr)
		 extxprs2)
	     extxprs1) in
	expr :: xprs
      else
	[expr] in
    List.concat (List.map convert_to_chif xprs) in
  let make_asserts exprs =
    List.concat (List.map convert_to_assert exprs) in
  let make_branch_assert exprs =
    let commands = List.map convert_to_assert exprs in
    [BRANCH (List.map LF.mkCode commands)] in
  let make_assert expr =
    convert_to_assert expr in
  let make_test_code expr =
    if is_conjunction expr then
      let conjuncts = get_conjuncts expr in
      make_asserts conjuncts
    else if is_disjunction expr then
      let disjuncts = get_disjuncts expr in
      make_branch_assert disjuncts
    else
      make_assert expr in
  match optboolxpr with
    Some bxpr ->
      let thencode = make_test_code bxpr in
      let elsecode = make_test_code (simplify_xpr (XOp (XLNot, [bxpr]))) in
      (frozenVars, Some (thencode, elsecode))
  | _ -> (frozenVars, None)
  
let make_tests
    ~(condinstr:arm_assembly_instruction_int)
    ~(testinstr:arm_assembly_instruction_int)
    ~(condloc:location_int)
    ~(testloc:location_int) =
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
  let env = testfloc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let (frozenVars, optboolxpr) =
    if is_opcode_conditional testinstr#get_opcode then
      let finfo = testfloc#f in
      let faddr = testfloc#fa in
      if finfo#has_associated_cc_setter testloc#ci then
        let testtestiaddr = finfo#get_associated_cc_setter testloc#ci in
        let testtestloc = ctxt_string_to_location faddr testtestiaddr in
        let testtestaddr = testtestloc#i in
        let testtestinstr = !arm_assembly_instructions#at_address testtestaddr in
        let _ =
          chlog#add
            "conditional conditional test"
            (LBLOCK [
                 testfloc#l#toPretty;
                 STR ": ";
                 STR (arm_opcode_to_string testinstr#get_opcode);
                 STR " with setter ";
                 STR (arm_opcode_to_string testtestinstr#get_opcode)]) in
        arm_conditional_conditional_expr
          ~condopc:condinstr#get_opcode
          ~testopc: testinstr#get_opcode
          ~testtestopc: testtestinstr#get_opcode
          ~condloc
          ~testloc
          ~testtestloc
      else
        arm_conditional_expr
          ~condopc:condinstr#get_opcode
          ~testopc:testinstr#get_opcode
          ~condloc
          ~testloc
    else
      arm_conditional_expr
        ~condopc:condinstr#get_opcode
        ~testopc:testinstr#get_opcode
        ~condloc
        ~testloc in

  let convert_to_chif expr =
    let (cmds,bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ [ASSERT bxpr] in
  let convert_to_assert expr  =
    let vars = variables_in_expr expr in
    let varssize = List.length vars in
    let xprs =
      if varssize = 1 then
	let var = List.hd vars in
	let extxprs = condfloc#inv#get_external_exprs var in
	let extxprs =
          List.map (fun e -> substitute_expr (fun v -> e) expr) extxprs in
	expr :: extxprs
      else if varssize = 2 then
	let varlist = vars in
	let var1 = List.nth varlist 0 in
	let var2 = List.nth varlist 1 in
	let extxprs1 = condfloc#inv#get_external_exprs var1 in
	let extxprs2 = condfloc#inv#get_external_exprs var2 in
	let xprs = List.concat
	  (List.map
	     (fun e1 ->
	       List.map
		 (fun e2 ->
		   substitute_expr
                     (fun w -> if w#equal var1 then e1 else e2) expr)
		 extxprs2)
	     extxprs1) in
	expr :: xprs
      else
	[expr] in
    List.concat (List.map convert_to_chif xprs) in
  let make_asserts exprs =
    let _ = env#start_transaction in
    let commands = List.concat (List.map convert_to_assert exprs) in
    let const_assigns = env#end_transaction in
    const_assigns @ commands in
  let make_branch_assert exprs =
    let _ = env#start_transaction in
    let commands = List.map convert_to_assert exprs in
    let branch = BRANCH (List.map LF.mkCode commands) in
    let const_assigns = env#end_transaction in
    const_assigns @ [branch] in
  let make_assert expr =
    let _ = env#start_transaction in
    let commands = convert_to_assert expr in
    let const_assigns = env#end_transaction in
    const_assigns @ commands in
  let make_test_code expr =
    if is_conjunction expr then
      let conjuncts = get_conjuncts expr in
      make_asserts conjuncts
    else if is_disjunction expr then
      let disjuncts = get_disjuncts expr in
      make_branch_assert disjuncts
    else
      make_assert expr in
  match optboolxpr with
    Some bxpr ->
      let thencode = make_test_code bxpr in
      let elsecode = make_test_code (simplify_xpr (XOp (XLNot, [bxpr]))) in
      (frozenVars, Some (thencode, elsecode))
  | _ -> (frozenVars, None)

let make_local_tests
      (condinstr: arm_assembly_instruction_int) (condloc: location_int) =
  let floc = get_floc condloc in
  let env = floc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let boolxpr =
    match condinstr#get_opcode with
    | CompareBranchZero (op, _) ->
       let x = op#to_expr floc in
       XOp (XEq, [x; zero_constant_expr])
    | CompareBranchNonzero (op, _) ->
       let x = op#to_expr floc in
       XOp (XNe, [x; zero_constant_expr])
    | _ ->
       raise (BCH_failure
                (LBLOCK [STR "Unexpected condition: "; condinstr#toPretty])) in
  let convert_to_chif expr =
    let (cmds,bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ [ASSERT bxpr] in
  let make_assert x =
    let _ = env#start_transaction in
    let commands = convert_to_chif x in
    let const_assigns = env#end_transaction in
    const_assigns @ commands in
  let thencode = make_assert boolxpr in
  let elsecode = make_assert (simplify_xpr (XOp (XLNot, [boolxpr]))) in
  (thencode, elsecode)


let make_local_condition
      (condinstr: arm_assembly_instruction_int)
      (condloc: location_int)
      (blocklabel: symbol_t)
      (thenaddr: ctxt_iaddress_t)
      (elseaddr: ctxt_iaddress_t) =
  let thenlabel = make_code_label thenaddr in
  let elselabel = make_code_label elseaddr in
  let (thentest, elsetest) = make_local_tests condinstr condloc in
  let make_node_and_label testcode tgtaddr modifier =
    let src = condloc#i in
    let nextlabel = make_code_label ~src ~modifier tgtaddr in
    let transaction = TRANSACTION (nextlabel, LF.mkCode testcode, None) in
    (nextlabel, [transaction]) in
  let (thentestlabel, thennode) =
    make_node_and_label thentest thenaddr "then" in
  let (elsetestlabel, elsenode) =
    make_node_and_label elsetest elseaddr "else" in
  let thenedges =
    [(blocklabel, thentestlabel); (thentestlabel, thenlabel)] in
  let elseedges =
    [(blocklabel, elsetestlabel); (elsetestlabel, elselabel) ] in
  ([(thentestlabel, thennode); (elsetestlabel, elsenode)], thenedges @ elseedges)


let make_condition
    ~(condinstr:arm_assembly_instruction_int)
    ~(testinstr:arm_assembly_instruction_int)
    ~(condloc:location_int)
    ~(testloc:location_int)
    ~(blocklabel:symbol_t)
    ~(thenaddr:ctxt_iaddress_t)
    ~(elseaddr:ctxt_iaddress_t) =
  let thenlabel = make_code_label thenaddr in
  let elselabel = make_code_label elseaddr in
  let (frozenVars, tests) =
    make_tests ~condloc ~testloc ~condinstr ~testinstr in
  match tests with
    Some (thentest, elsetest) ->
      let make_node_and_label testcode tgtaddr modifier =
	let src = condloc#i in
	let nextlabel = make_code_label ~src ~modifier tgtaddr in
	let testcode = testcode @ [ABSTRACT_VARS frozenVars] in
	let transaction = TRANSACTION (nextlabel, LF.mkCode testcode, None) in
	(nextlabel, [transaction]) in
      let (thentestlabel, thennode) =
	make_node_and_label thentest thenaddr "then" in
      let (elsetestlabel, elsenode) =
	make_node_and_label elsetest elseaddr "else" in
      let thenedges =
	[(blocklabel, thentestlabel); (thentestlabel, thenlabel)] in
      let elseedges =
	[(blocklabel, elsetestlabel); (elsetestlabel, elselabel) ] in
      ([(thentestlabel, thennode); (elsetestlabel, elsenode)],
       thenedges @ elseedges)
  | _ ->
    let abstractlabel =
      make_code_label ~modifier:"abstract" testloc#ci in
    let transaction =
      TRANSACTION (abstractlabel, LF.mkCode [ABSTRACT_VARS frozenVars], None) in
    let edges = [(blocklabel, abstractlabel);
                 (abstractlabel, thenlabel);
		 (abstractlabel, elselabel)] in
    ([(abstractlabel, [transaction])], edges)
    

let translate_arm_instruction
      ~(funloc:location_int)
      ~(codepc:arm_code_pc_int)
      ~(blocklabel:symbol_t)
      ~(exitlabel:symbol_t)
      ~(cmds:cmd_t list) =
  let (ctxtiaddr, instr) = codepc#get_next_instruction in
  let faddr = funloc#f in
  let finfo = get_function_info faddr in
  let loc = ctxt_string_to_location faddr ctxtiaddr in  (* instr location *)
  let invlabel = get_invariant_label loc in
  let invop = OPERATION {op_name = invlabel; op_args = []} in
  let bwdinvlabel = get_invariant_label ~bwd:true loc in
  let bwdinvop = OPERATION {op_name = bwdinvlabel; op_args = []} in
  let frozenAsserts =
    List.map (fun (v,fv) -> ASSERT (EQ (v,fv)))
      (finfo#get_test_variables ctxtiaddr) in
  let rewrite_expr floc x:xpr_t =
    let xpr = floc#inv#rewrite_expr x floc#env#get_variable_comparator in
    let rec expand x =
      match x with
      | XVar v when floc#env#is_symbolic_value v ->
         expand (floc#env#get_symbolic_value_expr v)
      | XOp (op,l) -> XOp (op, List.map expand l)
      | _ -> x in
    simplify_xpr (expand xpr) in

  (* arm reference A2.3 (page A2-45):
     PC, the program counter
     - when executing an ARM instruction, PC reads as the address of the
       current instruction plus 8;
     - when executing a Thumb instruction, PC reads as the address of the
       current instruction plus 4

     Here we are setting the PC value for the following instruction, so
     we need to add another 4 for ARM and 2 for Thumb in case the current
     instruction is 2-byte instruction and 4 in case this is a 4-byte
     instruction.
   *)
  let floc = get_floc loc in
  let pcv = (pc_r RD)#to_variable floc in
  let iaddr8 =
    if instr#is_arm32 then
      (loc#i#add_int 12)#to_numerical
    else if (String.length instr#get_instruction_bytes) = 2 then
      (loc#i#add_int 6)#to_numerical
    else
      (loc#i#add_int 8)#to_numerical in
  let pcassign = floc#get_assign_commands pcv (XConst (IntConst iaddr8)) in
  let default newcmds =
    ([], [], cmds @ frozenAsserts @ (invop :: newcmds) @ [bwdinvop] @ pcassign) in
  let make_conditional_commands (c: arm_opcode_cc_t) (cmds: cmd_t list) =
    if finfo#has_associated_cc_setter ctxtiaddr then
      let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
      let testloc = ctxt_string_to_location faddr testiaddr in
      let testaddr = (ctxt_string_to_location faddr testiaddr)#i in
      let testinstr = (!arm_assembly_instructions#at_address testaddr) in
      let (frozenvars, tests) =
        make_instr_local_tests ~condloc:loc ~testloc ~condinstr:instr ~testinstr in
      match tests with
      | Some (thentest, elsetest) ->
         default [BRANCH [LF.mkCode (thentest @ cmds); LF.mkCode elsetest]]
      | _ ->
         default [BRANCH [LF.mkCode cmds; LF.mkCode [SKIP]]]
    else
      default [BRANCH [LF.mkCode cmds; LF.mkCode [SKIP]]] in
  let get_register_vars (ops: arm_operand_int list) =
    List.fold_left (fun acc op ->
        if op#is_register || op#is_extension_register then
          (op#to_variable floc) :: acc
        else
          match op#get_kind with
          | ARMShiftedReg (r, ARMImmSRT _) ->
             (floc#env#mk_arm_register_variable r) :: acc
          | ARMShiftedReg (r, ARMRegSRT (_, rs)) ->
             let rvar = floc#env#mk_arm_register_variable r in
             let rsvar = floc#env#mk_arm_register_variable rs in
             rvar :: rsvar :: acc
          | _ -> acc) [] ops in
  let get_use_high_vars (xprs: xpr_t list):variable_t list =
    let inv = floc#inv in
    let comparator = floc#env#get_variable_comparator in
    List.fold_left (fun acc x ->
        let xw = inv#rewrite_expr x comparator in
        let xs = simplify_xpr xw in
        (vars_in_expr_list [xs]) @ acc) [] xprs in
  let flagdefs =
    let flags_set = get_arm_flags_set instr#get_opcode in
    List.map (fun f -> finfo#env#mk_flag_variable (ARMCCFlag f)) flags_set in

  match instr#get_opcode with

  | Branch (c, op, _)
    | BranchExchange (c, op) when is_cond_conditional c ->
     let thenaddr =
       if op#is_absolute_address then
         (make_i_location loc op#get_absolute_address)#ci
       else if op#is_register && op#get_register = ARLR then
         "exit"
       else
         "?" in
     let elseaddr = codepc#get_false_branch_successor in
     let cmds = cmds @ [invop] in
     let transaction = package_transaction finfo blocklabel cmds in
     if finfo#has_associated_cc_setter ctxtiaddr then
       let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
       let testloc = ctxt_string_to_location faddr testiaddr in
       let testaddr = (ctxt_string_to_location faddr testiaddr)#i in
       let (nodes, edges) =
         make_condition
           ~condinstr:instr
           ~testinstr:(!arm_assembly_instructions#at_address testaddr)
           ~condloc:loc
           ~testloc
           ~blocklabel
           ~thenaddr
           ~elseaddr in
       ((blocklabel, [transaction]) :: nodes, edges, [])
     else
       let thenlabel = make_code_label thenaddr in
       let elselabel = make_code_label elseaddr in
       let nodes = [(blocklabel, [transaction])] in
       let edges = [(blocklabel, thenlabel); (blocklabel, elselabel)] in
       (nodes, edges, [])

  | CompareBranchZero (op, tgt)
    | CompareBranchNonzero (op, tgt) ->
     let thenaddr = (make_i_location loc tgt#get_absolute_address)#ci in
     let elseaddr = codepc#get_false_branch_successor in
     let usevars = get_register_vars [op] in
     let defcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let cmds = cmds @ defcmds @ [invop] in
     let transaction = package_transaction finfo blocklabel cmds in
     let (nodes, edges) =
       make_local_condition instr loc blocklabel thenaddr elseaddr in
     ((blocklabel, [transaction]) :: nodes, edges, [])

  | Branch (_, op, _)
    | BranchExchange (ACCAlways, op) when op#is_absolute_address ->
     default []

  | Branch (_, op, _)
    | BranchExchange (ACCAlways, op)
       when op#is_register && op#get_register = ARLR ->
     default []

  (* -------------------------------------------------------------- Add -- *
   * if ConditionPassed() then
   *   shifted = Shift(R[m], shift_t, shift_n, APSR.C)
   *   (result, carry, overflow) = AddWithCarry(R[n], shifted, '0')
   *   if d == 15 then
   *     ALUWritePC(result);
   *   else
   *     R[d] = result;
   *     if setflags then
   *       APSR.N = result<31>;
   *       APSR.Z = IsZeroBit(result);
   *       APSR.C = carry;
   *       APSR.V = overflow;
   *------------------------------------------------------------------------- *)
  | Add (_, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let usevars = get_register_vars [rn; rm] in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let cmds = floc#get_assign_commands vrd (XOp (XPlus, [xrn; xrm])) in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ------------------------------------------------------------- AddCarry -- *
   * if ConditionPassed() then
   *   (result, carry, overflow) = AddWithCarry(R[n], op2, APSR.C)
   *   if d == 15 then
   *     ALUWritePC(result);
   *   else
   *     R[d] = result;
   *     if setflags then
   *       APSR.N = result<31>;
   *       APSR.Z = IsZeroBit(result);
   *       APSR.C = carry;
   *       APSR.V = overflow;
   * ------------------------------------------------------------------------ *)
  | AddCarry (_, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let cmds = floc#get_abstract_commands vrd () in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | Adr (c, dst, src) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = dst#to_lhs floc in
     let rhs = src#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     let defcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | ArithmeticShiftRight(setflags, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let asrr =
       match xrm with
       | XConst (IntConst n) when n#toInt = 2->
          XOp (XDiv, [xrn; XConst (IntConst (mkNumerical 4))])
       | _ -> XOp (XAsr, [xrn; xrm]) in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let cmds = floc#get_assign_commands vrd asrr in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BitFieldClear (_, rd, _, _, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrd = rd#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rd] in
     let usehigh = get_use_high_vars [xrd] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | BitFieldInsert (_, rd, rn, _, _, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrd = rd#to_expr floc in
     let xrn = rn#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rd; rn] in
     let usehigh = get_use_high_vars [xrd; xrn] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | BitwiseAnd (setflags, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let result = XOp (XBAnd, [xrn; xrm]) in
     let cmds = floc#get_assign_commands vrd result in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BitwiseBitClear (_, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let result = XOp (XBAnd, [xrn; XOp (XBNot, [xrm])]) in
     let cmds = floc#get_assign_commands vrd result in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BitwiseExclusiveOr (_, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ---------------------------------------------------------- BitwiseNot -- *
   * if immediate
   *   result = NOT(imm32);
   * if register
   *   (shifted, carry) = Shift_C(R[m], shift_t, shift_n, APSR.C);
   *   result = NOT(shifted);
   * if d == 15 then
   *   ALUWritePC(result);
   * else
   *   R[d] = result;
   *   if setflags then
   *     APSR.N = result<31>;
   *     APSR.Z = IsZeroBit(result);
   *     APSR.C = carry;
   * ------------------------------------------------------------------------ *)
  | BitwiseNot (setflags, c, dst, src, _) when src#is_immediate ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let notrhs =
       match rhs with
       | XConst (IntConst n) when n#equal numerical_zero ->
          XConst (IntConst numerical_one#neg)
       | XConst (IntConst n) ->
          XConst (IntConst ((nume32#sub n)#sub numerical_one))
       | _ -> XConst XRandom in
     let (lhs, lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs notrhs in
     let usevars = get_register_vars [src] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BitwiseNot (_, c, dst, src, _) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = dst#to_lhs floc in
     let rhs = src#to_expr floc in
     let cmds = floc#get_abstract_commands lhs () in
     let usevars = get_register_vars [src] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds =  lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BitwiseOr (_, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BitwiseOrNot (_, c, rd, rn, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ---------------------------------------------------------- BranchLink -- *
   * if CurrentInstrSet() == InstrSet_ARM then
   *   LR = PC - 4;
   * else
   *   LR = PC<31:1> : '1';
   * if targetInstrSet == InstrSet_ARM then
   *   targetAddress = Align(PC,4) + imm32;
   * else
   *   targetAddress = PC + imm32;
   * SelectInstrSet(targetInstrSet);
   * BranchWritePC(targetAddress);
   * ------------------------------------------------------------------------ *)
  | BranchLink (c, tgt) when tgt#is_absolute_address ->
     let floc = get_floc loc in
     let vr0 = floc#f#env#mk_arm_register_variable AR0 in
     let vr1 = floc#f#env#mk_arm_register_variable AR1 in
     let vr2 = floc#f#env#mk_arm_register_variable AR2 in
     let vr3 = floc#f#env#mk_arm_register_variable AR3 in
     let pars = List.map fst floc#get_arm_call_arguments in
     let args = List.map snd floc#get_arm_call_arguments in
     let (defs, use, usehigh) =
       if ((List.length pars) = 1
           && (is_floating_point_parameter (List.hd pars))) then
         let s0: arm_extension_register_t =
           {armxr_type = XSingle; armxr_index = 0} in
         let s0var = floc#f#env#mk_arm_extension_register_variable s0 in
         ([s0var], [s0var], [s0var])
       else
         let usehigh = get_use_high_vars args in
         let use =
           match List.length args with
           | 0 -> []
           | 1 -> [vr0]
           | 2 -> [vr0; vr1]
           | 3 -> [vr0; vr1; vr2]
           | _ -> [vr0; vr1; vr2; vr3] in
         ([vr0], use, usehigh) in
     let cmds = floc#get_arm_call_commands in
     let defcmds =
       floc#get_vardef_commands
         ~defs:defs
         ~clobbers:[vr1; vr2; vr3]
         ~use:use
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BranchLinkExchange (c, tgt) when tgt#is_absolute_address ->
     let floc = get_floc loc in
     let vr0 = floc#f#env#mk_arm_register_variable AR0 in
     let vr1 = floc#f#env#mk_arm_register_variable AR1 in
     let vr2 = floc#f#env#mk_arm_register_variable AR2 in
     let vr3 = floc#f#env#mk_arm_register_variable AR3 in
     let pars = List.map fst floc#get_arm_call_arguments in
     let args = List.map snd floc#get_arm_call_arguments in
     let (defs, use, usehigh) =
       if ((List.length pars) = 1
           && (is_floating_point_parameter (List.hd pars))) then
         let s0: arm_extension_register_t =
           {armxr_type = XSingle; armxr_index = 0} in
         let s0var = floc#f#env#mk_arm_extension_register_variable s0 in
         ([s0var], [s0var], [s0var])
       else
         let usehigh = get_use_high_vars args in
         let use =
           match List.length args with
           | 0 -> []
           | 1 -> [vr0]
           | 2 -> [vr0; vr1]
           | 3 -> [vr0; vr1; vr2]
           | _ -> [vr0; vr1; vr2; vr3] in
         ([vr0], use, usehigh) in
     let cmds = floc#get_arm_call_commands in
     let defcmds =
       floc#get_vardef_commands
         ~defs:defs
         ~clobbers:[vr1; vr2; vr3]
         ~use:use
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | ByteReverseWord (c, rd, rm, _) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = rd#to_lhs floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands lhs () in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = (lhscmds @ defcmds @ cmds) in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* --------------------------------------------- ByteReversePackedHalfword --
   * Reverses the byte order in each 16-bit halfword of a 32-bit register.
   *
   * bits(32) result;
   * result<31:24> = R[m]<23:16>
   * result<23:16> = R[m]<31:24>
   * result<15:8> = R[m]<7:0>
   * result<7>0> = R[m]<15:8>
   * R[d] = result;
   * ------------------------------------------------------------------------ *)
  | ByteReversePackedHalfword (c, rd, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | Compare (c, rn, rm, _) ->
     let floc = get_floc loc in
     let _ =
       floc#inv#rewrite_expr (rn#to_expr floc)
         floc#env#get_variable_comparator in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let xresult = XOp (XMinus, [xrn; xrm]) in
     let xresult = rewrite_expr floc xresult in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xresult] in
     let defcmds =
       floc#get_vardef_commands
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     (match c with
      | ACCAlways -> default defcmds
      | _ -> make_conditional_commands c defcmds)

  | CompareNegative (c, rn, rm) ->
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let xresult = XOp (XPlus, [xrn; xrm]) in
     let xresult = rewrite_expr floc xresult in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xresult] in
     let defcmds =
       floc#get_vardef_commands
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     (match c with
      | ACCAlways -> default defcmds
      | _ -> make_conditional_commands c defcmds)

  | CountLeadingZeros (c, rd, rm) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = rd#to_lhs floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands lhs () in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = (lhscmds @ defcmds @ cmds) in
     (match c with
      | ACCAlways -> default defcmds
      | _ -> make_conditional_commands c cmds)

  | DataMemoryBarrier _ ->
     default []

  | IfThen (c, xyz) when instr#is_aggregate ->
     let floc = get_floc loc in
     if finfo#has_associated_cc_setter ctxtiaddr then
       let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
       let testloc = ctxt_string_to_location faddr testiaddr in
       let testaddr = testloc#i in
       let testinstr = !arm_assembly_instructions#at_address testaddr in
       let dstop = instr#get_aggregate_dst in
       let (frozenvars, optpredicate) =
         make_conditional_predicate
           ~condinstr:instr
           ~testinstr:testinstr
           ~condloc:loc
           ~testloc:testloc in
       let cmds =
         match optpredicate with
         | Some p ->
            let (lhs, lhscmds) = dstop#to_lhs floc in
            let cmds = floc#get_assign_commands lhs p in
            let usevars = vars_in_expr_list [p] in
            let usehigh = get_use_high_vars [p] in
            let defcmds =
              floc#get_vardef_commands
                ~defs:[lhs]
                ~use:usevars
                ~usehigh:usehigh
                ~flagdefs:flagdefs
                ctxtiaddr in
            let _ =
              chlog#add
                "assign ite predicate"
                (LBLOCK [
                     testaddr#toPretty;
                     STR ": " ;
                     lhs#toPretty;
                     STR " := ";
                     x2p p]) in
            let _ =
              chlog#add
                "ite assign cmds"
                (LBLOCK (List.map (command_to_pretty 0) cmds)) in
            lhscmds @ defcmds @ cmds
       | _ ->
          let _ =
            chlog#add
              "no ite predicate"
              (LBLOCK [testaddr#toPretty; STR ": " ; testinstr#toPretty]) in
          [] in
       default cmds
     else
       let _ =
         chlog#add
           "aggregate without ite predicate"
           (LBLOCK [loc#toPretty; STR ": "; instr#toPretty]) in
       default []

  (* ---------------------------------------- LoadMultipleDecrementAfter --
   * Loads multiple registers from consecutive memory locations using an
   * address from a base register. The consecutive memory locations end at
   * this address, and address just below the lowest of those locations may
   * be written back to the base register.
   *
   * address = R[n] - 4 * BitCount(registers) + 4;
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     R[i] = MemA[address, 4]
   *     address = address + 4;
   *   if registers<15> == '1' then
   *     LoadWritePC(MemA[address, 4]);
   *   if wback && registers<n> == '0' then
   *     R[n] = R[n] - 4 * BitCount(registers);
   * ---------------------------------------------------------------------- *)
  | LoadMultipleDecrementAfter (wback, c, base, rl, _) ->
     let floc = get_floc loc in
     let basereg = base#get_register in
     let usevars = get_register_vars [base] in
     let regcount = rl#get_register_count in
     let reglhss = rl#to_multiple_variable floc in
     let basedefcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let (memreads, _) =
       List.fold_left
         (fun (acc, off) reglhs ->
           let memop = arm_reg_deref basereg ~with_offset:off RD in
           let memrhs = memop#to_expr floc in
           let cmds1 = floc#get_assign_commands reglhs memrhs in
           let memusehigh = get_use_high_vars [memrhs] in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[reglhs]
               ~use:memusehigh
               ~usehigh:memusehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + 4)) ([], 4 - (4 * regcount)) reglhss in
     let wbackassign =
       if wback then
         let (lhs, lhscmds) = base#to_lhs floc in
         let rhs = base#to_expr floc in
         let decrem = int_constant_expr (4 * regcount) in
         let newrhs = XOp (XMinus, [rhs; decrem]) in
         let wbackcmds = floc#get_assign_commands lhs newrhs in
         let wbackdefcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         wbackdefcmds @ wbackcmds
       else
         [] in
     let cmds = basedefcmds @ memreads @ wbackassign in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* --------------------------------------- LoadMultipleDecrementBefore --
   * Loads multiple registers from consecutive memory locations using an
   * address from a base register. The consecutive memory locations end
   * just below this address, and the lowest of those locations may be
   * written back to the base register.
   *
   * address = R[n] - 4 * BitCount(registers);
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     R[i] = MemA[address, 4];
   *     address = address + 4;
   * if registers<15> == '1' then
   *   LoadWritePC(MemA[address, 4]);
   * if wback && reigsters<n> == '0' then
   *   R[n] = R[n] - 4 * BitCount(registers);
   * ---------------------------------------------------------------------- *)
  | LoadMultipleDecrementBefore (wback, c, base, rl, _) ->
     let floc = get_floc loc in
     let basereg = base#get_register in
     let usevars = get_register_vars [base] in
     let regcount = rl#get_register_count in
     let reglhss = rl#to_multiple_variable floc in
     let basedefcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let (memreads, _) =
       List.fold_left
         (fun (acc, off) reglhs ->
           let memop = arm_reg_deref basereg ~with_offset:off RD in
           let memrhs = memop#to_expr floc in
           let cmds1 = floc#get_assign_commands reglhs memrhs in
           let memusehigh = get_use_high_vars [memrhs] in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[reglhs]
               ~use:memusehigh
               ~usehigh:memusehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + 4)) ([], -(4 * regcount)) reglhss in
     let wbackassign =
       if wback then
         let (lhs, lhscmds) = base#to_lhs floc in
         let rhs = base#to_expr floc in
         let decrem = int_constant_expr (4 * regcount) in
         let newrhs = XOp (XMinus, [rhs; decrem]) in
         let wbackcmds = floc#get_assign_commands lhs newrhs in
         let defwbackcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         defwbackcmds @ wbackcmds
       else
         [] in
     let cmds = basedefcmds @ memreads @ wbackassign in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ---------------------------------------- LoadMultipleIncrementAfter --
   * Loads multiple registers from consecutive memory locations using an
   * address from a base register. The consecutive memory locations start at
   * this address, and the address just above the highest of those locations
   * may be written back to the the base register.
   *
   * address = R[n];
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     R[i] = MemA[address, 4];
   *     address = address + 4;
   *   if registers<15> == '1' then
   *     LoadWritePC(MemA[address, 4]);
   *   if wback && registers<n> == '0' then
   *     R[n] = R[n] + + 4 * BitCount(registers);
   * ---------------------------------------------------------------------- *)
  | LoadMultipleIncrementAfter (wback, c, base, rl, _) ->
     let floc = get_floc loc in
     let basereg = base#get_register in
     let usevars = get_register_vars [base] in
     let regcount = rl#get_register_count in
     let reglhss = rl#to_multiple_variable floc in
     let basedefcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let (memreads, _) =
       List.fold_left
         (fun (acc, off) reglhs ->
           let memop = arm_reg_deref ~with_offset:off basereg RD in
           let memrhs = memop#to_expr floc in
           let cmds1 = floc#get_assign_commands reglhs memrhs in
           let memusehigh = get_use_high_vars [memrhs] in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[reglhs]
               ~use:memusehigh
               ~usehigh:memusehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + 4)) ([], 0) reglhss in
     let wbackassign =
       if wback then
         let (lhs, lhscmds) = base#to_lhs floc in
         let rhs = base#to_expr floc in
         let increm = int_constant_expr (4 * regcount) in
         let newrhs = XOp (XPlus, [rhs; increm]) in
         let wbackcmds = floc#get_assign_commands lhs newrhs in
         let defwbackcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         defwbackcmds @ wbackcmds
       else
         [] in
     let cmds = basedefcmds @ memreads @ wbackassign in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* --------------------------------------- LoadMultipleIncrementBefore --
   * Loads multiple registers from consecutive memory locations using an
   * address from a base register. The consecutive memory locations start
   * just above the address, and the address of the of those locations may
   * be written back to the base register.
   *
   * address = R[n] + 4;
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     R[i] = MemA[address, 4];
   *     address = address + 4;
   * if registers<15> == '1' then
   *   LoadWritePC(MemA[address, 4])
   * if wback && reigsters<n> == '0' then
   *   R[n] = R[n] + 4 * BitCount(registers)
   * ---------------------------------------------------------------------- *)
  | LoadMultipleIncrementBefore (wback, c, base, rl, _) ->
     let floc = get_floc loc in
     let basereg = base#get_register in
     let usevars = get_register_vars [base] in
     let regcount = rl#get_register_count in
     let reglhss = rl#to_multiple_variable floc in
     let basedefcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let (memreads, _) =
       List.fold_left
         (fun (acc, off) reglhs ->
           let memop = arm_reg_deref ~with_offset:off basereg RD in
           let memrhs = memop#to_expr floc in
           let cmds1 = floc#get_assign_commands reglhs memrhs in
           let memusehigh = get_use_high_vars [memrhs] in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[reglhs]
               ~use:memusehigh
               ~usehigh:memusehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + 4)) ([], 4) reglhss in
     let wbackassign =
       if wback then
         let (lhs, lhscmds) = base#to_lhs floc in
         let rhs = base#to_expr floc in
         let increm = int_constant_expr (4 * regcount) in
         let newrhs = XOp (XPlus, [rhs; increm]) in
         let wbackcmds = floc#get_assign_commands lhs newrhs in
         let defwbackcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         defwbackcmds @ wbackcmds
       else
         [] in
     let cmds = basedefcmds @ memreads @ wbackassign in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* -------------------------------------------------------- LoadRegister -- *
   * offset = Shift(R[m], shift_t, shift_n, APSR.C);
   * offset_addr = if add then (R[n] + offset) else (R[n] - offset);
   * address = if index then offset_addr else R[n];
   * data = MemU[address,4];
   * if wback then R[n] = offset_addr;
   * if t == 15 then
   *   if address<1:0> == '00' then
   *     LoadWritePC(data)
   *   else
   *     UNPREDICTABLE
   * elsif UnalignedSupport() || address<1:0> == '00' then
   *   R[t] = data;
   * else
   *   R[t] = ROR(data, 8*UInt(address<1:0>));
   * ------------------------------------------------------------------------ *)
  | LoadRegister (c, rt, rn, rm, mem, _) ->
     let floc = get_floc loc in
     let rhs =
       floc#inv#rewrite_expr (mem#to_expr floc)
         floc#env#get_variable_comparator in
     let (lhs, lhscmds) = rt#to_lhs floc in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let addr = mem#to_updated_offset_address floc in
         let (baselhs, baselhscmds) = rn#to_lhs floc in
         let ucmds = floc#get_assign_commands baselhs addr in
         let defupdatecmds = floc#get_vardef_commands ~defs:[baselhs] ctxtiaddr in
         baselhscmds @ defupdatecmds @ ucmds
       else
         [] in
     let cmds = (floc#get_assign_commands lhs rhs) @ updatecmds in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ---------------------------------------------------- LoadRegisterByte -- *
   * R[t] = ZeroExtend(MemU[address,1], 32);
   * if wback then R[n] = offset_addr;
   * -------------------------------------------------------------------------*)
  | LoadRegisterByte (c, rt, rn, rm, mem, _) ->
     let floc = get_floc loc in
     let rhs = XOp (XXlsb, [mem#to_expr floc]) in
     let rhs = floc#inv#rewrite_expr rhs floc#env#get_variable_comparator in
     let (lhs, lhscmds) = rt#to_lhs floc in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let addr = mem#to_updated_offset_address floc in
         let (baselhs, baselhscmds) = rn#to_lhs floc in
         let ucmds = floc#get_assign_commands baselhs addr in
         let defupdatecmds = floc#get_vardef_commands ~defs:[baselhs] ctxtiaddr in
         baselhscmds @ defupdatecmds @ ucmds
       else
         [] in
     let cmds = (floc#get_assign_commands lhs rhs) @updatecmds in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LoadRegisterDual (c, rt, rt2, rn, rm, mem, mem2) ->
     let floc = get_floc loc in
     let (lhs1, lhscmds1) = rt#to_lhs floc in
     let (lhs2, lhscmds2) = rt2#to_lhs floc in
     let rhs1 = mem#to_expr floc in
     let rhs2 = mem2#to_expr floc in
     let cmds1 = floc#get_assign_commands lhs1 rhs1 in
     let cmds2 = floc#get_assign_commands lhs2 rhs2 in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [rhs1; rhs2] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs1; lhs2]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds1 @ lhscmds2 @ defcmds @ cmds1 @ cmds2 in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LoadRegisterExclusive (c, rt, rn, rm, mem) ->
     let floc = get_floc loc in
     let rhs =
       floc#inv#rewrite_expr (mem#to_expr floc)
         floc#env#get_variable_comparator in
     let (lhs, lhscmds) = rt#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LoadRegisterHalfword (c, rt, rn,rm, mem, _) ->
     let floc = get_floc loc in
     let rhs = XOp (XXlsh, [mem#to_expr floc]) in
     let (lhs, lhscmds) = rt#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LoadRegisterSignedHalfword (c, rt, rn, rm, mem, _) ->
     let floc = get_floc loc in
     let rhs = mem#to_expr floc in
     let rhs = floc#inv#rewrite_expr rhs floc#env#get_variable_comparator in
     let (lhs, lhscmds) = rt#to_lhs floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let is_external v = floc#env#is_function_initial_value v in
     let rec is_symbolic_expr x =
       match x with
       | XOp (_, l) -> List.for_all is_symbolic_expr l
       | XVar v -> is_external v
       | XConst _ -> true
       | XAttr _ -> false in
     let cmds =
       (match rhs with
        | XConst  (IntConst n) when n#toInt > e15 ->
           let rhs = XOp (XPlus, [rhs; int_constant_expr (e32-e16)]) in
           let cmds = floc#get_assign_commands lhs rhs in
           lhscmds @ defcmds @ cmds
        | _ ->
           if is_symbolic_expr rhs then
             let rhs = floc#env#mk_signed_symbolic_value rhs 16 32 in
             let cmds = floc#get_assign_commands lhs (XVar rhs) in
             lhscmds @ defcmds @ cmds
           else
             let cmds = floc#get_abstract_commands lhs () in
             lhscmds @ defcmds @ cmds) in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LoadRegisterSignedByte (c, rt, rn, rm, mem, _) ->
     let floc = get_floc loc in
     let rhs = mem#to_expr floc in
     let (lhs, lhscmds) = rt#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LogicalShiftLeft (_, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let result = XOp (XLsl, [xrn; xrm]) in
     let cmds = floc#get_assign_commands vrd result in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LogicalShiftRight (_, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let result = XOp (XLsr, [xrn; xrm]) in
     let cmds = floc#get_assign_commands vrd result in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ---------------------------------------------------------------- Move -- *
   * result = R[m];
   * if d == 15 then
   *   ALUWritePC(result);
   * else
   *   R[d] = result;
   *  if setflags then
   *    APSR.N = result<31>;
   *    APSR.Z = IsZeroBit(result);
   * ------------------------------------------------------------------------ *)
  | Move (_, c, rd, rm, _, _) when instr#is_subsumed ->
     let _ =
       chlog#add
         "instr subsumed"
         (LBLOCK [(get_floc loc)#l#toPretty; STR ": "; instr#toPretty]) in
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = rm#to_expr floc in
     let xxrm = floc#inv#rewrite_expr xrm floc#env#get_variable_comparator in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xxrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     default defcmds

  | Move (setflags, c, rd, rm, _, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = rm#to_expr floc in
     let xxrm = floc#inv#rewrite_expr xrm floc#env#get_variable_comparator in
     let cmds = floc#get_assign_commands vrd xrm in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xxrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | MoveRegisterCoprocessor (_, _, _, dst, _, _, _) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     let defcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
     default (lhscmds @ defcmds @ cmds)

  | MoveToCoprocessor _ -> default []

  (* ------------------------------------------------------------ MoveTop ---
   * R[d]<31:16> = imm16;
   * // R[d]<15:0> unchanged
   * ------------------------------------------------------------------------ *)
  | MoveTop (c, rd, imm) ->
     let floc = get_floc loc in
     let (vrd, lhscmds) = rd#to_lhs floc in
     let xrd = rd#to_expr floc in
     let xrd = rewrite_expr floc xrd in
     let imm16 = imm#to_expr floc in
     let ximm16 = XOp (XMult, [imm16; int_constant_expr e16]) in
     let xrdm16 = XOp (XXlsh, [xrd]) in
     let rhsxpr = XOp (XPlus, [xrdm16; ximm16]) in
     let cmds = floc#get_assign_commands vrd rhsxpr in
     let usevars = get_register_vars [rd] in
     let usehigh = get_use_high_vars [xrd] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | MoveTwoRegisterCoprocessor (c, _, _, rt, rt2, _) ->
     let floc = get_floc loc in
     let (lhs1, lhs1cmds) = rt#to_lhs floc in
     let (lhs2, lhs2cmds) = rt2#to_lhs floc in
     let cmds1 = floc#get_abstract_commands lhs1 () in
     let cmds2 = floc#get_abstract_commands lhs2 () in
     let defcmds = floc#get_vardef_commands ~defs:[lhs1; lhs2] ctxtiaddr in
     let cmds = lhs1cmds @ lhs2cmds @ defcmds @ cmds1 @ cmds2 in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | Multiply (_, c, rd, rn, rm) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = rd#to_lhs floc in
     let rhs1 = rn#to_expr floc in
     let rhs2 = rm#to_expr floc in
     let result = XOp (XMult, [rhs1; rhs2]) in
     let cmds = floc#get_assign_commands lhs result in
     let defcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | MultiplyAccumulate (_, c, rd, rn, rm, ra) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = rd#to_lhs floc in
     let rhs1 = rn#to_expr floc in
     let rhs2 = rm#to_expr floc in
     let rhsa = ra#to_expr floc in
     let result = XOp (XPlus, [XOp (XMult, [rhs1; rhs2]); rhsa]) in
     let cmds = floc#get_assign_commands lhs result in
     let usevars = get_register_vars [rn; rm; ra] in
     let usehigh = get_use_high_vars [rhs1; rhs2; rhsa] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | MultiplySubtract (c, rd, rn, rm, ra) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = rd#to_lhs floc in
     let rhs1 = rn#to_expr floc in
     let rhs2 = rm#to_expr floc in
     let rhsa = ra#to_expr floc in
     let result = XOp (XMinus, [rhsa; XOp (XMult, [rhs1; rhs2])]) in
     let cmds = floc#get_assign_commands lhs result in
     let usevars = get_register_vars [rn; rm; ra] in
     let usehigh = get_use_high_vars [rhs1; rhs2; rhsa] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[lhs]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = lhscmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | NoOperation _ ->
     default []

  (* ----------------------------------------------------------------- Pop -- *
   * address = SP;
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     R[i] = if UnalignedAllowed then
   *              MemU[address,4]
   *            else
   *              MemA[address,4];
   *     address = address + 4;
   * if registers<15> == '1' then
   *   if UnalignedAllowed then
   *     if address<1:0> == '00' then
   *       LoadWritePC(MemU[address,4]);
   *     else
   *       UNPREDICTABLE;
   *   else
   *     LoadWritePC(MemA[address,4]);
   * if registers<13> == '0' then SP = SP + 4*BitCount(registers);
   * if registers<13> == '1' then SP = bits(32) UNKNOWN;
   * ------------------------------------------------------------------------ *)

  | Pop (c, sp, rl, _) ->
     let floc = get_floc loc in
     let regcount = rl#get_register_count in
     let sprhs = sp#to_expr floc in
     let reglhss = rl#to_multiple_variable floc in
     let (stackops,_) =
       List.fold_left
         (fun (acc, off) reglhs ->
           let (splhs,splhscmds) = (sp_r RD)#to_lhs floc in
           let stackop = arm_sp_deref ~with_offset:off RD in
           let stackvar = stackop#to_variable floc in
           let stackrhs = stackop#to_expr floc in
           let cmds1 = floc#get_assign_commands reglhs stackrhs in
           let usehigh = get_use_high_vars [stackrhs] in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[reglhs]
               ~use:[stackvar]
               ~usehigh:usehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1 @ splhscmds, off+4)) ([],0) reglhss in
     let (splhs,splhscmds) = (sp_r WR)#to_lhs floc in
     let increm = XConst (IntConst (mkNumerical (4 * regcount))) in
     let cmds = floc#get_assign_commands splhs (XOp (XPlus, [sprhs; increm])) in
     let useshigh =
       if rl#includes_pc then
         [floc#f#env#mk_arm_register_variable AR0]
       else
         [] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[splhs]
         ~use:(get_register_vars [sp])
         ~usehigh:useshigh
         ctxtiaddr in
     let cmds = stackops @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | PreloadData _ ->
     default []

  (* ---------------------------------------------------------------- Push -- *
   * address = SP - 4*BitCount(registers);
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     if i == 13 && i != LowestSetBit(registers) then
   *       MemA[address,r] = bits(32) UNKNOWN;
   *     else
   *        if UnalignedAllowed then
   *          MemU[address,4] = R[i];
   *        else
   *          MemA[address,4] = R[i];
   *     address = address + 4;
   * if registers<15> == '1' then
   *   if UnalignedAllowed then
   *     MemU[address,4] = PCStoreValue();
   *   else
   *     MemA[address,4] = PCStoreValue();
   * SP = SP - 4*BitCount(registers);
   * ------------------------------------------------------------------------ *)
  | Push (c, sp, rl, _) ->
     let floc = get_floc loc in
     let regcount = rl#get_register_count in
     let sprhs = sp#to_expr floc in
     let rhsvars = rl#to_multiple_variable floc in
     let (stackops,_) =
       List.fold_left
         (fun (acc, off) rhsvar ->
           let (splhs,splhscmds) = (sp_r RD)#to_lhs floc in
           let stackop = arm_sp_deref ~with_offset:off WR in
           let (stacklhs, stacklhscmds) = stackop#to_lhs floc in
           let rhsexpr = rewrite_expr floc (XVar rhsvar) in
           let cmds1 = floc#get_assign_commands stacklhs rhsexpr in
           let usehigh = get_use_high_vars [rhsexpr] in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[stacklhs]
               ~use:[rhsvar]
               ~usehigh:usehigh
               ctxtiaddr in
           (acc @ stacklhscmds @ splhscmds @ defcmds1 @ cmds1, off+4))
         ([],(-(4*regcount))) rhsvars in
     let (splhs,splhscmds) = (sp_r WR)#to_lhs floc in
     let decrem = XConst (IntConst (mkNumerical(4 * regcount))) in
     let cmds = floc#get_assign_commands splhs (XOp (XMinus, [sprhs; decrem])) in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[splhs]
         ~use:(get_register_vars [sp])
         ctxtiaddr in
     let cmds = stackops @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | ReverseBits (c, rd, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | ReverseSubtract (_, c, rd, rn, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_assign_commands vrd (XOp (XMinus, [xrm; xrn])) in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | ReverseSubtractCarry(_, c, rd, rn, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_assign_commands vrd (XOp (XMinus, [xrm; xrn])) in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | RotateRight (_, c, rd, rn, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | RotateRightExtend (_, c, rd, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SelectBytes (c, rd, rn, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SignedBitFieldExtract (c, rd, rn) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rn] in
     let usehigh = get_use_high_vars [xrn] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = (defcmds @ cmds) in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SignedDivide (c, rd, rn, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let usevars = get_register_vars [rn; rm] in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let result = XOp (XDiv, [xrn; xrm]) in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let cmds = floc#get_assign_commands vrd result in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SignedExtendByte (c, rd, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SignedExtendHalfword (c, rd, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = rm#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SignedMostSignificantWordMultiply (c, rd, rm, rn, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = rm#to_expr floc in
     let xrn = rn#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rm; rn] in
     let usehigh = get_use_high_vars [xrm; xrn] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SignedMostSignificantWordMultiplyAccumulate (c, rd, rn, rm, ra, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let cmds = floc#get_abstract_commands vrd () in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let xra = ra#to_expr floc in
     let usevars = get_register_vars [rn; rm; ra] in
     let usehigh = get_use_high_vars [xrn; xrm; xra] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SignedMultiplyLong (_, _, rdlo, rdhi, _, _) ->
     let floc = get_floc loc in
     let vlo = rdlo#to_variable floc in
     let vhi = rdhi#to_variable floc in
     let cmdslo = floc#get_abstract_commands vlo () in
     let cmdshi = floc#get_abstract_commands vhi () in
     let defcmds = floc#get_vardef_commands ~defs:[vlo; vhi] ctxtiaddr in
     default (defcmds @ cmdslo @ cmdshi)

  (* ---------------------------------------- StoreMultipleIncrementAfter --
   * Stores multiple registers to consecutive memoy locations using an address
   * from a base register. The consecutive memory locations start at this
   * address, and the address just above the last of those locations may be
   * written back to be base register.
   *
   * address = R[n];
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     MemA[address, 4] = R[i];
   *     address = address + 4;
   * if registers<15> == '1' then
   *   MemA[address, 4] = PCStoreValue();
   * if wback then R[n] = R[n] + 4 * BitCount(registers);
   * ------------------------------------------------------------------------ *)
  | StoreMultipleIncrementAfter (wback, c, base, rl, _, _) ->
     let floc = get_floc loc in
     let basereg = base#get_register in
     let regcount = rl#get_register_count in
     let rhsexprs = rl#to_multiple_expr floc in
     let rhsexprs = List.map (rewrite_expr floc) rhsexprs in
     let (memassigns, _) =
       List.fold_left
         (fun (acc, off) rhsexpr ->
           let memop = arm_reg_deref ~with_offset:off basereg WR in
           let (memlhs, memlhscmds) = memop#to_lhs floc in
           let cmds1 = floc#get_assign_commands memlhs rhsexpr in
           let defcmds1 = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           (acc @ memlhscmds @ defcmds1 @ cmds1, off + 4))
         ([], 0)
         rhsexprs in
    let wbackassign =
       if wback then
         let (lhs, lhscmds) = base#to_lhs floc in
         let rhs = base#to_expr floc in
         let increm = int_constant_expr (4 * regcount) in
         let newrhs = XOp (XPlus, [rhs; increm]) in
         let wbackcmds = floc#get_assign_commands lhs newrhs in
         let wbackdefcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         lhscmds @ wbackdefcmds @ wbackcmds
       else
         [] in
    let cmds = memassigns @ wbackassign in
    (match c with
     | ACCAlways -> default cmds
     | _ -> make_conditional_commands c cmds)

  (* ---------------------------------------- StoreMultipleIncrementBefore --
   * Stores multiple registers to consecutive memory locations using an
   * address from a base register. The consecutive memory locations start just
   * above this address, and the address of the last of those locations may be
   * written back to the base register.
   *
   * address = R[n] + 4;
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *      MemA[address, 4] = R[i];
   *      address = address + 4;
   * if registers<15> == '1' then
   *   MemA[address, 4] = PCStoreValue();
   * if wback then
   *   R[n] = R[n] + 4 * BitCount(registers);
   * ------------------------------------------------------------------------ *)
  | StoreMultipleIncrementBefore (wback, c, base, rl, _, _) ->
     let floc = get_floc loc in
     let basereg = base#get_register in
     let regcount = rl#get_register_count in
     let rhsexprs = rl#to_multiple_expr floc in
     let rhsexprs = List.map (rewrite_expr floc) rhsexprs in
     let (memassigns, _) =
       List.fold_left
         (fun (acc, off) rhsexpr ->
           let memop = arm_reg_deref ~with_offset:off basereg WR in
           let (memlhs, memlhscmds) = memop#to_lhs floc in
           let cmds1 = floc#get_assign_commands memlhs rhsexpr in
           let defcmds1 = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           (acc @ memlhscmds @ defcmds1 @ cmds1, off + 4))
         ([], 4)
         rhsexprs in
     let wbackassign =
       if wback then
         let (lhs, lhscmds) = base#to_lhs floc in
         let rhs = base#to_expr floc in
         let increm = int_constant_expr (4 + (4 * regcount)) in
         let newrhs = XOp (XPlus, [rhs; increm]) in
         let wbackcmds = floc#get_assign_commands lhs newrhs in
         let wbackdefcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         lhscmds @ wbackdefcmds @ wbackcmds
       else
         [] in
     let cmds = memassigns @ wbackassign in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ---------------------------------------- StoreMultipleDecrementBefore --
   * Stores multiple registers to consecutive memory locations using an address
   * from a base register. The consecutive memory locations end just below this
   * address, and the address of the first of those locations may be written
   * back to the base register.
   *
   * address = R[n] - 4 * BitCount(registers);
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     MemA[address, 4] = R[i];
   *     address = address + 4;
   * if registers<15> == '1' then
   *   MemA[address, 4] = PCStoreValue();
   * if wback then R[n] = R[n] - 4 * BitCount(registers);
   * ------------------------------------------------------------------------ *)
  | StoreMultipleDecrementBefore (wback, c, base, rl, _, _) ->
     let floc = get_floc loc in
     let basereg = base#get_register in
     let regcount = rl#get_register_count in
     let rhsvars = rl#to_multiple_variable floc in
     let (memassigns, _) =
       List.fold_left
         (fun (acc, off) rhsvar ->
           let memop = arm_reg_deref ~with_offset:off basereg WR in
           let (memlhs, memlhscmds) = memop#to_lhs floc in
           let memop1 = arm_reg_deref ~with_offset:(off+1) basereg WR in
           let memlhs1 = memop1#to_variable floc in
           let memop2 = arm_reg_deref ~with_offset:(off+2) basereg WR in
           let memlhs2 = memop2#to_variable floc in
           let memop3 = arm_reg_deref ~with_offset:(off+3) basereg WR in
           let memlhs3 = memop3#to_variable floc in
           let rhsexpr = rewrite_expr floc (XVar rhsvar) in
           let cmds1 = floc#get_assign_commands memlhs rhsexpr in
           let usehigh = get_use_high_vars [rhsexpr] in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[memlhs; memlhs1; memlhs2; memlhs3]
               ~use:[rhsvar]
               ~usehigh:usehigh
               ctxtiaddr in
           (acc @ memlhscmds @ defcmds1 @ cmds1, off + 4))
         ([], -(4 * regcount))
         rhsvars in
     let wbackassign =
       if wback then
         let (lhs, lhscmds) = base#to_lhs floc in
         let rhs = base#to_expr floc in
         let decrem = int_constant_expr (4 * regcount) in
         let newrhs = XOp (XMinus, [rhs; decrem]) in
         let wbackcmds = floc#get_assign_commands lhs newrhs in
         let wbackdefcmds =
           floc#get_vardef_commands
             ~defs:[lhs]
             ~use:(get_register_vars [base])
             ctxtiaddr in
         wbackdefcmds @ wbackcmds
       else
         [] in
     let cmds = memassigns @ wbackassign in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegister (c, rt, rn, rm, mem, _) ->
     let floc = get_floc loc in
     let (vmem, memcmds) = mem#to_lhs floc in
     let xrt = rt#to_expr floc in
     let cmds = memcmds @ (floc#get_assign_commands vmem xrt) in
     let usevars = get_register_vars [rt; rn; rm] in
     let usehigh = get_use_high_vars [xrt] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vmem]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegisterByte (c, rt, rn, rm, mem, _) ->
     let floc = get_floc loc in
     let (vmem, memcmds) = mem#to_lhs floc in
     let xrt = XOp (XXlsb, [rt#to_expr floc]) in
     let cmds = floc#get_assign_commands vmem xrt in
     let usevars = get_register_vars [rt; rn; rm] in
     let usehigh = get_use_high_vars [xrt] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vmem]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = memcmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegisterDual (c, rt, rt2, _, _, mem, mem2) ->
     let floc = get_floc loc in
     let (vmem, memcmds) = mem#to_lhs floc in
     let (vmem2, mem2cmds) = mem2#to_lhs floc in
     let xrt = rt#to_expr floc in
     let xrt2 = rt2#to_expr floc in
     let cmds1 = floc#get_assign_commands vmem xrt in
     let cmds2 = floc#get_assign_commands vmem2 xrt2 in
     let defcmds = floc#get_vardef_commands ~defs:[vmem; vmem2] ctxtiaddr in
     let cmds = memcmds @ mem2cmds @ defcmds @ cmds1 @ cmds2 in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegisterExclusive (c, rd, rt, rn, mem) ->
     let floc = get_floc loc in
     let (vmem,memcmds) = mem#to_lhs floc in
     let (vrd, vrdcmds) = rd#to_lhs floc in
     let xrt = rt#to_expr floc in
     let cmds = floc#get_assign_commands vmem xrt in
     let scmds = floc#get_abstract_commands vrd () in
     let defcmds = floc#get_vardef_commands ~defs:[vmem; vrd] ctxtiaddr in
     let cmds = memcmds @ vrdcmds @ defcmds @ cmds @ scmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegisterHalfword (c, rt, rn, rm, mem, _) ->
     let floc = get_floc loc in
     let (vmem, memcmds) = mem#to_lhs floc in
     let xrt = rt#to_expr floc in
     let cmds = floc#get_assign_commands vmem xrt in
     let usevars = get_register_vars [rt; rn; rm] in
     let usehigh = get_use_high_vars [xrt] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vmem]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = memcmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ------------------------------------------------------------ Subtract -- *
   * if ConditionPassed() then
   *   (result, carry, overflow) = AddWithCarry (R[n], NOT9imm32), '1');
   *   R[d] = result;
   *   if setflags then
   *     APSR.N = result<31>;
   *     APSR.Z = IsZeroBit(result);
   *     APSR.C = carry;
   *     APSR.V = overflow
   * ------------------------------------------------------------------------- *)
  | Subtract (_, c, rd, rn, rm, _, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let usevars = get_register_vars [rn; rm] in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let cmds = floc#get_assign_commands vrd (XOp (XMinus, [xrn; xrm])) in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SubtractCarry(_, _, dst, _, _, _) ->
     let floc = get_floc loc in
     let vdst = dst#to_variable floc in
     let cmds = floc#get_abstract_commands vdst () in
     let defcmds = floc#get_vardef_commands ~defs:[vdst] ctxtiaddr in
     default (defcmds @ cmds)

  | Swap (_, rd, _, _) ->     (* TBD *)
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let cmds = floc#get_abstract_commands vrd () in
     default cmds

  | SwapByte (_, rd, _, _) ->  (* TBD *)
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let cmds = floc#get_abstract_commands vrd () in
     default cmds

  | TableBranchByte _ ->
     default cmds

  | TableBranchHalfword _ ->
     default cmds

  | UnsignedAdd8 (_, rd, rn, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let cmds = floc#get_abstract_commands vrd () in
     let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
     default (defcmds @ cmds)

  | UnsignedBitFieldExtract (c, rd, rn) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrn = rn#to_expr floc in
     let cmds = floc#get_abstract_commands vrd () in
     let usevars = get_register_vars [rn] in
     let usehigh = get_use_high_vars [xrn] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = (defcmds @ cmds) in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedDivide (_, rd, _, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let cmds = floc#get_abstract_commands vrd () in
     let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
     default (defcmds @ cmds)

  | UnsignedExtendAddByte (_, rd, _, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let cmds = floc#get_abstract_commands vrd () in
     let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
     default (defcmds @ cmds)

  | UnsignedExtendAddHalfword (_, rd, _, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let cmds = floc#get_abstract_commands vrd () in
     let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
     default (defcmds @ cmds)

  | UnsignedExtendByte (c, rd, rm, _) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = XOp (XXlsb, [rm#to_expr floc]) in
     let result = xrm in
     let cmds = floc#get_assign_commands vrd result in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedExtendHalfword (c, rd, rm) ->
     let floc = get_floc loc in
     let vrd = rd#to_variable floc in
     let xrm = XOp (XXlsh, [rm#to_expr floc]) in
     let result = xrm in
     let cmds = floc#get_assign_commands vrd result in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars [xrm] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedMultiplyAccumulateLong (_, _, rdlo, rdhi, _, _) ->
     let floc = get_floc loc in
     let vlo = rdlo#to_variable floc in
     let vhi = rdhi#to_variable floc in
     let cmdslo = floc#get_abstract_commands vlo () in
     let cmdshi = floc#get_abstract_commands vhi () in
     let defcmds = floc#get_vardef_commands ~defs:[vlo; vhi] ctxtiaddr in
     default (defcmds @ cmdslo @ cmdshi)

  | UnsignedMultiplyLong (_, c, rdlo, rdhi, rn, rm) ->
     let floc = get_floc loc in
     let vlo = rdlo#to_variable floc in
     let vhi = rdhi#to_variable floc in
     let xrn = rn#to_expr floc in
     let xrm = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars [xrn; xrm] in
     let cmdslo = floc#get_abstract_commands vlo () in
     let cmdshi = floc#get_abstract_commands vhi () in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vlo; vhi]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default (defcmds @ cmdslo @ cmdshi)

  | UnsignedSaturatingSubtract8 (_, rd, _, _) ->
     let floc = get_floc loc in
     let vdst = rd#to_variable floc in
     let cmds = floc#get_abstract_commands vdst () in
     let defcmds = floc#get_vardef_commands ~defs:[vdst] ctxtiaddr in
     default (defcmds @ cmds)

  | VectorAdd _ -> default []

  | VectorBitwiseBitClear _ -> default []

  | VectorBitwiseOr _ -> default []

  | VectorBitwiseNot _ -> default []

  | VCompare (_, _, _, src1, src2) ->
     let floc = get_floc loc in
     let xsrc1 = src1#to_expr floc in
     let xsrc2 = src2#to_expr floc in
     let usevars = get_register_vars [src1; src2] in
     let usehigh = get_use_high_vars [xsrc1; xsrc2] in
     let defcmds =
       floc#get_vardef_commands
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default defcmds

  | VectorConvert (_, _, _, _, dst, src) ->
     let floc = get_floc loc in
     let vdst = dst#to_variable floc in
     let xsrc = src#to_expr floc in
     let usevars = get_register_vars [src] in
     let usehigh = get_use_high_vars [xsrc] in
     let cmds = floc#get_abstract_commands vdst () in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vdst]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | VDivide (_, _, dst, src1, src2) ->
     let floc = get_floc loc in
     let vdst = dst#to_variable floc in
     let xsrc1 = src1#to_expr floc in
     let xsrc2 = src2#to_expr floc in
     let usevars = get_register_vars [src1; src2] in
     let usehigh = get_use_high_vars [xsrc1; xsrc2] in
     let cmds = floc#get_abstract_commands vdst () in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vdst]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | VectorDuplicate _ -> default []

  | VectorMove (_, _, [dst; src]) ->
     let floc = get_floc loc in
     let vdst = dst#to_variable floc in
     let xsrc = src#to_expr floc in
     let usevars = get_register_vars [src] in
     let usehigh = get_use_high_vars [xsrc] in
     let cmds = floc#get_abstract_commands vdst () in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vdst]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | VLoadRegister(c, dst, rn, mem) ->
     let floc = get_floc loc in
     let vdst = dst#to_variable floc in
     let xrn = rn#to_expr floc in
     let xmem = mem#to_expr floc in
     let usevars = get_register_vars [rn] in
     let usehigh = get_use_high_vars [xrn; xmem] in
     let cmds = floc#get_abstract_commands vdst () in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vdst]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VMoveRegisterStatus (_, dst, src) ->
     let floc = get_floc loc in
     let vdst = dst#to_variable floc in
     let xsrc = src#to_expr floc in
     let usevars = get_register_vars [src] in
     let usehigh = get_use_high_vars [xsrc] in
     let cmds = floc#get_abstract_commands vdst () in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vdst]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | VectorMultiply _ -> default []

  | VectorNegate _ -> default []

  | VectorReverseDoublewords _ -> default []

  | VectorReverseWords _ -> default []

  | VectorReverseHalfwords _ -> default []

  | VStoreRegister(c, dd, rn, mem) ->
     let floc = get_floc loc in
     let (vmem, memcmds) = mem#to_lhs floc in
     let xdd = dd#to_expr floc in
     let cmds = memcmds @ (floc#get_abstract_commands vmem ()) in
     let usevars = get_register_vars [dd; rn] in
     let usehigh = get_use_high_vars [xdd] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vmem]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorSubtract _ -> default []

  | VectorTranspose _ -> default []

  | instr ->
     let _ =
       chlog#add
         "no semantics"
         (LBLOCK [loc#toPretty;
                  STR ": ";
                  STR (arm_opcode_to_string instr)]) in
     default []
        

class arm_assembly_function_translator_t (f:arm_assembly_function_int) =
object (self)

  val finfo = get_function_info f#get_address
  val funloc =
    make_location {loc_faddr = f#get_address; loc_iaddr = f#get_address}
  val exitlabel =
    make_code_label
      ~modifier:"exit"
      (make_location {loc_faddr = f#get_address; loc_iaddr = f#get_address})#ci
  val codegraph = make_code_graph ()

  method translate_block (block:arm_assembly_block_int) exitLabel =
    let codepc = make_arm_code_pc block in
    let blocklabel = make_code_label block#get_context_string in
    let rec aux cmds =
      let (nodes,edges,newcmds) =
        try
          translate_arm_instruction ~funloc ~codepc ~blocklabel ~exitlabel ~cmds
        with
        | BCH_failure p ->
           let msg =
             LBLOCK [STR "function: ";
                     funloc#toPretty;
                     STR ", block: ";
                     blocklabel#toPretty;
                     STR ": ";
                     p] in
           begin
             ch_error_log#add "translate arm block" msg;
             raise (BCH_failure msg)
           end in
      match nodes with
      | [] ->
         if codepc#has_more_instructions then
           aux newcmds
         (*
         else if codepc#has_conditional_successor then
           let (testloc,jumploc,theniaddr,elseiaddr,testexpr) =
             codepc#get_conditional_successor_info in
           let transaction = package_transaction finfo blocklabel newcmds in
           let (nodes,edges) =
             make_condition
               ~testloc ~jumploc ~theniaddr ~elseiaddr ~blocklabel ~testexpr in
           ((blocklabel, [transaction])::nodes, edges) *)
         else
           let transaction = package_transaction finfo blocklabel newcmds in
           let nodes = [(blocklabel, [transaction])] in
           let edges =
             List.map
               (fun succ ->
                 let succlabel = make_code_label succ in
                 (blocklabel, succlabel)) codepc#get_block_successors in
           let edges =
             match edges with
             | [] -> (blocklabel, exitLabel) :: edges
             | _ -> edges in
           (nodes, edges)
      | _ -> (nodes,edges) in
    let _ = finfo#env#start_transaction in
    let (nodes, edges) = aux [] in
    begin
      List.iter (fun (label, node) -> codegraph#add_node label node) nodes;
      List.iter (fun (src, tgt) -> codegraph#add_edge src tgt) edges
    end

  method private create_arg_deref_asserts
                   (finfo: function_info_int)
                   (reg: arm_reg_t)
                   (offset: int)
                   (optlb: int option)
                   (optub: int option) =
    let env = finfo#env in
    let reqN () = env#mk_num_temp in
    let reqC = env#request_num_constant in
    let ri = env#mk_initial_register_value (ARMRegister reg) in
    let _ = finfo#add_base_pointer ri in
    let rbase = env#mk_base_variable_reference ri in
    let memvar = env#mk_memory_variable rbase (mkNumerical offset) in
    let cmdasserts cxpr =
      let (cmds, bxpr) = xpr_to_boolexpr reqN reqC cxpr in
      cmds @ [ASSERT bxpr] in
    match (optlb, optub) with
    | (Some lb, Some ub) when lb = ub ->
       let cxpr = XOp (XEq, [XVar memvar; int_constant_expr lb]) in
       cmdasserts cxpr
    | (Some lb, Some ub) ->
       let c1xpr = XOp (XGe, [XVar memvar; int_constant_expr lb]) in
       let c2xpr = XOp (XLe, [XVar memvar; int_constant_expr ub]) in
       (cmdasserts c1xpr) @ (cmdasserts c2xpr)
    | (Some lb, _) ->
       let cxpr = XOp (XGe, [XVar memvar; int_constant_expr lb]) in
       cmdasserts cxpr
    | (_, Some ub) ->
       let cxpr = XOp (XLe, [XVar memvar; int_constant_expr ub]) in
       cmdasserts cxpr
    | _ -> []

  method private create_arg_scalar_asserts
                   (finfo: function_info_int)
                   (var: variable_t)
                   (optlb: int option)
                   (optub: int option) =
    let env = finfo#env in
    let reqN () = env#mk_num_temp in
    let reqC = env#request_num_constant in
    (* let regvar = env#mk_arm_register_variable reg in *)
    let cmdasserts cxpr =
      let (cmds, bxpr) = xpr_to_boolexpr reqN reqC cxpr in
      cmds @ [ASSERT bxpr] in
    match (optlb, optub) with
    | (Some lb, Some ub) when lb = ub ->
       let cxpr = XOp (XEq, [XVar var; int_constant_expr lb]) in
       cmdasserts cxpr
    | (Some lb, Some ub) ->
       let c1xpr = XOp (XGe, [XVar var; int_constant_expr lb]) in
       let c2xpr = XOp (XLe, [XVar var; int_constant_expr ub]) in
       (cmdasserts c1xpr) @ (cmdasserts c2xpr)
    | (Some lb, _) ->
       let cxpr = XOp (XGe, [XVar var; int_constant_expr lb]) in
       cmdasserts cxpr
    | (_, Some ub) ->
       let cxpr = XOp (XLe, [XVar var; int_constant_expr ub]) in
       cmdasserts cxpr
    | _ -> []


  method private create_arg_asserts
                   (finfo: function_info_int)
                   (c: (string * int option * int option * int option)) =
    let (name, optoffset, optlb, optub) = c in
    if (String.length name) > 1 && (String.sub name 0 2) = "0x" then
      let gv = finfo#env#mk_global_variable (string_to_doubleword name)#to_numerical in
      (* let gv_in = finfo#env#mk_initial_memory_value gv in *)
      self#create_arg_scalar_asserts finfo gv optlb optub
    else
      let reg = armreg_from_string name in
      match optoffset with
      | Some offset -> self#create_arg_deref_asserts finfo reg offset optlb optub
      | _ ->
         let regvar = finfo#env#mk_arm_register_variable reg in
         self#create_arg_scalar_asserts finfo regvar optlb optub

  method private create_args_asserts
                   (finfo: function_info_int)
                   (argconstraints:
                      (string * int option * int option * int option) list) =
    List.concat
      (List.map (fun c -> self#create_arg_asserts finfo c) argconstraints)

  method private get_entry_cmd
                   (argconstraints:
                      (string * int option * int option * int option) list) =
    let env = finfo#env in
    let _ = env#start_transaction in
    let freeze_initial_register_value (reg:arm_reg_t) =
      let regVar = env#mk_arm_register_variable reg in
      let initVar = env#mk_initial_register_value (ARMRegister reg) in
      let _ =
        ignore(finfo#env#mk_symbolic_variable ~domains:["reachingdefs"] initVar) in
      ASSERT (EQ (regVar, initVar)) in
    let freeze_external_memory_values (v:variable_t) =
      let initVar = env#mk_initial_memory_value v in
      let _ =
        ignore(finfo#env#mk_symbolic_variable ~domains:["reachingdefs"] initVar) in
      ASSERT (EQ (v, initVar)) in
    let rAsserts = List.map freeze_initial_register_value arm_regular_registers in
    let externalMemvars = env#get_external_memory_variables in
    let externalMemvars = List.filter env#has_constant_offset externalMemvars in
    let _ =
      chlog#add
        "external memory variables"
        (LBLOCK [
             finfo#get_address#toPretty;
             pretty_print_list
               externalMemvars (fun v -> v#toPretty) " [" ", " "]"]) in
    let mAsserts = List.map freeze_external_memory_values externalMemvars in
    let sp0 = env#mk_initial_register_value (ARMRegister ARSP) in
    let _ = finfo#add_base_pointer sp0 in

    (* ----- test code --- *)
    let argasserts = self#create_args_asserts finfo argconstraints in

    let unknown_scalar = env#mk_special_variable "unknown_scalar" in
    let initializeScalar =
      DOMAIN_OPERATION
        ([valueset_domain],
         {op_name = new symbol_t "set_unknown_scalar";
          op_args = [("unknown_scalar", unknown_scalar, WRITE)]}) in
    let initializeBasePointerOperations:cmd_t list =
      List.map (fun base ->
          DOMAIN_OPERATION
            ([valueset_domain],
             {op_name = new symbol_t "initialize";
              op_args = [(base#getName#getBaseName, base, READ)]}))
        finfo#get_base_pointers in
    let initialize_reaching_defs: cmd_t list =
      List.map (fun v ->
          DOMAIN_OPERATION
            (["reachingdefs"],
             {op_name = new symbol_t ~atts:["init"] "def";
              op_args = [("dst", v, WRITE)]}))
        (finfo#env#get_domain_sym_variables "reachingdefs") in
    let initialize_flag_reaching_defs: cmd_t list =
      List.map (fun v ->
          DOMAIN_OPERATION
            (["flagreachingdefs"],
             {op_name = new symbol_t ~atts:["init"] "def";
              op_args = [("dst", v, WRITE)]}))
         (finfo#env#get_domain_sym_variables "flagreachingdefs") in
    let constantAssigns = env#end_transaction in
    let cmds =
      constantAssigns
      @ argasserts
      @ rAsserts
      @ mAsserts
      @ [ initializeScalar ]
      @ initializeBasePointerOperations
      @ initialize_reaching_defs
      @ initialize_flag_reaching_defs in
    TRANSACTION (new symbol_t "entry", LF.mkCode cmds, None)

  method private get_exit_cmd =
    let env = finfo#env in
    let _ = env#start_transaction in
    let cmds: cmd_t list =
      List.map (fun v ->
          DOMAIN_OPERATION
            (["defuse"],
             {op_name = new symbol_t ~atts:["exit"] "use";
              op_args = [("dst", v, WRITE)]}))
        (finfo#env#get_domain_sym_variables "defuse") in
    let cmdshigh: cmd_t list =
      let symvars = finfo#env#get_domain_sym_variables "defusehigh" in
      let symvars =
        List.filter (fun v ->
            if v#getName#getSeqNumber >= 0 then
              let numvar = finfo#env#get_symbolic_num_variable v in
              not (finfo#env#is_register_variable numvar
                   || finfo#env#is_local_variable numvar)
            else
              false) symvars in
      List.map (fun v ->
          DOMAIN_OPERATION
            (["defusehigh"],
             {op_name = new symbol_t ~atts:["exit"] "use_high";
              op_args = [("dst", v, WRITE)]})) symvars in
    let constantAssigns = env#end_transaction in
    let cmds = constantAssigns @ cmds @ cmdshigh in
    TRANSACTION (new symbol_t "exit", LF.mkCode cmds, None)

  method translate =
    let faddr = f#get_address in
    let firstInstrLabel = make_code_label funloc#ci in
    let entryLabel = make_code_label ~modifier:"entry" funloc#ci in
    let exitLabel = make_code_label ~modifier:"exit" funloc#ci in
    let procname = make_arm_proc_name faddr in
    let _ = f#iter (fun b -> self#translate_block b exitLabel) in
    let argconstraints =
      system_info#get_argument_constraints faddr#to_hex_string in
    let entrycmd = self#get_entry_cmd argconstraints in
    let exitcmd = self#get_exit_cmd in
    let scope = finfo#env#get_scope in
    let _ = codegraph#add_node entryLabel [entrycmd] in
    let _ = codegraph#add_node exitLabel [exitcmd] in
    let _ = codegraph#add_edge entryLabel firstInstrLabel in
    let cfg = codegraph#to_cfg entryLabel exitLabel in
    let body = LF.mkCode [CFG (procname, cfg)] in
    let proc = LF.mkProcedure procname [] [] scope body in
    (* let _ = pr_debug [proc#toPretty; NL] in *)
    arm_chif_system#add_arm_procedure proc

end

    
let translate_arm_assembly_function (f:arm_assembly_function_int) =
  let translator = new arm_assembly_function_translator_t f in
  try
    translator#translate
  with
  | CHFailure p
    | BCH_failure p ->
     let msg = LBLOCK [ STR "Failure in translation: "; p] in
     raise (BCH_failure msg)

(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs LLC

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
open BCHBCTypes
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

(* bchlibpower32 *)
open BCHPowerAssemblyBlock
open BCHPowerAssemblyFunction
open BCHPowerAssemblyFunctions
open BCHPowerAssemblyInstruction
open BCHPowerAssemblyInstructions
open BCHPowerCHIFSystem
open BCHPowerCodePC
open BCHPowerConditionalExpr
open BCHPowerOpcodeRecords
open BCHPowerOperand
open BCHPowerTypes
open BCHDisassemblePower


module B = Big_int_Z
module LF = CHOnlineCodeSet.LanguageFactory
module TR = CHTraceResult


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


let make_tests
      ~(condinstr: pwr_assembly_instruction_int)
      ~(testinstr: pwr_assembly_instruction_int)
      ~(condloc: location_int)
      ~(testloc: location_int) =
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
  let env = testfloc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let (frozenVars, optboolxpr) =
    pwr_conditional_expr
      ~condopc:condinstr#get_opcode
      ~testopc:testinstr#get_opcode
      ~condloc
      ~testloc in

  let convert_to_chif expr =
    let (cmds, bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ [ASSERT bxpr] in

  let convert_to_assert expr =
    let vars = variables_in_expr expr in
    let varssize = List.length vars in
    let xprs =
      if varssize = 1 then
        let var = List.hd vars in
        let extxprs = condfloc#inv#get_external_exprs var in
        let extxprs =
          List.map (fun e -> substitute_expr (fun v -> e) expr) extxprs in
        match extxprs with
        | [] -> [expr]
        | _ -> extxprs
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


let make_condition
      ~(condinstr: pwr_assembly_instruction_int)
      ~(testinstr: pwr_assembly_instruction_int)
      ~(condloc: location_int)
      ~(testloc: location_int)
      ~(blocklabel: symbol_t)
      ~(thenaddr: ctxt_iaddress_t)
      ~(elseaddr: ctxt_iaddress_t) =
  let thenlabel = make_code_label thenaddr in
  let elselabel = make_code_label elseaddr in
  let (frozenVars, tests) =
    make_tests ~condloc ~testloc ~condinstr ~testinstr in
  match tests with
  | Some (thentest, elsetest) ->
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
       [(blocklabel, elsetestlabel); (elsetestlabel, elselabel)] in
     ([(thentestlabel, thennode); (elsetestlabel, elsenode)],
      thenedges @ elseedges)
  | _ ->
     let _ =
       chlog#add
         "make_condition: no tests"
         (LBLOCK [
              STR "cond: ";
              condloc#toPretty;
              STR ": ";
              condinstr#toPretty;
              STR "; ";
              testloc#toPretty;
              STR ": ";
              testinstr#toPretty]) in
     let abstractlabel =
       make_code_label ~modifier:"abstract" testloc#ci in
     let transaction =
       TRANSACTION (abstractlabel, LF.mkCode [ABSTRACT_VARS frozenVars], None) in
     let edges = [
         (blocklabel, abstractlabel);
         (abstractlabel, thenlabel);
         (abstractlabel, elselabel)] in
     ([(abstractlabel, [transaction])], edges)


let translate_pwr_instruction
      ~(funloc: location_int)
      ~(codepc: pwr_code_pc_int)
      ~(blocklabel: symbol_t)
      ~(exitlabel: symbol_t)
      ~(cmds: cmd_t list) =
  let (ctxtiaddr, instr) = codepc#get_next_instruction in
  let faddr = funloc#f in
  let finfo = get_function_info faddr in
  let loc = ctxt_string_to_location faddr ctxtiaddr in
  let invlabel = get_invariant_label loc in
  let invop = OPERATION {op_name = invlabel; op_args = []} in
  let bwdinvlabel = get_invariant_label ~bwd:true loc in
  let bwdinvop = OPERATION {op_name = bwdinvlabel; op_args = []} in
  let frozenAsserts =
    List.map (fun (v, fv) -> ASSERT (EQ (v, fv)))
      (finfo#get_test_variables ctxtiaddr) in

  (*
  let rewrite_expr floc (x: xpr_t): xpr_t =
    let xpr = floc#inv#rewrite_expr x floc#env#get_variable_comparator in
    let rec expand x =
      match x with
      | XVar v when floc#env#is_symbolic_value v ->
         expand (floc#env#get_symbolic_value_expr v)
      | XOp (op,l) -> XOp (op, List.map expand l)
      | _ -> x in
    simplify_xpr (expand xpr) in
   *)

  let floc = get_floc loc in

  let get_register_vars (ops: pwr_operand_int list) =
    List.fold_left (fun acc op ->
        if op#is_gp_register || op#is_sp_register || op#is_register_field then
          (op#to_variable floc) :: acc
        else if op#is_ind_register then
          (floc#f#env#mk_pwr_gp_register_variable op#get_ind_base_register) :: acc
        else if op#is_xind_register then
          (List.map
             floc#f#env#mk_pwr_gp_register_variable
             [op#get_xind_base_register; op#get_xind_index_register]) @ acc
        else
          acc) []  ops in

  let get_use_high_vars (xprs: xpr_t list):variable_t list =
    let inv = floc#inv in
    let comparator = floc#env#get_variable_comparator in
    List.fold_left (fun acc x ->
        let xw = inv#rewrite_expr x comparator in
        let xs = simplify_xpr xw in
        (vars_in_expr_list [xs]) @ acc) [] xprs in

  let default newcmds =
    ([], [], cmds @ frozenAsserts @ (invop :: newcmds) @ [bwdinvop]) in

  match instr#get_opcode with

  | BranchConditional (_, _, _, _, tgt)
    | CBranchEqual (_, _, _, _, _, _, tgt)
    | CBranchGreaterThan (_, _, _, _, _, _, tgt)
    | CBranchLessEqual (_, _, _, _, _, _, tgt)
    | CBranchLessThan (_, _, _, _, _, _, tgt)
    | CBranchNotEqual (_, _, _, _, _, _, tgt) when tgt#is_absolute_address ->
     let thenaddr = (make_i_location loc tgt#get_absolute_address)#ci in
     let elseaddr = codepc#get_false_branch_successor in
     let cmds = cmds @ [invop] in
     let transaction = package_transaction finfo blocklabel cmds in
     if finfo#has_associated_cc_setter ctxtiaddr then
       let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
       let testloc = ctxt_string_to_location faddr testiaddr in
       let testaddr = (ctxt_string_to_location faddr testiaddr)#i in
       let testinstr =
         fail_tvalue
           (trerror_record
              (LBLOCK [STR "Internal error in make_instr_tests"]))
           (get_pwr_assembly_instruction testaddr) in
       let (nodes, edges) =
         make_condition
           ~condinstr:instr
           ~testinstr
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

  | Add (_, _, _, rd, ra, rb, _, _, _) ->
     let vrd = rd#to_variable floc in
     let xra = ra#to_expr floc in
     let xrb = rb#to_expr floc in
     let xrhs = XOp (XPlus, [xra; xrb]) in
     let cmds = floc#get_assign_commands vrd xrhs in
     let usevars = get_register_vars [ra; rb] in
     let usehigh = get_use_high_vars [xra; xrb] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | AddImmediate (_, shifted, _, _, _, rd, ra, simm, cr) ->
     let vrd = rd#to_variable floc in
     let xra = ra#to_expr floc in
     let xsimm =
       if shifted then
         simm#to_shifted_expr 16
       else
         simm#to_expr floc in
     let xrhs = XOp (XPlus, [xra; xsimm]) in
     let cmds = floc#get_assign_commands vrd xrhs in
     let usevars = get_register_vars [ra] in
     let usehigh = get_use_high_vars [xra] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | BranchLink (_, tgt, _) when tgt#is_absolute_address ->
     let floc = get_floc loc in
     let argvars =
       List.map
         floc#f#env#mk_pwr_gp_register_variable
         [3; 4; 5; 6; 7; 8; 9; 10] in
     let args = List.map snd floc#get_pwr_call_arguments in
     let (defs, use, usehigh) =
       let usehigh = get_use_high_vars args in
       let argcount = List.length args in
       let use =
         List.map
           floc#f#env#mk_pwr_gp_register_variable
           (List.init argcount (fun i -> i)) in
       ([List.hd argvars], usehigh, use) in
     let cmds = floc#get_pwr_call_commands in
     let defcmds =
       floc#get_vardef_commands
         ~defs:defs
         ~clobbers:(List.tl argvars)
         ~use
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | ClearLeftWordImmediate (_, _, ra, rs, mb) ->
     let vra = ra#to_variable floc in
     let xrs = rs#to_expr floc in
     let cmds = floc#get_abstract_commands vra () in
     let usevars = get_register_vars [rs] in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vra]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | DivideWordUnsigned (_, _, _, rd, ra, rb, _, _, _) ->
     let vrd = rd#to_variable floc in
     let xra = ra#to_expr floc in
     let xrb = rb#to_expr floc in
     let xrhs = XOp (XDiv, [xra; xrb]) in
     let cmds = floc#get_assign_commands vrd xrhs in
     let usevars = get_register_vars [ra; rb] in
     let usehigh = get_use_high_vars [xra; xrb] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | ExtendSignHalfword (_, _, ra, rs, _) ->
     let vra = ra#to_variable floc in
     let xrs = rs#to_expr floc in
     let cmds = floc#get_assign_commands vra xrs in
     let usevars = get_register_vars [rs] in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vra]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | ExtractRightJustifyWordImmediate (_, _, ra, rs, n, b, _) ->
     let vra = ra#to_variable floc in
     let xrs = rs#to_expr floc in
     let cmds = floc#get_abstract_commands vra () in
     let usevars = get_register_vars [rs] in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vra]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | LoadImmediate (_, _, shifted, rd, imm) ->
     let vrd = rd#to_variable floc in
     let ximm =
       if shifted then
         imm#to_shifted_expr 16
       else
         imm#to_expr floc in
     let cmds = floc#get_assign_commands vrd ximm in
     let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
     default (defcmds @ cmds)

  | LoadByteZero (_, update, rd, ra, mem) ->
     let vrd = rd#to_variable floc in
     let rhs =
       floc#inv#rewrite_expr (mem#to_expr floc)
         floc#env#get_variable_comparator in
     let cmds = floc#get_assign_commands vrd rhs in
     let usevars = get_register_vars [ra] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
       ctxtiaddr in
     let updatecmds =
       if update then
         let vra = ra#to_variable floc in
         let addr = mem#to_address floc in
         let udefcmds = floc#get_vardef_commands ~defs:[vra] ctxtiaddr in
         let ucmds = floc#get_assign_commands vra addr in
         udefcmds @ ucmds
       else
         [] in
     default (defcmds @ cmds @ updatecmds)

  | LoadHalfwordZero (_, update, rd, ra, mem) ->
     let vrd = rd#to_variable floc in
     let rhs =
       floc#inv#rewrite_expr (mem#to_expr floc)
         floc#env#get_variable_comparator in
     let cmds = floc#get_assign_commands vrd rhs in
     let usevars = get_register_vars [ra] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
       ctxtiaddr in
     let updatecmds =
       if update then
         let vra = ra#to_variable floc in
         let addr = mem#to_address floc in
         let udefcmds = floc#get_vardef_commands ~defs:[vra] ctxtiaddr in
         let ucmds = floc#get_assign_commands vra addr in
         udefcmds @ ucmds
       else
         [] in
     default (defcmds @ cmds @ updatecmds)

  | LoadWordZero (_, update, rd, ra, mem) ->
     let vrd = rd#to_variable floc in
     let rhs =
       floc#inv#rewrite_expr (mem#to_expr floc)
         floc#env#get_variable_comparator in
     let cmds = floc#get_assign_commands vrd rhs in
     let usevars = get_register_vars [ra] in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
       ctxtiaddr in
     let updatecmds =
       if update then
         let vra = ra#to_variable floc in
         let addr = mem#to_address floc in
         let udefcmds = floc#get_vardef_commands ~defs:[vra] ctxtiaddr in
         let ucmds = floc#get_assign_commands vra addr in
         udefcmds @ ucmds
       else
         [] in
     default (defcmds @ cmds @ updatecmds)

  | MoveFromLinkRegister (_, rd, lr) ->
     let vrd = rd#to_variable floc in
     let xlr = lr#to_expr floc in
     let cmds = floc#get_assign_commands vrd xlr in
     let usevars = get_register_vars [lr] in
     let usehigh = get_use_high_vars [xlr] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | MoveRegister (_, _, rd, rs) ->
     let vrd = rd#to_variable floc in
     let xrs = rs#to_expr floc in
     let cmds = floc#get_assign_commands vrd xrs in
     let usevars = get_register_vars [rs] in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | MoveToLinkRegister (_, lr, rs) ->
     let vlr = lr#to_variable floc in
     let xrs = rs#to_expr floc in
     let cmds = floc#get_assign_commands vlr xrs in
     let usevars = get_register_vars [rs] in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vlr]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | Or (_, _, ra, rs, rb, _) ->
     let vra = ra#to_variable floc in
     let xrs = rs#to_expr floc in
     let xrb = rb#to_expr floc in
     let xrhs = XOp (XBOr, [xrs; xrb]) in
     let cmds = floc#get_assign_commands vra xrhs in
     let usevars = get_register_vars [rs; rb] in
     let usehigh = get_use_high_vars [xrhs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vra]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | OrImmediate (_, _, shifted, _, ra, rs, uimm, _) ->
     let vra = ra#to_variable floc in
     let xrs = rs#to_expr floc in
     let xuimm =
       if shifted then
         uimm#to_shifted_expr 16
       else
         uimm#to_expr floc in
     let rhs = XOp (XBOr, [xrs; xuimm]) in
     let cmds = floc#get_assign_commands vra rhs in
     let usevars = get_register_vars [rs] in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vra]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | RotateLeftWordImmediateAndMask (_, _, ra, rs, sh, _, _, _) ->
     let vra = ra#to_variable floc in
     let xrs = rs#to_expr floc in
     let cmds = floc#get_abstract_commands vra () in
     let usevars = get_register_vars [rs] in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vra]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | ShiftLeftWordImmediate (_, _, ra, rs, sh, _) ->
     let vra = ra#to_variable floc in
     let xrs = rs#to_expr floc in
     let cmds = floc#get_abstract_commands vra () in
     let usevars = get_register_vars [rs] in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vra]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | StoreByte (_, update, rs, ra, mem) ->
     let (vmem, memcmds) = mem#to_lhs floc in
     let xrs = rs#to_expr floc in
     let xra = ra#to_expr floc in
     let cmds = floc#get_assign_commands vmem xrs in
     let usevars = get_register_vars [rs; ra] in
     let usehigh = get_use_high_vars [xrs; xra] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vmem]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     let updatecmds =
       if update then
         let vra = ra#to_variable floc in
         let addr = mem#to_address floc in
         let ucmds = floc#get_assign_commands vra addr in
         let udefcmds = floc#get_vardef_commands ~defs:[vra] ctxtiaddr in
         (udefcmds @ ucmds)
       else
         [] in
     default (defcmds @ memcmds @ cmds @ updatecmds)

  | StoreHalfword (_, update, rs, ra, mem) ->
     let (vmem, memcmds) = mem#to_lhs floc in
     let xrs = rs#to_expr floc in
     let xra = ra#to_expr floc in
     let cmds = floc#get_assign_commands vmem xrs in
     let usevars = get_register_vars [rs; ra] in
     let usehigh = get_use_high_vars [xrs; xra] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vmem]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     let updatecmds =
       if update then
         let vra = ra#to_variable floc in
         let addr = mem#to_address floc in
         let ucmds = floc#get_assign_commands vra addr in
         let udefcmds = floc#get_vardef_commands ~defs:[vra] ctxtiaddr in
         (udefcmds @ ucmds)
       else
         [] in
     default (defcmds @ memcmds @ cmds @ updatecmds)

  | StoreWord (_, update, rs, ra, mem) ->
     let (vmem, memcmds) = mem#to_lhs floc in
     let xrs = rs#to_expr floc in
     let xra = ra#to_expr floc in
     let cmds = floc#get_assign_commands vmem xrs in
     let usevars = get_register_vars [rs; ra] in
     let usehigh = get_use_high_vars [xrs; xra] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vmem]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     let updatecmds =
       if update then
         let vra = ra#to_variable floc in
         let addr = mem#to_address floc in
         let ucmds = floc#get_assign_commands vra addr in
         let udefcmds = floc#get_vardef_commands ~defs:[vra] ctxtiaddr in
         (udefcmds @ ucmds)
       else
         [] in
     default (defcmds @ memcmds @ cmds @ updatecmds)

  | SubtractFrom (_, _, _, rd, ra, rb, _, _, _) ->
     let vrd = rd#to_variable floc in
     let xra = ra#to_expr floc in
     let xrb = rb#to_expr floc in
     let xrhs = XOp (XMinus, [xrb; xra]) in
     let cmds = floc#get_assign_commands vrd xrhs in
     let usevars = get_register_vars [ra; rb] in
     let usehigh = get_use_high_vars [xra; xrb] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | opc ->
     let _ =
       chlog#add
         "no semantics"
         (LBLOCK [
              loc#toPretty;
              STR ": ";
              STR (pwr_opcode_to_string opc)]) in
     default []

  
class pwr_assembly_function_translator_t (f: pwr_assembly_function_int) =
object (self)
     
  val finfo = get_function_info f#faddr
  val funloc =
    make_location {loc_faddr = f#faddr; loc_iaddr = f#faddr}
  val exitlabel =
    make_code_label
      ~modifier:"exit"
      (make_location {loc_faddr = f#faddr; loc_iaddr=f#faddr})#ci
  val codegraph = make_code_graph ()
                
  method translate_block (block: pwr_assembly_block_int) exitLabel =
    let codepc = make_pwr_code_pc block in
    let blocklabel = make_code_label block#context_string in
    let rec aux cmds =
      let (nodes, edges, newcmds) =
        try
          translate_pwr_instruction
            ~funloc ~codepc ~blocklabel ~exitlabel ~cmds
        with
        | BCH_failure p ->
           let msg =
             LBLOCK [
                 STR "function: ";
                 funloc#toPretty;
                 STR ", block ";
                 blocklabel#toPretty;
                 STR ": ";
                 p] in
           begin
             ch_error_log#add "translate pwr block" msg;
             raise (BCH_failure msg)
           end in
      match nodes with
      | [] ->
         if codepc#has_more_instructions then
           aux newcmds
         else
           let transaction = package_transaction finfo blocklabel newcmds in
           let nodes = [(blocklabel, [transaction])] in
           let edges =
             List.map
               (fun succ ->
                 let succlabel = make_code_label succ in
                 (blocklabel, succlabel)) codepc#block_successors in
           let edges =
             match edges with
             | [] -> (blocklabel, exitLabel) :: edges
             | _ -> edges in
           (nodes, edges)
      | _ -> (nodes, edges) in
    let _ = finfo#env#start_transaction in
    let (nodes, edges) = aux [] in
    begin
      List.iter (fun (label, node) -> codegraph#add_node label node) nodes;
      List.iter (fun (src, tgt) -> codegraph#add_edge src tgt) edges
    end

  method private get_entry_cmd
                   (argconstraints:
                      (string * int option * int option * int option) list) =
    let env = finfo#env in
    let _ = env#start_transaction in
    let freeze_initial_gp_register_value (index: int) =
      let regvar = env#mk_pwr_gp_register_variable index in
      let initvar = env#mk_initial_register_value (PowerGPRegister index) in
      let _ =
        ignore
          (finfo#env#mk_symbolic_variable ~domains:["reachingdefs"] initvar) in
      ASSERT (EQ (regvar, initvar)) in
    let freeze_initial_sp_register_value (r: pwr_special_reg_t) =
      let regvar = env#mk_pwr_sp_register_variable r in
      let initvar = env#mk_initial_register_value (PowerSPRegister r) in
      let _ =
        ignore
          (finfo#env#mk_symbolic_variable ~domains:["reachingdefs"] initvar) in
      ASSERT (EQ (regvar, initvar)) in
    let freeze_external_memory_values (v: variable_t) =
      let initVar = env#mk_initial_memory_value v in
      let _ =
        ignore (finfo#env#mk_symbolic_variable ~domains:["reachingdefs"] initVar) in
      ASSERT (EQ (v, initVar)) in
    let gprAsserts =
      List.map freeze_initial_gp_register_value (List.init 32 (fun i -> i)) in
    let sprAsserts =
      List.map freeze_initial_sp_register_value pwr_special_registers in
    let externalMemvars = env#get_external_memory_variables in
    let externalMemvars = List.filter env#has_constant_offset externalMemvars in
    let memAsserts =
      List.map freeze_external_memory_values externalMemvars in
    let sp0 = env#mk_initial_register_value (PowerGPRegister 1) in
    let _ = finfo#add_base_pointer sp0 in

    let unknown_scalar = env#mk_special_variable "unknown_scalar" in
    let initialize_scalar =
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
    let constantAssigns = env#end_transaction in
    let cmds =
      constantAssigns
      @ gprAsserts
      @ sprAsserts
      @ memAsserts
      @ [initialize_scalar]
      @ initializeBasePointerOperations
      @ initialize_reaching_defs in
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
    let faddr = f#faddr in
    let firstlabel = make_code_label funloc#ci in
    let entrylabel = make_code_label ~modifier:"entry" funloc#ci in
    let exitlabel = make_code_label ~modifier:"exit" funloc#ci in
    let procname = make_pwr_proc_name faddr in
    let _ = f#iter (fun b -> self#translate_block b exitlabel) in
    let entrycmd = self#get_entry_cmd [] in
    let exitcmd = self#get_exit_cmd in
    let scope = finfo#env#get_scope in
    let _ = codegraph#add_node entrylabel [entrycmd] in
    let _ = codegraph#add_node exitlabel [exitcmd] in
    let _ = codegraph#add_edge entrylabel firstlabel in
    let cfg = codegraph#to_cfg entrylabel exitlabel in
    let body = LF.mkCode [CFG (procname, cfg)] in
    let proc = LF.mkProcedure procname ~signature:[] ~bindings:[] ~scope ~body in
    pwr_chif_system#add_pwr_procedure proc

end


let translate_pwr_assembly_function (f: pwr_assembly_function_int) =
  let translator = new pwr_assembly_function_translator_t f in
  try
    translator#translate
  with
  | CHFailure p
    | BCH_failure p ->
     let msg =
       LBLOCK [
           STR "Failure in translation of ";
           f#faddr#toPretty;
           STR ": ";
           p] in
     raise (BCH_failure msg)

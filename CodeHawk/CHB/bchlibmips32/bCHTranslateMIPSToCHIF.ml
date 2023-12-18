(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open BCHBCTypeUtil
open BCHCallTarget
open BCHCodegraph
open BCHCPURegisters
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummary
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant
open BCHMemoryReference
open BCHSpecializations
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities
open BCHVariable

(* bchlibmips32 *)
open BCHMIPSAssemblyBlock
open BCHMIPSAssemblyFunction
open BCHMIPSAssemblyFunctions
open BCHMIPSAssemblyInstruction
open BCHMIPSAssemblyInstructions
open BCHMIPSCodePC
open BCHDisassembleMIPS
open BCHMIPSCHIFSystem
open BCHMIPSTypes
open BCHMIPSOperand
open BCHMIPSOpcodeRecords

module LF = CHOnlineCodeSet.LanguageFactory

let valueset_domain = "valuesets"
let x2p = xpr_formatter#pr_expr

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let get_multiplier (n:numerical_t) =
  int_constant_expr (pow 2 n#toInt)

(* special operation semantics *)
let op_not         = new symbol_t "bitwise_complement"
let op_bitwise_or  = new symbol_t "bitwise_or"
let op_bitwise_and = new symbol_t "bitwise_and"
let op_bitwise_xor = new symbol_t "bitwise_xor"
let op_bitwise_sll = new symbol_t "bitwise_sll"
let op_bitwise_srl = new symbol_t "bitwise_srl"
let op_bitwise_sra = new symbol_t "bitwise_sra"


let make_code_label ?src ?modifier (address:ctxt_iaddress_t) =
  let name = "pc_" ^ address in
  let atts = match modifier with
    | Some s -> [s] | _ -> [] in
  let atts = match src with
    | Some s -> s#to_fixed_length_hex_string :: atts | _ -> atts in
  ctxt_string_to_symbol name ~atts address


let get_invariant_label ?(bwd=false) (loc:location_int) =
  if bwd then
    ctxt_string_to_symbol "bwd-invariant" loc#ci
  else
    ctxt_string_to_symbol "invariant" loc#ci


let package_transaction
      (finfo:function_info_int) (label:symbol_t) (cmds:cmd_t list) =
  let cmds =
    List.filter
      (fun cmd -> match cmd with SKIP -> false | _ -> true) cmds in
  let cnstAssigns = finfo#env#end_transaction in
  TRANSACTION (label, LF.mkCode (cnstAssigns @ cmds), None)


let make_tests
      ~(testloc:location_int)
      ~(jumploc:location_int)
      ~(testexpr:xpr_t)
      ~(restriction:block_restriction_t option) =
  let testfloc = get_floc testloc in
  let jumpfloc = get_floc jumploc in
  let env = testfloc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let frozenvars = new VariableCollections.table_t in
  let rtestexpr = testexpr (* rewrite_expr testfloc testexpr *) in
  let vars = variables_in_expr rtestexpr in
  let _ =
    List.iter (fun v ->
        if env#is_local_variable v then
          let fv = env#mk_frozen_test_value v testloc#ci jumploc#ci in
          frozenvars#set v fv
        else
          ()) vars in
  let _ = testfloc#set_test_variables frozenvars#listOfPairs in
  let subst v =
    if frozenvars#has v then XVar (Option.get (frozenvars#get v)) else XVar v in
  let ftestexpr = substitute_expr subst rtestexpr in
  let convert_to_chif expr =
    let (cmds,bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ [ ASSERT bxpr ] in
  let convert_to_assert (expr:xpr_t) =
    let vars = variables_in_expr expr in
    let varssize = List.length vars in
    let get_external_exprs v =
      if jumpfloc#env#is_symbolic_value v then
        [ jumpfloc#env#get_symbolic_value_expr v ]
      else
        jumpfloc#inv#get_external_exprs v in
    let xprs =
      if varssize = 1 then
        let var = List.hd vars in
        let extExprs = get_external_exprs var in
        let extExprs =
          List.map (fun e -> substitute_expr (fun v -> e) expr) extExprs in
        expr :: extExprs
      else if varssize = 2 then
        let varlist = vars in
        let var1 = List.nth varlist 0 in
        let var2 = List.nth varlist 1 in
        let externalexprs1 = get_external_exprs var1 in
        let externalexprs2 = get_external_exprs var2 in
        let xprs =
          List.concat
            (List.map
               (fun e1 ->
                 List.map
                   (fun e2 ->
                     substitute_expr (fun w -> if w#equal var1 then e1 else e2) expr)
                   externalexprs2)
               externalexprs1) in
        expr :: xprs
      else
        [ expr ] in
    List.concat (List.map convert_to_chif xprs) in
  let make_asserts (exprs:xpr_t list) =
    let _ = env#start_transaction in
    let cmds = List.concat (List.map convert_to_assert exprs) in
    let constassigns = env#end_transaction in
    constassigns  @ cmds in
  let make_branch_assert (exprs:xpr_t list) =
    let _ = env#start_transaction in
    let cmds = List.map convert_to_assert exprs in
    let br = BRANCH (List.map LF.mkCode cmds) in
    let constassigns = env#end_transaction in
    constassigns @ [ br ] in
  let make_assert (expr:xpr_t) =
    let _ = env#start_transaction in
    let cmds = convert_to_assert expr in
    let constassigns = env#end_transaction in
    constassigns @ cmds in
  let make_test_code (expr:xpr_t) =
    if is_conjunction expr then
      let conjuncts = get_conjuncts expr in
      make_asserts conjuncts
    else if is_disjunction expr then
      let disjuncts = get_disjuncts expr in
      make_branch_assert disjuncts
    else
      make_assert expr in
  let thenexpr =
    match restriction with
    | Some (BranchAssert false) ->   (* assert false branch *)
       let _ =
         chlog#add
           "restriction"
           (LBLOCK [ x2p ftestexpr ; STR " -> false" ]) in
       false_constant_expr
    | _ -> ftestexpr in
  let elseexpr =
    match restriction with
    | Some (BranchAssert true) ->   (* assert true branch *)
       let _ =
         chlog#add
           "restriction"
           (LBLOCK [ x2p (simplify_xpr (XOp (XLNot, [ ftestexpr ]))) ;
                     STR " -> false " ]) in
       false_constant_expr
    | _ -> simplify_xpr (XOp (XLNot, [ ftestexpr ])) in
  let thencode = make_test_code thenexpr in
  let elsecode = make_test_code elseexpr in
  (frozenvars#listOfValues, thencode, elsecode)


let make_condition
      ~(testloc:location_int)
      ~(jumploc:location_int)
      ~(theniaddr:ctxt_iaddress_t)
      ~(elseiaddr:ctxt_iaddress_t)
      ~(blocklabel:symbol_t)
      ~(testexpr:xpr_t)
      ~(restriction:block_restriction_t option) =
  let thensucclabel = make_code_label theniaddr in
  let elsesucclabel = make_code_label elseiaddr in
  let (frozenvars,thentest,elsetest) = make_tests ~testloc ~jumploc ~testexpr ~restriction in
  let make_node_and_label testcode tgtaddr modifier =
    let src = jumploc#i in
    let nextlabel = make_code_label ~src ~modifier tgtaddr in
    let testcode = testcode @ [ ABSTRACT_VARS frozenvars ] in
    let transaction = TRANSACTION (nextlabel, LF.mkCode testcode, None) in
    (nextlabel, [ transaction ]) in
  let (thentestlabel, thennode) =
    make_node_and_label thentest theniaddr "then" in
  let (elsetestlabel, elsenode) =
    make_node_and_label elsetest  elseiaddr "else" in
  let thenedges =
    [(blocklabel, thentestlabel); (thentestlabel, thensucclabel)] in
  let elseedges =
    [(blocklabel, elsetestlabel); (elsetestlabel, elsesucclabel)] in
  ([(thentestlabel, thennode); (elsetestlabel, elsenode)], thenedges @ elseedges)


let translate_mips_instruction
      ~(funloc:location_int)
      ~(codepc:mips_code_pc_int)
      ~(blocklabel:symbol_t)
      ~(exitlabel:symbol_t)
      ~(cmds:cmd_t list) =                         (* commands carried over *)
  let (ctxtiaddr,instr) = codepc#get_next_instruction in
  let faddr = funloc#f in
  let loc = ctxt_string_to_location faddr ctxtiaddr in    (* instr location *)
  let finfo = get_function_info faddr in
  let env = finfo#env in
  let invlabel = get_invariant_label loc in
  let invop = OPERATION {op_name = invlabel; op_args = []} in
  let bwdinvlabel = get_invariant_label ~bwd:true loc in
  let bwdinvop = OPERATION {op_name = bwdinvlabel; op_args = []} in
  let frozenasserts =
    List.map (fun (v, fv) -> ASSERT (EQ (v, fv)))
      (finfo#get_test_variables ctxtiaddr) in
  let rewrite_expr floc x:xpr_t =
    let xpr = floc#inv#rewrite_expr x env#get_variable_comparator in
    let rec expand x =
      match x with
      | XVar v when env#is_symbolic_value v ->
         expand (env#get_symbolic_value_expr v)
      | XOp (op, l) -> XOp (op, List.map expand l)
      | _ -> x in
    simplify_xpr (expand xpr) in
  let floc = get_floc loc in
  let default newcmds =
    ([],[], cmds @ frozenasserts @ (invop :: newcmds) @ [bwdinvop]) in

  let get_register_vars (ops: mips_operand_int list) =
    List.fold_left (fun acc op ->
        if op#is_register || op#is_special_register then
          if not op#is_register_zero then
            (op#to_variable floc) :: acc
          else
            acc
        else
          acc) [] ops in

  let get_use_high_vars (xprs: xpr_t list): variable_t list =
    let inv = floc#inv in
    let comparator = env#get_variable_comparator in
    List.fold_left (fun acc x ->
        let xw = inv#rewrite_expr x comparator in
        let xs = simplify_xpr xw in
        let vars = env#variables_in_expr xs in
        vars @ acc) [] xprs in

  match instr#get_opcode with
  | Add (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XPlus, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  (* Format: ADDI rt, rs, immediate
     Description: GPR[rt] <- GPR[rs] + immediate
     The 16-bit signed immediate is added to the 32-bit value in GPR rs
     to produce a 32-bit result.
     If the addition results in 32-bit 2's complement arithmetic overflow,
     the destination register is not modified and an Integer Overflow
     exception occurs. If the addition does not overflow, the 32-bit result
     is placed into GRP rt.
   *)
  | AddImmediate (rt, rs, imm) ->
     let rtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let ximm = imm#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let result = XOp (XPlus, [xrs; ximm]) in
     let (vrt, cmds) =
       floc#get_ssa_assign_commands rtreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  (* Format: ADDIU rt, rs, immediate
     Description: GPR[rt] <- GPR[rs] + immediate
     The 16-bit signed immediate is added to the 32-bit value in GPR
     rs and the 32-bit arithmetic result is placed into GPT rt.

     Note: The term 'unsigned' in the instruction name is a misnomer;
     this operation is 32-bit modulo arithmetic that does not trap on
     overflow. This instruction is appropriate for unsigned arithmetic,
     such as address arithmetic, or integer arithmetic environments that
     ignore overflow, such as C language arithmetic.
   *)
  | AddImmediateUnsigned (rt, rs, imm) ->
     let rtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let ximm = imm#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let result = XOp (XPlus, [xrs; ximm]) in
     let (vrt, cmds) =
       floc#get_ssa_assign_commands rtreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | AddUpperImmediate (rt, rs, imm) ->
     let rtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let ximm =
       num_constant_expr (imm#to_numerical#mult (mkNumerical (256 * 256))) in
     let usehigh = get_use_high_vars [xrs] in
     let result = XOp (XPlus, [xrs; ximm]) in
     let (vrt, cmds) =
       floc#get_ssa_assign_commands rtreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | AddUnsigned (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XPlus, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | And (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XBAnd, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | AndImmediate (rt, rs, imm) ->
     let rtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let ximm = imm#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let result = XOp (XBAnd, [xrs; ximm]) in
     let (vrt, cmds) =
       floc#get_ssa_assign_commands rtreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | BranchEqual (rs, rt, _) ->
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchEqualLikely (rs, rt, _) ->
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchFPFalse _ -> default []

  | BranchFPFalseLikely _ -> default []

  | BranchFPTrue _ -> default []

  | BranchFPTrueLikely _ -> default []

  | BranchGEZero (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchGEZeroLikely (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchGEZeroLink (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchGTZero (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchGTZeroLikely (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchLEZero (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchLEZeroLikely (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchLink _ ->
     default (get_floc loc)#get_mips_call_commands

  | BranchLTZero (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchLTZeroLikely (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchLTZeroLink (rs, _) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchNotEqual (rs, rt, _) ->
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | BranchNotEqualLikely (rs, rt, _) ->
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | ControlWordFromFP (rt, fs) ->
     let rtreg = rt#to_register in
     let (vrt, cmds) = floc#get_ssa_abstract_commands rtreg ~vtype:t_uint () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = defcmds @ cmds in
     default cmds

  | ControlWordToFP (rt, fs) ->
     let xrt = rt#to_expr floc in
     let use = get_register_vars [rt] in
     let usehigh = get_use_high_vars [xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | CountLeadingZeros (rd, rs) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let (vrd, cmds) = floc#get_ssa_abstract_commands rdreg ~vtype:t_uint () in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     default cmds

  | DivideWord (hi, lo, rs, rt) ->
     let hireg = hi#to_register in
     let loreg = lo#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XDiv, [xrs; xrt]) in
     let (vhi, cmdshi) = floc#get_ssa_abstract_commands hireg () in
     let (vlo, cmdslo) =
       floc#get_ssa_assign_commands loreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vhi; vlo] ~use ~usehigh ctxtiaddr in
     let cmds = cmdshi @ cmdslo @ defcmds in
     default cmds

  | DivideUnsignedWord (hi, lo, rs, rt) ->
     let hireg = hi#to_register in
     let loreg = lo#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XDiv, [xrs; xrt]) in
     let (vhi, cmdshi) = floc#get_ssa_abstract_commands hireg () in
     let (vlo, cmdslo) =
       floc#get_ssa_assign_commands loreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vhi; vlo] ~use ~usehigh ctxtiaddr in
     let cmds = cmdshi @ cmdslo @ defcmds in
     default cmds

  | ExtractBitField (rt, rs, pos, size) ->
     let vtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let (vrt, cmds) = floc#get_ssa_abstract_commands vtreg ~vtype:t_uint () in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | FPAbsfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPAddfmt (fmt, fd, fs, ft) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPCeilLfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPCeilWfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPCVTDfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPCVTLfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPCVTSfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPCVTSPfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPCVTWfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPDivfmt (fmd, fd, fs, ft) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPFloorLfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPFloorWfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPMovfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let rhs = fs#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | FPMulfmt (fmt, fd, fs, ft) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPNegfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPRSqrtfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPSqrtfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPSubfmt (fmt, fd, fs, ft) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPRoundLfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPRoundWfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPTruncLfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPTruncWfmt (fmt, fd, fs) ->
     let floc = get_floc loc in
     let (lhs, lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | InsertBitField (rt, rs, pos, size) ->
     let vtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let (vrt, cmds) = floc#get_ssa_abstract_commands vtreg ~vtype:t_uint () in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | Jump _ -> default []

  | JumpLink _ ->
     default (get_floc loc)#get_mips_call_commands

  | JumpLinkRegister _ ->
     default (get_floc loc)#get_mips_call_commands

  | JumpRegister _ when (get_floc loc)#has_call_target ->
     default (get_floc loc)#get_mips_call_commands

  | JumpRegister _ -> default []

  | LoadByte (rt, addr) ->
     let rtreg = rt#to_register in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [rt; base] in
     let rhs = XOp (XXlsb, [addr#to_expr floc]) in
     let (vrt, cmds) = floc#get_ssa_assign_commands rtreg ~vtype:t_char rhs in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadByteUnsigned (rt, addr) ->
     let rtreg = rt#to_register in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let rhs = XOp (XXlsb, [addr#to_expr floc]) in
     let (vrt, cmds) = floc#get_ssa_assign_commands rtreg ~vtype:t_uchar rhs in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadDoublewordToFP (ft, addr) ->
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let rhs = addr#to_expr floc in
     let usehigh = get_use_high_vars [rhs] in
     let (lhs, lhscmds) = ft#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     let cmds = lhscmds @ cmds @ defcmds in
     default cmds

  | LoadHalfWord (rt, addr) ->
     let rtreg = rt#to_register in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let rhs = XOp (XXlsh, [addr#to_expr floc]) in
     let (vrt, cmds) = floc#get_ssa_assign_commands rtreg ~vtype:t_short rhs in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadHalfWordUnsigned (rt, addr) ->
     let rtreg = rt#to_register in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let rhs = XOp (XXlsh, [addr#to_expr floc]) in
     let (vrt, cmds) = floc#get_ssa_assign_commands rtreg ~vtype:t_ushort rhs in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadImmediate (rt, imm) ->
     let rtreg = rt#to_register in
     let rhs = imm#to_expr floc in
     let (vrt, cmds) = floc#get_ssa_assign_commands rtreg ~vtype:t_int rhs in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadLinkedWord (rt, addr) ->
     let rtreg = rt#to_register in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let rhs = XOp (XXlsh, [addr#to_expr floc]) in
     let (vrt, cmds) = floc#get_ssa_assign_commands rtreg ~vtype:t_int rhs in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadUpperImmediate (rt, imm) ->
     let rtreg = rt#to_register in
     let rhs =
       num_constant_expr (imm#to_numerical#mult (mkNumerical (256 * 256))) in
     let (vrt, cmds) = floc#get_ssa_assign_commands rtreg ~vtype:t_int rhs in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadWord (rt, addr) ->
     let rtreg = rt#to_register in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let rhs = addr#to_expr floc in
     let rhs = floc#inv#rewrite_expr rhs floc#env#get_variable_comparator in
     let (vrt, cmds) = floc#get_ssa_assign_commands rtreg ~vtype:t_int rhs in
     let _ =
       match rhs with
       | XVar rhsvar ->
          if env#is_initial_register_value rhsvar then
            match env#get_initial_register_value_register rhsvar with
            | MIPSRegister r when r = rt#get_register ->
               let memaddr = addr#to_address floc in
               let memaddr =
                 floc#inv#rewrite_expr
                   memaddr floc#env#get_variable_comparator in
               finfo#restore_register
                 memaddr floc#cia (MIPSRegister rt#get_register)
            | _ -> ()
          else
            ()
       | _ -> () in
     let usehigh = get_use_high_vars [rhs] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadWordFP (ft, addr) ->
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let rhs = addr#to_expr floc in
     let usehigh = get_use_high_vars [rhs] in
     let (lhs, lhscmds) = ft#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     let cmds = lhscmds @ cmds @ defcmds in
     default cmds

  | LoadWordLeft (rt, addr) ->
     let rtreg = rt#to_register in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let (vrt, cmds) = floc#get_ssa_abstract_commands rtreg ~vtype:t_int () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ~use ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | LoadWordRight (rt, addr) ->
     let rtreg = rt#to_register in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let (vrt, cmds) = floc#get_ssa_abstract_commands rtreg ~vtype:t_int () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ~use ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveConditionalNotZero (rd, rs, rt) ->
     let vrt = rd#to_variable floc in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let testxpr = XOp (XNe, [xrt; zero_constant_expr]) in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let cmds = floc#get_conditional_assign_commands xrt vrt testxpr in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveConditionalZero (rd, rs, rt) ->
     let vrt = rd#to_variable floc in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let testxpr = XOp (XEq, [xrt; zero_constant_expr]) in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let cmds = floc#get_conditional_assign_commands xrt vrt testxpr in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MovF (cc, rd, rs) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let (vrd, cmds) = floc#get_ssa_abstract_commands rdreg () in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MovT (cc, rd, rs) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let (vrd, cmds) = floc#get_ssa_abstract_commands rdreg () in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | Move (rd, rs) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let (vrd, cmds) = floc#get_ssa_assign_commands rdreg xrs in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveFromHi (rd, hi) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [hi] in
     let xhi = hi#to_expr floc in
     let usehigh = get_use_high_vars [xhi] in
     let (vrd, cmds) = floc#get_ssa_assign_commands rdreg xhi in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveToHi (hi, rs) ->
     let hireg = hi#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let (vhi, cmds) = floc#get_ssa_assign_commands hireg xrs in
     let defcmds =
       floc#get_vardef_commands ~defs:[vhi] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveFromLo (rd, lo) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [lo] in
     let xlo = lo#to_expr floc in
     let usehigh = get_use_high_vars [xlo] in
     let (vrd, cmds) = floc#get_ssa_assign_commands rdreg xlo in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveToLo (lo, rs) ->
     let loreg = lo#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let (vlo, cmds) = floc#get_ssa_assign_commands loreg xrs in
     let defcmds =
       floc#get_vardef_commands ~defs:[vlo] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveWordFromFP (rt, fs) ->
     let vtreg = rt#to_register in
     let (vrt, cmds) = floc#get_ssa_abstract_commands vtreg () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveWordFromHighHalfFP (rt, fs) ->
     let vtreg = rt#to_register in
     let (vrt, cmds) = floc#get_ssa_abstract_commands vtreg () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveWordToHighHalfFP (rt, fs) ->
     let (lhs, lhscmds) = fs#to_lhs floc in
     let use = get_register_vars [rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let cmds = floc#get_abstract_commands lhs () in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveWordToFP (rt, fs) ->
     let (lhs, lhscmds) = fs#to_lhs floc in
     let use = get_register_vars [rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let cmds = floc#get_abstract_commands lhs () in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveFromCoprocessor0 (rt, _, _) ->
     let rtreg = rt#to_register in
     let (vrt, cmds) = floc#get_ssa_abstract_commands rtreg () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveToCoprocessor0 (rt, _, _) ->
     let use = get_register_vars [rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | MoveFromHighCoprocessor0 (rt, _, _) ->
     let rtreg = rt#to_register in
     let (vrt, cmds) = floc#get_ssa_abstract_commands rtreg () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveToHighCoprocessor0 (rt, _, _) ->
     let use = get_register_vars [rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | MoveWordFromCoprocessor2 (rt, _, _) ->
     let rtreg = rt#to_register in
     let (vrt, cmds) = floc#get_ssa_abstract_commands rtreg () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveWordFromHighHalfCoprocessor2 (rt, _, _) ->
     let rtreg = rt#to_register in
     let (vrt, cmds) = floc#get_ssa_abstract_commands rtreg () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | MoveWordToCoprocessor2 (rt, _, _) ->
     let use = get_register_vars [rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | MultiplyAddWord (hi, lo, rs, rt) ->
     let hireg = hi#to_register in
     let loreg = lo#to_register in
     let use = get_register_vars [hi; lo; rs; rt] in
     let xhi = hi#to_expr floc in
     let xlo = lo#to_expr floc in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let result = XOp (XPlus, [xlo; XOp (XMult, [xrs; xrt])]) in
     let usehigh = get_use_high_vars [xhi; xlo; xrs; xrt] in
     let (vhi, hicmds) = floc#get_ssa_abstract_commands hireg () in
     let (vlo, locmds) =
       floc#get_ssa_assign_commands loreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vlo; vhi] ~use ~usehigh ctxtiaddr in
     let cmds = hicmds @ locmds @ defcmds in
     default cmds

  | MultiplyAddUnsignedWord (hi, lo, rs, rt) ->
     let hireg = hi#to_register in
     let loreg = lo#to_register in
     let use = get_register_vars [hi; lo; rs; rt] in
     let xhi = hi#to_expr floc in
     let xlo = lo#to_expr floc in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let result = XOp (XPlus, [xlo; XOp (XMult, [xrs; xrt])]) in
     let usehigh = get_use_high_vars [xhi; xlo; xrs; xrt] in
     let (vhi, hicmds) = floc#get_ssa_abstract_commands hireg () in
     let (vlo, locmds) =
       floc#get_ssa_assign_commands loreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vlo; vhi] ~use ~usehigh ctxtiaddr in
     let cmds = hicmds @ locmds @ defcmds in
     default cmds

  | MultiplyUnsignedWord (hi, lo, rs, rt) ->
     let hireg = hi#to_register in
     let loreg = lo#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let result = XOp (XMult, [xrs; xrt]) in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let (vhi, hicmds) = floc#get_ssa_abstract_commands hireg () in
     let (vlo, locmds) =
       floc#get_ssa_assign_commands loreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vlo; vhi] ~use ~usehigh ctxtiaddr in
     let cmds = hicmds @ locmds @ defcmds in
     default cmds

  | MultiplyWord (hi, lo, rs, rt) ->
     let hireg = hi#to_register in
     let loreg = lo#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let result = XOp (XMult, [xrs; xrt]) in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let (vhi, hicmds) = floc#get_ssa_abstract_commands hireg () in
     let (vlo, locmds) =
       floc#get_ssa_assign_commands loreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vlo; vhi] ~use ~usehigh ctxtiaddr in
     let cmds = hicmds @ locmds @ defcmds in
     default cmds

  | MultiplyWordToGPR (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XMult, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | Nor (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XBNor, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | Or (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XBOr, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | OrImmediate (rt, rs, imm) ->
     let rtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let ximm = imm#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let result = XOp (XBOr, [xrs; ximm]) in
     let (vrt, cmds) =
       floc#get_ssa_assign_commands rtreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | Prefetch (addr, _) ->
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let defcmds = floc#get_vardef_commands ~use ctxtiaddr in
     default defcmds

  | ReadHardwareRegister (rt, rd) ->
     let rtreg = rt#to_register in
     let (vrt, cmds) = floc#get_ssa_abstract_commands rtreg () in
     let defcmds = floc#get_vardef_commands ~defs:[vrt] ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | SetLT (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XLt, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_bool result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | SetLTImmediate (rt, rs, imm) ->
     let rtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let ximm = imm#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let result = XOp (XLt, [xrs; ximm]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rtreg ~vtype:t_bool result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | SetLTImmediateUnsigned (rt, rs, imm) ->
     let rtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let ximm = imm#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let result = XOp (XLt, [xrs; ximm]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rtreg ~vtype:t_bool result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | SetLTUnsigned (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XLt, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_bool result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | ShiftLeftLogical (rd, rt, sa) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rt; sa] in
     let xrt = rt#to_expr floc in
     let xsa = sa#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let result =
       match xsa with
       | XConst (IntConst n) ->
          let m = get_multiplier n in
          XOp (XMult, [xrt; m])
       | _ ->
          raise
            (BCH_failure
               (LBLOCK [
                    STR "Unexpected operand in ShiftLeftLogical (SLL): ";
                    sa#toPretty])) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | ShiftLeftLogicalVariable (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result =
       (match xrs with
        | XConst (IntConst n) when n#equal numerical_one ->
           XOp (XPow, [int_constant_expr 2; xrt])
        | _ -> XOp (XLsl, [xrs; xrt])) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | ShiftRightArithmetic (rd, rt, sa) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rt; sa] in
     let xrt = rt#to_expr floc in
     let xsa = sa#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let result = XOp (XAsr, [xrt; xsa]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | ShiftRightArithmeticVariable (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XAsr, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | ShiftRightLogical (rd, rt, sa) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rt; sa] in
     let xrt = rt#to_expr floc in
     let xsa = sa#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let result =
       match xsa with
       | XConst (IntConst n) when n#toInt = 31 ->
          (match rewrite_expr floc xrt with
           | XOp (XBNor, [x1; x2]) when is_zero x1 ->
              (XOp (XGe, [x2; x1]))
           | XOp (XBNor, [x1; x2]) when is_zero x2 ->
              (XOp (XGe, [x1; x2]))
           | _ -> XOp (XGe, [xrt; zero_constant_expr]))
       | _ ->
          XOp (XLsr, [xrt; xsa]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | ShiftRightLogicalVariable (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XLsr, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | SignExtendByte (rd, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let result = XOp (XXlsb, [xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_char result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | SignExtendHalfword (rd, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let result = XOp (XXlsh, [xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_short result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | StoreByte (addr, rt) ->
     let (vmem, memcmds) = addr#to_lhs floc in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base; rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let cmds = floc#get_assign_commands vmem xrt in
     let defcmds =
       floc#get_vardef_commands ~defs:[vmem] ~use ~usehigh ctxtiaddr in
     let cmds = memcmds @ cmds @ defcmds in
     default cmds

  (* Assume that the write succeeds, that is, no concurrent conflicting
     accesses *)
  | StoreConditionalWord (addr, rt) ->
     let (vmem, memcmds) = addr#to_lhs floc in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base; rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let cmds = floc#get_assign_commands vmem xrt in
     let defcmds =
       floc#get_vardef_commands ~defs:[vmem] ~use ~usehigh ctxtiaddr in
     let cmds = memcmds @ cmds @ defcmds in
     default cmds

  | StoreDoublewordFromFP (addr, ft) ->
     let (vmem, memcmds) = addr#to_lhs floc in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let xft = ft#to_expr floc in
     let usehigh = get_use_high_vars [xft] in
     let eight = int_constant_expr 8 in
     let cmds =
       floc#get_assign_commands vmem ~size:eight ~vtype:t_double xft in
     let defcmds =
       floc#get_vardef_commands ~defs:[vmem] ~use ~usehigh ctxtiaddr in
     let cmds = memcmds @ cmds @ defcmds in
     default cmds

  | StoreHalfWord (addr, rt) ->
     let (vmem, memcmds) = addr#to_lhs floc in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base; rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let cmds = floc#get_assign_commands vmem xrt in
     let defcmds =
       floc#get_vardef_commands ~defs:[vmem] ~use ~usehigh ctxtiaddr in
     let cmds = memcmds @ cmds @ defcmds in
     default cmds

  | StoreWord (addr, rt) ->
     let (vmem, memcmds) = addr#to_lhs floc in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base; rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let cmds = floc#get_assign_commands vmem xrt in
     let defcmds =
       floc#get_vardef_commands ~defs:[vmem] ~use ~usehigh ctxtiaddr in
     let cmds = memcmds @ cmds @ defcmds in
     let _ =
       if not rt#is_register_zero then
         let var = env#mk_mips_register_variable rt#get_register in
         if floc#has_initial_value var then
           finfo#save_register vmem floc#cia (MIPSRegister rt#get_register) in
     default cmds

  | StoreWordFromFP (addr, ft) ->
     let (vmem, memcmds) = addr#to_lhs floc in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base] in
     let xft = ft#to_expr floc in
     let usehigh = get_use_high_vars [xft] in
     let four = int_constant_expr 4 in
     let cmds =
       floc#get_assign_commands vmem ~size:four ~vtype:t_float xft in
     let defcmds =
       floc#get_vardef_commands ~defs:[vmem] ~use ~usehigh ctxtiaddr in
     let cmds = memcmds @ cmds @ defcmds in
     default cmds

  (* TODO: StoreWordLeft and StoreWordRight semantics should be combined
     into a single store, as per MIPS architecture documentation *)
  | StoreWordLeft (addr, rt) ->
     let (vmem, memcmds) = addr#to_lhs floc in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base; rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let cmds = floc#get_assign_commands vmem xrt in
     let defcmds =
       floc#get_vardef_commands ~defs:[vmem] ~use ~usehigh ctxtiaddr in
     let cmds = memcmds @ cmds @ defcmds in
     default cmds

  | StoreWordRight (addr, rt) ->
     let (vmem, memcmds) = addr#to_lhs floc in
     let base = mips_register_op addr#get_indirect_register RD in
     let use = get_register_vars [base; rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let cmds = floc#get_assign_commands vmem xrt in
     let defcmds =
       floc#get_vardef_commands ~defs:[vmem] ~use ~usehigh ctxtiaddr in
     let cmds = memcmds @ cmds @ defcmds in
     default cmds

  | Subtract (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XMinus, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_int result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | SubtractUnsigned (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XMinus, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | Syscall _ ->
     let floc = get_floc loc in
     if floc#has_call_target then
       default (get_floc loc)#get_mips_syscall_commands
     else
       default []

  (* TODO: add an ASSERT on the condition *)
  | TrapIfEqualImmediate (rs, imm) ->
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  (* TODO: add an ASSERT on the condition *)
  | TrapIfEqual (_, rs, rt) ->
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let defcmds = floc#get_vardef_commands ~use ~usehigh ctxtiaddr in
     default defcmds

  | Xor (rd, rs, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rs; rt] in
     let xrs = rs#to_expr floc in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrs; xrt] in
     let result = XOp (XBXor, [xrs; xrt]) in
     let (vrd, cmds) =
       floc#get_ssa_assign_commands rdreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | XorImmediate (rt, rs, imm) ->
     let rtreg = rt#to_register in
     let use = get_register_vars [rs] in
     let xrs = rs#to_expr floc in
     let ximm = imm#to_expr floc in
     let usehigh = get_use_high_vars [xrs] in
     let result =
       match ximm with
       | XConst (IntConst n) when n#equal numerical_one ->
          (match rewrite_expr floc xrs with
           | XOp (XLt, [x1; x2]) ->
              XOp (XGe, [x1; x2])
           | _ ->
              XOp (XBXor, [xrs; ximm]))
       | _ -> XOp (XBXor, [xrs; ximm]) in
     let (vrt, cmds) =
       floc#get_ssa_assign_commands rtreg ~vtype:t_uint result in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | WordSwapBytesHalfwords (rd, rt) ->
     let rdreg = rd#to_register in
     let use = get_register_vars [rt] in
     let xrt = rt#to_expr floc in
     let usehigh = get_use_high_vars [xrt] in
     let (vrd, cmds) = floc#get_ssa_abstract_commands rdreg ~vtype:t_uint () in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     default cmds

  | NoOperation -> default []

  | Halt -> default []

  | Sync _ -> default []

  | opc ->
     let _ =
       chlog#add
         "opcode not translated"
         (LBLOCK [faddr#toPretty; STR ": "; STR (mips_opcode_to_string opc)]) in
     default []


class mips_assembly_function_translator_t (f:mips_assembly_function_int) =
object (self)

  val finfo = get_function_info f#get_address
  val funloc =
    make_location {loc_faddr = f#get_address; loc_iaddr = f#get_address}
  val codegraph = make_code_graph ()
  val specialization =
    let faddr = f#get_address#to_hex_string in
    if specializations#has_specialization faddr then
      Some (specializations#get_specialization faddr)
    else
      None

  method translate_block (block:mips_assembly_block_int) exitlabel =
    let codepc = make_mips_code_pc block in
    let blocklabel = make_code_label block#get_context_string in
    let restriction =
      let faddr = f#get_address#to_hex_string in
      let baddr = block#get_context_string in
      match specialization with
      | Some s ->
         if s#has_block_restriction faddr baddr then
           Some (s#get_block_restriction faddr baddr)
         else
           None
      | _ -> None in
    let rec aux cmds =
      let (nodes, edges, newcmds) =
        try
          translate_mips_instruction ~funloc ~codepc ~blocklabel ~exitlabel ~cmds
        with
        | BCH_failure p ->
           let msg = LBLOCK [funloc#toPretty; STR ", "; blocklabel#toPretty; p] in
           begin
             ch_error_log#add "translate mips block" msg;
             raise (BCH_failure msg)
           end in
      match nodes with
      | [] ->
         if codepc#has_more_instructions then
           aux newcmds
         else if codepc#has_conditional_successor then
           let (testloc, jumploc, theniaddr, elseiaddr, testexpr) =
             codepc#get_conditional_successor_info in
           let transaction = package_transaction finfo blocklabel newcmds in
           let (nodes,edges) =
             make_condition
               ~testloc
               ~jumploc
               ~theniaddr
               ~elseiaddr
               ~blocklabel
               ~testexpr
               ~restriction in
           ((blocklabel, [transaction ]) :: nodes, edges)
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
             | [] -> (blocklabel, exitlabel) :: edges
             | _ -> edges in
           (nodes,edges)
      | _ -> (nodes,edges) in
    let _ = finfo#env#start_transaction in
    let (nodes,edges) = aux [] in
    begin
      List.iter (fun (label,node) -> codegraph#add_node label node) nodes;
      List.iter (fun (src,tgt) -> codegraph#add_edge src tgt) edges
    end

  method private get_entry_cmd =
    let env = finfo#env in
    let  _ = env#start_transaction in
    let freeze_initial_register_value (reg:mips_reg_t) =
      let regVar = env#mk_mips_register_variable reg in
      let initVar = env#mk_initial_register_value (MIPSRegister reg) in
      let _ =
        ignore (env#mk_symbolic_variable ~domains:["reachingdefs"] initVar) in
      ASSERT (EQ (regVar, initVar)) in
    let freeze_initial_special_register_value (reg: mips_special_reg_t) =
      let regVar = env#mk_mips_special_register_variable reg in
      let initVar = env#mk_initial_register_value (MIPSSpecialRegister reg) in
      let _ =
        ignore (env#mk_symbolic_variable ~domains:["reachingdefs"] initVar) in
      ASSERT (EQ (regVar, initVar)) in
    let freeze_external_memory_values (v:variable_t) =
      let initVar = env#mk_initial_memory_value v in
      let _ =
        ignore (env#mk_symbolic_variable ~domains:["reachingdefs"] initVar) in
      ASSERT (EQ (v, initVar)) in
    let t9Assign =
      let t9Var = env#mk_mips_register_variable MRt9 in
      let reqN () = env#mk_num_temp in
      let reqC = env#request_num_constant in
      let (rhsCmds,rhs) =
        xpr_to_numexpr reqN reqC (num_constant_expr f#get_address#to_numerical) in
      rhsCmds @ [ASSIGN_NUM (t9Var, rhs)] in
    let rAsserts =
      List.map freeze_initial_register_value mips_regular_registers in
    let xAsserts =
      List.map freeze_initial_special_register_value [MMHi; MMLo] in
    let externalMemVars = env#get_external_memory_variables in
    let externalMemVars = List.filter env#has_constant_offset externalMemVars in
    let mAsserts = List.map freeze_external_memory_values externalMemVars in
    let sp0 = env#mk_initial_register_value (MIPSRegister MRsp) in
    let _ = finfo#add_base_pointer sp0 in
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
      (env#get_domain_sym_variables "reachingdefs") in
    let constantAssigns = env#end_transaction in
    let cmds =
      constantAssigns
      @ t9Assign
      @ rAsserts
      @ xAsserts
      @ mAsserts
      @ [initializeScalar]
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
      let symvars = env#get_domain_sym_variables "defusehigh" in
      let symvars =
        List.filter (fun v ->
            if v#getName#getSeqNumber >= 0 then
              let numvar = env#get_symbolic_num_variable v in
              not (env#is_register_variable numvar
                   || env#is_local_variable numvar)
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
    let entrylabel = make_code_label ~modifier:"entry" funloc#ci in
    let exitlabel = make_code_label ~modifier:"exit" funloc#ci in
    let firstInstrLabel = make_code_label funloc#ci in
    let procname = make_mips_proc_name faddr in
    let _ = f#iter (fun b -> self#translate_block b exitlabel) in
    let entrycmd = self#get_entry_cmd in
    let exitcmd = self#get_exit_cmd in
    let scope = finfo#env#get_scope in
    let _ = codegraph#add_node entrylabel [entrycmd] in
    let _ = codegraph#add_node exitlabel [exitcmd] in
    let _ = codegraph#add_edge entrylabel firstInstrLabel in
    let cfg = codegraph#to_cfg entrylabel exitlabel in
    let body = LF.mkCode [CFG (procname,cfg)] in
    let proc = LF.mkProcedure procname ~signature:[] ~bindings:[] ~scope ~body in
    (* let _ = pverbose [proc#toPretty; NL] in *)
    mips_chif_system#add_mips_procedure proc

end

let translate_mips_assembly_function (f:mips_assembly_function_int) =
  let translator = new mips_assembly_function_translator_t f in
  try
    translator#translate
  with
  | CHFailure p
    | BCH_failure p ->
     let msg = LBLOCK [ STR "Failure in translation: " ; p ] in
     raise (BCH_failure msg)

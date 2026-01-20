(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2025  Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHTraceResult

(* xprlib *)
open Xprt
open XprTypes
open XprToPretty
open XprUtil
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHBCTypeUtil
open BCHCodegraph
open BCHCPURegisters
open BCHDoubleword
open BCHFloc
open BCHFtsParameter
open BCHFunctionInfo
open BCHFunctionInterface
open BCHLibTypes
open BCHLocation
open BCHSystemInfo

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMCHIFSystem
open BCHARMCodePC
open BCHARMConditionalExpr
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMTestSupport
open BCHARMTypes


module LF = CHOnlineCodeSet.LanguageFactory
module TR = CHTraceResult

let x2p = xpr_formatter#pr_expr
let p2s = CHPrettyUtil.pretty_to_string
let x2s x = p2s (x2p x)
let x_r2s x_r = TR.tfold_default x2s "error-value" x_r

let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("TranslateARMToCHIF:" ^ tag) msg

let valueset_domain = "valuesets"


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
    ctxt_string_to_symbol "bwd_invariant" loc#ci
  else
    ctxt_string_to_symbol "invariant" loc#ci


let package_transaction
      (finfo:function_info_int) (label:symbol_t) (cmds:cmd_t list) =
  let cmds =
    List.filter
      (fun cmd -> match cmd with SKIP -> false | _ -> true) cmds in
  let cnstAssigns = finfo#env#end_transaction in
  TRANSACTION (label, LF.mkCode (cnstAssigns @ cmds), None)


(* Returns the predicate instruction and associated info for a conditional,
   in particular, it returns a tuple consisting of:
   - a list of temporary variables created to preserve the (frozen) values
     at the test location (testloc) for the location of the conditional (condloc)
   - the predicate that expresses the joint condition of test and condition
     code (cc, e.g., EQ), and
   - a list of the operands used in the creation of the predicate
 *)
let make_conditional_predicate
      ~(condinstr: arm_assembly_instruction_int)
      ~(testinstr: arm_assembly_instruction_int)
      ~(condloc: location_int)
      ~(testloc: location_int) =
  let (frozenvars, optxpr, opsused) =
    arm_conditional_expr
      ~condopc:condinstr#get_opcode
      ~testopc:testinstr#get_opcode
      ~condloc:condloc
      ~testloc:testloc in
  (frozenvars, optxpr, opsused)


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
  let get_default_conditional_expr () =
    arm_conditional_expr
      ~condopc:condinstr#get_opcode
      ~testopc:testinstr#get_opcode
      ~condloc
      ~testloc in
  let (frozenVars, optboolxpr, _) =
    if is_opcode_conditional testinstr#get_opcode then
      let finfo = testfloc#f in
      match get_associated_test_instr finfo testloc#ci with
      | Some (testtestloc, testtestinstr) ->
         arm_conditional_conditional_expr
           ~condopc:condinstr#get_opcode
           ~testopc: testinstr#get_opcode
           ~testtestopc: testtestinstr#get_opcode
           ~condloc
           ~testloc
           ~testtestloc
      | _ ->
         get_default_conditional_expr ()
    else
      get_default_conditional_expr () in

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
          List.map (fun e -> substitute_expr (fun _ -> e) expr) extxprs in
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
  let get_default_conditional_expr () =
    arm_conditional_expr
      ~condopc:condinstr#get_opcode
      ~testopc:testinstr#get_opcode
      ~condloc
      ~testloc in
  let (frozenVars, optboolxpr, _) =
    if is_opcode_conditional testinstr#get_opcode then
      let finfo = testfloc#f in
      match get_associated_test_instr finfo testloc#ci with
      | Some (testtestloc, testtestinstr) ->
        arm_conditional_conditional_expr
          ~condopc:condinstr#get_opcode
          ~testopc: testinstr#get_opcode
          ~testtestopc: testtestinstr#get_opcode
          ~condloc
          ~testloc
          ~testtestloc
      | _ ->
         get_default_conditional_expr ()
    else
      get_default_conditional_expr () in

  let _ =
    if testsupport#requested_arm_conditional_expr then
      testsupport#submit_arm_conditional_expr condinstr testinstr optboolxpr in

  let convert_to_chif ?(high=true) expr =
    let vars = variables_in_expr expr in
    let varscmds =
      if high then
        condfloc#get_vardef_commands ~usehigh:vars condloc#ci
      else
        condfloc#get_vardef_commands ~use:vars condloc#ci in
    let (cmds, bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ varscmds @ [ASSERT bxpr] in
  let convert_to_assert expr  =
    let vars = variables_in_expr expr in
    let varssize = List.length vars in
    let xprs =
      if varssize = 1 then
	let var = List.hd vars in
	let extxprs = condfloc#inv#get_external_exprs var in
	let extxprs =
          List.map (fun e -> substitute_expr (fun _ -> e) expr) extxprs in
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
    let _ =
      if testsupport#requested_chif_conditionxprs then
        testsupport#submit_chif_conditionxprs condinstr testinstr xprs in
    let basic_asserts = convert_to_chif ~high:false (List.hd xprs) in
    let rewritten_asserts = List.concat (List.map convert_to_chif (List.tl xprs)) in
    basic_asserts @ rewritten_asserts in

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


(* Returns the CHIF code for a conditional branch instruction that
   incorporates the full condition as part of the instruction (i.e. no
   dependency on a separate test instruction), such as CBZ or CBNZ.

   The CHIF code consists of a tuple of two sequences of CHIF commands.
   The first sequence is the CHIF for the then test, the second sequence
   is the CHIF for the else test.

   If the condition cannot be converted to CHIF SKIP commands are
   returned, that is, the conditional branch is effectively turned into
   a nondeterminstic branch.
 *)
let make_local_tests
      (condinstr: arm_assembly_instruction_int)
      (condloc: location_int): (cmd_t list * cmd_t list) =
  let floc = get_floc condloc in
  let env = floc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let boolxpr_r =
    match condinstr#get_opcode with
    | CompareBranchZero (op, _) ->
       TR.tmap
         ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
         (fun x -> XOp (XEq, [x; zero_constant_expr]))
         (op#to_expr floc)
    | CompareBranchNonzero (op, _) ->
       TR.tmap
         ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
         (fun x -> XOp (XNe, [x; zero_constant_expr]))
         (op#to_expr floc)
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Unexpected condition: " ^ (p2s condinstr#toPretty)] in

  let convert_to_chif expr =
    let vars = variables_in_expr expr in
    let defcmds = floc#get_vardef_commands ~usehigh:vars floc#l#ci in
    let (cmds, bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ defcmds @ [ASSERT bxpr] in
  let make_assert x =
    let _ = env#start_transaction in
    let commands = convert_to_chif x in
    let const_assigns = env#end_transaction in
    const_assigns @ commands in
  TR.tfold
    ~ok:(fun boolxpr ->
      let thencode = make_assert boolxpr in
      let elsecode = make_assert (simplify_xpr (XOp (XLNot, [boolxpr]))) in
      (thencode, elsecode))
    ~error:(fun e ->
      begin
        log_error_result __FILE__ __LINE__ e;
        ([SKIP], [SKIP])
      end)
    boolxpr_r


(* Returns the control-flow graph nodes and edges of a conditional branch
   instruction that incorporates the full condition as part of the instruction
   (i.e., no dependency on a separate test instruction), such as CBZ
   (CompareBranchZero) or CBNZ)

   Two cfg nodes are created: a 'then' node with the then-test and an 'else'
   node with the else-test. Four cfg edges are created: (1) from block label
   to thennode, (2) from block label to elsenode, (3) from thennode to the
   cfg target jump address, and (4) from elsenode to the cfg fall-through
   address.
 *)
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


(* Returns the control-flow graph nodes and edges of a conditional branch or an
   IfThen instruction that is handled with full control flow rather than with an
   aggregate. It applies to conditional branches in which the test is performed
   by a separate instruction (the test instruction) and the branch condition
   is determined by the combination of the test instruction and the condition
   code that is part of the branch instruction (or IfThen).

   If a conditional predicate for the branch can be synthesized and converted into
   CHIF, a 'then node' with the then-test and an 'else node' with the else-test
   are created. In both nodes the temporary variables that were created to carry
   the frozen values are abstracted to avoid unnecessary propagation of variables
   that will never be used again. Four edges are created: (1) from block-label
   to thenblock, (2) from thenblock to the cfg target jump address, (3) from
   block-label to elseblock, and (4) from elseblock to the cfg fall-through
   instruction.

   If a conditional predicate for the branch cannot be constructed the control flow
   components created represent a non-deterministic branch. One node is
   constructed, to abstract the temporary variables created by the attempt to
   create a condition. Three edges are created: (1) from block-label to the new
   node, (2) from the new node to the cfg target jump address, and (3) from the new
   node to the cfg fall-through instruction.
*)
let make_condition
      ?(thencode: cmd_t list = [])
      ?(elsecode: cmd_t list = [])
    ~(condinstr:arm_assembly_instruction_int)
    ~(testinstr:arm_assembly_instruction_int)
    ~(condloc:location_int)
    ~(testloc:location_int)
    ~(blocklabel:symbol_t)
    ~(thenaddr:ctxt_iaddress_t)
    ~(elseaddr:ctxt_iaddress_t)
    () =
  let thenlabel = make_code_label thenaddr in
  let elselabel = make_code_label elseaddr in
  let (frozenVars, tests) =
    make_tests ~condloc ~testloc ~condinstr ~testinstr in
  match tests with
    Some (thentest, elsetest) ->
      let make_node_and_label testcode tgtaddr modifier =
	let src = condloc#i in
	let nextlabel = make_code_label ~src ~modifier tgtaddr in
	let testcode =
          testcode
          @ (match frozenVars with
             | [] -> []
             | _ -> [ABSTRACT_VARS frozenVars]) in
	let transaction = TRANSACTION (nextlabel, LF.mkCode testcode, None) in
	(nextlabel, [transaction]) in
      let (thentestlabel, thennode) =
	make_node_and_label (thencode @ thentest) thenaddr "then" in
      let (elsetestlabel, elsenode) =
	make_node_and_label (elsecode @ elsetest) elseaddr "else" in
      let thenedges =
	[(blocklabel, thentestlabel); (thentestlabel, thenlabel)] in
      let elseedges =
	[(blocklabel, elsetestlabel); (elsetestlabel, elselabel) ] in
      ([(thentestlabel, thennode); (elsetestlabel, elsenode)],
       thenedges @ elseedges)
  | _ ->
     let abstractlabel =
       make_code_label ~modifier:"abstract" testloc#ci in
     let trcode =
       match frozenVars with
       | [] -> [SKIP]
       | _ -> [ABSTRACT_VARS frozenVars] in
     let transaction =
       TRANSACTION (abstractlabel, LF.mkCode trcode, None) in
     let edges = [
         (blocklabel, abstractlabel);
         (abstractlabel, thenlabel);
	 (abstractlabel, elselabel)] in
     ([(abstractlabel, [transaction])], edges)


let translate_arm_instruction
      ~(funloc:location_int)
      ~(codepc:arm_code_pc_int)
      ~(blocklabel:symbol_t)
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
    List.map (fun (v,fv) -> ASSERT (EQ (v, fv)))
      (finfo#get_test_variables ctxtiaddr) in
  let rewrite_expr (floc: floc_int) (x:xpr_t): xpr_t =
    let xpr = floc#inv#rewrite_expr x in
    let rec expand x =
      match x with
      | XVar v when floc#env#is_symbolic_value v ->
         expand (TR.tget_ok (floc#env#get_symbolic_value_expr v))
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
  let log_dc_error_result (file: string) (line: int) (e: string list) =
    if BCHSystemSettings.system_settings#collect_data then
      log_error_result ~msg:(p2s floc#l#toPretty) file line e
    else
      () in
  let pcv = TR.tget_ok ((pc_r RD)#to_variable floc) in
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

  let make_conditional_commands (_c: arm_opcode_cc_t) (cmds: cmd_t list) =
    if instr#is_condition_covered then
      default cmds
    else
      match get_associated_test_instr finfo ctxtiaddr with
      | Some (testloc, testinstr) ->
         let (_, tests) =
           make_instr_local_tests
             ~condloc:loc ~testloc ~condinstr:instr ~testinstr in
         (match tests with
          | Some (thentest, elsetest) ->
             if has_false_condition_context ctxtiaddr then
               default elsetest
             else if has_true_condition_context ctxtiaddr then
               default (thentest @ cmds)
             else
               default [BRANCH [LF.mkCode (thentest @ cmds); LF.mkCode elsetest]]
          | _ ->
             (* make non-deterministic branch, unless covered by True/False
                context*)
             if has_false_condition_context ctxtiaddr then
               default []
             else if has_true_condition_context ctxtiaddr then
               default cmds
             else
               default [BRANCH [LF.mkCode cmds; LF.mkCode [SKIP]]])
      | _ ->
         if has_false_condition_context ctxtiaddr then
           default []
         else if has_true_condition_context ctxtiaddr then
           default cmds
         else
           default [BRANCH [LF.mkCode cmds; LF.mkCode [SKIP]]] in

  let get_register_vars (ops: arm_operand_int list) =
    List.fold_left (fun acc op ->
        if op#is_register || op#is_extension_register then
          (TR.tget_ok (op#to_variable floc)) :: acc
        else
          match op#get_kind with
          | ARMShiftedReg (r, ARMImmSRT _) ->
             (floc#env#mk_arm_register_variable r) :: acc
          | ARMShiftedReg (r, ARMRegSRT (_, rs)) ->
             let rvar = floc#env#mk_arm_register_variable r in
             let rsvar = floc#env#mk_arm_register_variable rs in
             rvar :: rsvar :: acc
          | ARMRegBitSequence (r, _, _) ->
             (floc#env#mk_arm_register_variable r) :: acc
          | _ -> acc) [] ops in

  let get_use_high_vars ?(is_pop=false) (xprs: xpr_t list): variable_t list =
    let inv = floc#inv in
    List.fold_left (fun acc x ->
        let xw = inv#rewrite_expr x in
        let xs = simplify_xpr xw in
        let disvars = inv#get_init_disequalities in
        let disvars =
          List.filter
            (fun v ->
              not ((floc#f#env#is_initial_stackpointer_value v)
                   || (floc#f#env#is_initial_register_value v))) disvars in
        let is_disvar v = List.exists (fun vv -> v#equal vv) disvars in
        let xprvars = floc#env#variables_in_expr xs in
        let vars =
          if List.exists is_disvar xprvars && not is_pop then
            let _ =
              chlog#add
                "get_use_high_vars:basic"
                (LBLOCK [
                     floc#l#toPretty;
                     STR "  ";
                     x2p xs;
                     STR " ==> ";
                     x2p x;
                     pretty_print_list
                       (floc#env#variables_in_expr x)
                       (fun v -> v#toPretty)
                       " [" "; " "]"]) in
            floc#env#variables_in_expr x
          else
            List.filter (fun v -> not (floc#f#env#is_function_initial_value v))
              xprvars in
        vars @ acc) [] xprs in

  let get_use_high_vars_r
        ?(is_pop=false)
        (xprrs: xpr_t traceresult list): variable_t list =
    let xprs =
      List.fold_left (fun acc x_r ->
          TR.tfold_default (fun x -> x :: acc) acc x_r) [] xprrs in
    get_use_high_vars ~is_pop xprs in

  let get_addr_use_high_vars_r (xprs: xpr_t traceresult list): variable_t list =
    (* Don't apply invariants to the expressions *)
    List.fold_left (fun acc x_r ->
        let x_r = TR.tmap simplify_xpr x_r in
        TR.tfold_default
          (fun x ->
            let vars =
              List.filter (fun v -> not (floc#f#env#is_function_initial_value v))
                (floc#env#variables_in_expr x) in
            vars @ acc)
          acc
          x_r) [] xprs in

  let flagdefs =
    let flags_set = get_arm_flags_set instr#get_opcode in
    List.map (fun f -> finfo#env#mk_flag_variable (ARMCCFlag f)) flags_set in
  let apsr_flagdefs =
    let flags_set = [APSR_N; APSR_Z; APSR_C; APSR_V] in
    List.map (fun f -> finfo#env#mk_flag_variable (ARMCCFlag f)) flags_set in
  let in_jumptable_seq =
    match instr#is_in_aggregate with
    | Some dw -> (get_aggregate dw)#is_jumptable
    | _ -> false in

  let is_part_of_pseudo_instr () =
    match instr#is_in_aggregate with
    | Some dw ->
       let agg = get_aggregate dw in
       agg#is_pseudo_ldrsh || agg#is_pseudo_ldrsb
    | _ -> false in

  let calltgt_cmds (_tgt: arm_operand_int): cmd_t list =
    let callargs = floc#get_call_arguments in
    let fintf = floc#get_call_target#get_function_interface in
    let rtype = get_fts_returntype fintf in
    let returnreg =
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
    let returnvar = floc#f#env#mk_register_variable returnreg in
    let (usecmds, use, usehigh) =
      List.fold_left (fun (acccmds, accuse, accusehigh) (p, x) ->
          let ptype = get_parameter_type p in
          let addressedvars =
            if is_pointer ptype && (not (is_char_pointer ptype)) then
              let xx = rewrite_expr floc x in
              match BCHARMDisassemblyUtils.get_string_reference floc xx with
              | Some _ -> []
              | _ ->
                 match xx with
                 | XVar _ -> []
                 | _ ->
                    TR.tfold
                      ~ok:(fun v -> [v])
                      ~error:(fun e ->
                        let _ = log_dc_error_result __FILE__ __LINE__ e in
                        [])
                      (floc#get_var_at_address ~btype:(ptr_deref ptype) xx)
            else
              [] in
          if is_register_parameter p then
            let regarg = TR.tget_ok (get_register_parameter_register p) in
            let pvar = floc#f#env#mk_register_variable regarg in
            (acccmds,
             pvar :: (addressedvars @ accuse),
             addressedvars @ accusehigh)

          else if is_stack_parameter p then
            let p_offset = TR.tget_ok (get_stack_parameter_offset p) in
            let stackop = arm_sp_deref ~with_offset:p_offset RD in
            TR.tfold
              ~ok:(fun (stacklhs, stacklhscmds) ->
                (stacklhscmds @ acccmds,
                 stacklhs :: (addressedvars @ accuse),
                 addressedvars @ accusehigh))
              ~error:(fun e ->
                begin
                  log_error_result __FILE__ __LINE__ e;
                  (acccmds, accuse, accusehigh)
                end)
              (stackop#to_lhs floc)
          else
            raise
              (BCH_failure
                 (LBLOCK [
                      floc#l#toPretty;
                      STR "  Parameter type not recognized in call translation"])))
        ([], [], []) callargs in
    let usehigh = usehigh @ (get_use_high_vars (List.map snd callargs)) in
    let vr1 = floc#f#env#mk_arm_register_variable AR1 in
    let vr2 = floc#f#env#mk_arm_register_variable AR2 in
    let vr3 = floc#f#env#mk_arm_register_variable AR3 in
    let callcmds = floc#get_arm_call_commands in
    let defcmds =
      floc#get_vardef_commands
        ~defs:[returnvar]
        ~clobbers:[vr1; vr2; vr3]
        ~use
        ~usehigh
        ctxtiaddr in
    usecmds @ defcmds @ callcmds in

  match instr#get_opcode with

  | Branch _ | BranchExchange _ when in_jumptable_seq ->
     (* nothing to add to the semantics at this point *)
     default []

  | Branch (c, tgt, _) when floc#has_call_target ->
     let cmds = calltgt_cmds tgt in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | Branch (c, op, _)
    | BranchExchange (c, op) when is_cond_conditional c ->
     let thenaddr =
       if op#is_absolute_address then
         (make_i_location loc op#get_absolute_address)#ci
       else if op#is_register && op#get_register = ARLR then
         "exit"
       else
         "?" in
     let defcmds =
       match get_associated_test_instr finfo ctxtiaddr with
       | Some (testloc, testinstr) ->
         let (_, optxpr, opsused) =
           make_conditional_predicate
             ~condinstr:instr
             ~testinstr:testinstr
             ~condloc:loc
             ~testloc in
         let use = get_register_vars opsused in
         let usehigh = match optxpr with
           | Some xpr -> get_use_high_vars [xpr]
           | _ -> [] in
         floc#get_vardef_commands ~use ~usehigh ctxtiaddr
       | _ ->
         [] in
     let elseaddr = codepc#get_false_branch_successor in
     let cmds = cmds @ [invop] @ defcmds @ [bwdinvop] in
     let transaction = package_transaction finfo blocklabel cmds in
     if finfo#has_associated_cc_setter ctxtiaddr then
       let testiaddr = finfo#get_associated_cc_setter ctxtiaddr in
       let testloc = ctxt_string_to_location faddr testiaddr in
       let testaddr = (ctxt_string_to_location faddr testiaddr)#i in
       let testinstr =
         fail_tvalue
           (trerror_record
              (LBLOCK [STR "Internal error in make_instr_local_tests"]))
           (get_arm_assembly_instruction testaddr) in
       let (nodes, edges) =
         make_condition
           ~condinstr:instr
           ~testinstr:testinstr
           ~condloc:loc
           ~testloc
           ~blocklabel
           ~thenaddr
           ~elseaddr () in
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
     let usehigh =
       TR.tfold
         ~ok:(fun x -> get_use_high_vars [x])
         ~error:(fun e ->
           begin
             log_error_result __FILE__ __LINE__ e;
             []
           end)
         (op#to_expr floc) in
     let defcmds = floc#get_vardef_commands ~use:usevars ~usehigh ctxtiaddr in
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
     let returntype = finfo#get_summary#get_returntype in
     let defcmds =
       match returntype with
       | TVoid _ -> []
       | _ ->
          let r0_op = arm_register_op AR0 RD in
          let usevars = get_register_vars [r0_op] in
          let xr0 = r0_op#to_expr floc in
          let usehigh = get_use_high_vars_r [xr0] in
          floc#get_vardef_commands ~use:usevars ~usehigh ctxtiaddr in
     default defcmds

  | Branch (_, op, _)
    | BranchExchange (_, op) when op#is_register ->
     let usevars = get_register_vars [op] in
     let xop = op#to_expr floc in
     let usehigh = get_use_high_vars_r [xop] in
     let defcmds = floc#get_vardef_commands ~use:usevars ~usehigh ctxtiaddr in
     default defcmds

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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let result_r =
       TR.tmap2 (fun xrn xrm -> XOp (XPlus, [xrn; xrm])) xrn_r xrm_r in
     (* let result = floc#inv#rewrite_expr result in
     let result = simplify_xpr result in *)
     let result_r =
       TR.tmap (fun result ->
           match result with
           | XConst (IntConst n) when n#geq numerical_e32 ->
              (* Assume unsigned roll-over *)
              XConst (IntConst (n#sub numerical_e32))
           | _ ->
              result) result_r in
     let cmds = floc#get_assign_commands_r lhs_r result_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ~flagdefs:flagdefs
         ctxtiaddr in
     let cmds = cmds @ defcmds in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap (fun (v, _) -> v) (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
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

  | Adr (c, rd, src) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let rhs_r = src#to_expr floc in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | ArithmeticShiftRight _ when is_part_of_pseudo_instr () ->
     default []

  | ArithmeticShiftRight(_, c, rd, rn, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r =
       TR.tmap2
         (fun xrn xrm ->
           match xrm with
           | XConst (IntConst n) when n#toInt = 2->
              XOp (XDiv, [xrn; XConst (IntConst (mkNumerical 4))])
           | _ -> XOp (XAsr, [xrn; xrm]))
         xrn_r xrm_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
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

  | BitFieldClear (c, rd, _, _, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let rhs_r = rd#to_expr floc in
     let usevars = get_register_vars [rd] in
     let usehigh = get_use_high_vars_r [rhs_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
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

  | BitFieldInsert (c, rd, rn, _, _, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrd_r = rd#to_expr floc in
     let xrn_r = rn#to_expr floc in
     let usevars = get_register_vars [rd; rn] in
     let usehigh = get_use_high_vars_r [xrd_r; xrn_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
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

  | BitwiseAnd (_, c, rd, rn, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r =
       TR.tmap2 (fun xrn xrm -> XOp (XBAnd, [xrn; xrm])) xrn_r xrm_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r =
       TR.tmap2
         (fun xrn xrm -> XOp (XBAnd, [xrn; XOp (XBNot, [xrm])]))
         xrn_r xrm_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
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
  | BitwiseNot _ when Option.is_some instr#is_in_aggregate ->
     (* may be part of a ternary assignment.
        TODO: add code for the case where MVN is the anchor instruction.*)
     default []

  | BitwiseNot (_, c, rd, rm, _) when rm#is_immediate ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let rhs_r = rm#to_expr floc in
     let rhs_r =
       TR.tbind
         ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
         (fun rhs ->
           match rhs with
           | XConst (IntConst n) when n#equal numerical_zero ->
              Ok (XConst (IntConst numerical_one#neg))
           | XConst (IntConst n) ->
              Ok (XConst (IntConst ((nume32#sub n)#sub numerical_one)))
           | _ ->
              Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
                     ^ "Unable to invert " ^ (x2s rhs)])
         rhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [rhs_r] in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
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

  | BitwiseNot (_, c, rd, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let rhs_r = rm#to_expr floc in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [rhs_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds =  defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BitwiseOr (_, c, rd, rn, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
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
  | BranchLink (c, tgt)
    | BranchLinkExchange (c, tgt) when tgt#is_absolute_address ->
     if instr#is_inlined_call then
       default []
     else
       let cmds = calltgt_cmds tgt in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | BranchLink (c,_)
    | BranchLinkExchange (c, _) ->
     let vr0 = floc#f#env#mk_arm_register_variable AR0 in
     let vr1 = floc#f#env#mk_arm_register_variable AR1 in
     let vr2 = floc#f#env#mk_arm_register_variable AR2 in
     let vr3 = floc#f#env#mk_arm_register_variable AR3 in
     let (defs, use, usehigh) =
       let use = [vr0; vr1; vr2; vr3] in
       ([vr0], use, use) in
     let cmds = floc#get_arm_call_commands in
     let defcmds =
       floc#get_vardef_commands
         ~defs:defs
         ~clobbers:[vr1; vr2; vr3]
         ~use:use
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = cmds @ defcmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | ByteReverseWord (c, rd, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
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
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default defcmds
      | _ -> make_conditional_commands c cmds)

  | DataMemoryBarrier _ ->
     default []

  | IfThen _ when instr#is_aggregate_anchor ->
     (match get_associated_test_instr finfo ctxtiaddr with
      | Some (testloc, testinstr) ->
         let itagg = get_aggregate loc#i in
         let its = itagg#it_sequence in
         (match its#kind with
          | ITPredicateAssignment (inverse, dstop) ->
             let (_, optpredicate, _opsused) =
               make_conditional_predicate
                 ~condinstr:instr
                 ~testinstr:testinstr
                 ~condloc:loc
                 ~testloc:testloc in
             let cmds =
               match optpredicate with
               | Some p ->
                  let p = if inverse then XOp (XLNot, [p]) else p in
                  let vrd = floc#env#mk_register_variable dstop#to_register in
                  let lhs_r = TR.tmap fst (dstop#to_lhs floc) in
                  let usevars = vars_in_expr_list [p] in
                  let usehigh = get_use_high_vars [p] in
                  let cmds = floc#get_assign_commands_r lhs_r (Ok p) in
                  let defcmds =
                    floc#get_vardef_commands
                      ~defs:[vrd]
                      ~use:usevars
                      ~usehigh:usehigh
                      ~flagdefs:flagdefs
                      ctxtiaddr in
                  defcmds @ cmds
               | _ ->
                  begin
                    log_error_result
                      ~tag:"IfThen"
                      __FILE__ __LINE__
                      ["Predicate assignment without predicate"];
                    []
                  end in
             default cmds)
      | _ ->
         begin
           log_error_result
             ~tag:"IfThen"
             __FILE__ __LINE__
             ["Aggregate IfThen without associated cc setter"];
           default []
         end)

  | IfThen _ when instr#is_block_condition ->
     let thenaddr = codepc#get_true_branch_successor in
     let elseaddr = codepc#get_false_branch_successor in
     let cmds = cmds @ [invop] in
     let transaction = package_transaction finfo blocklabel cmds in
     (match get_associated_test_instr finfo ctxtiaddr with
      | Some (testloc, testinstr) ->
         let (nodes, edges) =
           make_condition
             ~condinstr:instr
             ~testinstr:testinstr
             ~condloc:loc
             ~testloc
             ~blocklabel
             ~thenaddr
             ~elseaddr () in
         ((blocklabel, [transaction]) :: nodes, edges, [])
      | _ ->
         let thenlabel = make_code_label thenaddr in
         let elselabel = make_code_label elseaddr in
         let nodes = [(blocklabel, [transaction])] in
         let edges = [(blocklabel, thenlabel); (blocklabel, elselabel)] in
         (nodes, edges, []))

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
     let basereg = base#get_register in
     let usevars = get_register_vars [base] in
     let regcount = rl#get_register_count in
     let regs = rl#to_multiple_register in
     let basedefcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let (memreads, _) =
       List.fold_left
         (fun (acc, off) reg ->
           let regvar = floc#env#mk_register_variable reg in
           let memop = arm_reg_deref basereg ~with_offset:off RD in
           let memvar_r = memop#to_variable floc in
           let memrhs_r = memop#to_expr floc in
           let memuse = TR.tfold_default (fun memvar -> [memvar]) [] memvar_r in
           let memusehigh = get_use_high_vars_r [memrhs_r] in
           let cmds1 = floc#get_assign_commands_r memvar_r memrhs_r in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[regvar]
               ~use:memuse
               ~usehigh:memusehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + 4)) ([], 4 - (4 * regcount)) regs in
     let wbackassign =
       if wback then
         let lhs = floc#env#mk_register_variable base#to_register in
         let rhs_r = base#to_expr floc in
         let decrem = int_constant_expr (4 * regcount) in
         let rhs_r = TR.tmap (fun rhs -> XOp (XMinus, [rhs; decrem])) rhs_r in
         let wbackcmds = floc#get_assign_commands_r (Ok lhs) rhs_r in
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
     let basereg = base#get_register in
     let usevars = get_register_vars [base] in
     let regcount = rl#get_register_count in
     let regs = rl#to_multiple_register in
     let basedefcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let (memreads, _) =
       List.fold_left
         (fun (acc, off) reg ->
           let regvar = floc#env#mk_register_variable reg in
           let memop = arm_reg_deref basereg ~with_offset:off RD in
           let memvar_r = memop#to_variable floc in
           let memrhs_r = memop#to_expr floc in
           let memuse = TR.tfold_default (fun memvar -> [memvar]) [] memvar_r in
           let memusehigh = get_use_high_vars_r [memrhs_r] in
           let cmds1 = floc#get_assign_commands_r memvar_r memrhs_r in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[regvar]
               ~use:memuse
               ~usehigh:memusehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + 4)) ([], -(4 * regcount)) regs in
     let wbackassign =
       if wback then
         let lhs = floc#env#mk_register_variable base#to_register in
         let rhs_r = base#to_expr floc in
         let decrem = int_constant_expr (4 * regcount) in
         let rhs_r = TR.tmap (fun rhs -> XOp (XMinus, [rhs; decrem])) rhs_r in
         let wbackcmds = floc#get_assign_commands_r (Ok lhs) rhs_r in
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
     let basereg = base#get_register in
     let usevars = get_register_vars [base] in
     let regcount = rl#get_register_count in
     let regs = rl#to_multiple_register in
     let basedefcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let (memreads, _) =
       List.fold_left
         (fun (acc, off) reg ->
           let regvar = floc#env#mk_register_variable reg in
           let memop = arm_reg_deref ~with_offset:off basereg RD in
           let memvar_r = memop#to_variable floc in
           let memrhs_r = memop#to_expr floc in
           let memuse = TR.tfold_default (fun memvar -> [memvar]) [] memvar_r in
           let memusehigh = get_use_high_vars_r [memrhs_r] in
           let cmds1 = floc#get_assign_commands_r (Ok regvar) memrhs_r in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[regvar]
               ~use:memuse
               ~usehigh:memusehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + 4)) ([], 0) regs in
     let wbackassign =
       if wback then
         let lhs = floc#env#mk_register_variable base#to_register in
         let rhs_r = base#to_expr floc in
         let increm = int_constant_expr (4 * regcount) in
         let rhs_r = TR.tmap (fun rhs -> XOp (XPlus, [rhs; increm])) rhs_r in
         let wbackcmds = floc#get_assign_commands_r (Ok lhs) rhs_r in
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
     let basereg = base#get_register in
     let usevars = get_register_vars [base] in
     let regcount = rl#get_register_count in
     let regs = rl#to_multiple_register in
     let basedefcmds = floc#get_vardef_commands ~use:usevars ctxtiaddr in
     let (memreads, _) =
       List.fold_left
         (fun (acc, off) reg ->
           let regvar = floc#env#mk_register_variable reg in
           let memop = arm_reg_deref ~with_offset:off basereg RD in
           let memvar_r = memop#to_variable floc in
           let memrhs_r = memop#to_expr floc in
           let memuse = TR.tfold_default (fun memvar -> [memvar]) [] memvar_r in
           let memusehigh = get_use_high_vars_r [memrhs_r] in
           let cmds1 = floc#get_assign_commands_r memvar_r memrhs_r in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[regvar]
               ~use:memuse
               ~usehigh:memusehigh
               ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + 4)) ([], 4) regs in
     let wbackassign =
       if wback then
         let lhs = floc#env#mk_register_variable base#to_register in
         let rhs_r = base#to_expr floc in
         let increm = int_constant_expr (4 * regcount) in
         let rhs_r = TR.tmap (fun rhs -> XOp (XPlus, [rhs; increm])) rhs_r in
         let wbackcmds = floc#get_assign_commands_r (Ok lhs) rhs_r in
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
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let rhs_r = mem#to_expr floc in
     let rhs_r = TR.tmap floc#inv#rewrite_expr rhs_r in
     let vrd = floc#env#mk_register_variable rt#to_register in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let baselhs = floc#env#mk_register_variable rn#to_register in
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let ucmds = floc#get_assign_commands_r (Ok baselhs) addr_r in
         let defupdatecmds = floc#get_vardef_commands ~defs:[baselhs] ctxtiaddr in
         defupdatecmds @ ucmds
       else
         [] in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let cmds = cmds @ updatecmds in
     let usevars = get_register_vars [rn; rm] in
     let memvar_r = mem#to_variable floc in
     let (usevars, usehigh) =
       TR.tfold
         ~error:(fun _ ->
           (* elevate address variables to high-use *)
           let xrn_r = rn#to_expr floc in
           let xrm_r = rm#to_expr floc in
           (usevars, get_use_high_vars_r [xrn_r; xrm_r]))
         ~ok:(fun memvar ->
           if floc#env#has_variable_index_offset memvar then
             let xrn_r = rn#to_expr floc in
             let xrm_r = rm#to_expr floc in
             (usevars, get_use_high_vars_r [xrn_r; xrm_r])
           else
             (memvar :: usevars, get_use_high_vars_r [rhs_r]))
         memvar_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     let _ =
       TR.tfold_default
         (fun rhs ->
           (* record register restore *)
           let rhs = rewrite_expr floc rhs in
           match rhs with
           | XVar rhsvar ->
              if floc#f#env#is_initial_register_value rhsvar then
                let memreg =
                  TR.tget_ok
                    (floc#f#env#get_initial_register_value_register rhsvar) in
                match memreg with
                | ARMRegister r when r = rt#get_register ->
                   TR.tfold_default
                   (fun memaddr ->
                     let memaddr = floc#inv#rewrite_expr memaddr in
                     finfo#restore_register memaddr floc#cia rt#to_register)
                   ()
                   (mem#to_address floc)
                | _ -> ()
              else
                ()
           | _ -> ())
         ()
         rhs_r in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ---------------------------------------------------- LoadRegisterByte -- *
   * R[t] = ZeroExtend(MemU[address,1], 32);
   * if wback then R[n] = offset_addr;
   * -------------------------------------------------------------------------*)
  | LoadRegisterByte (c, rt, rn, rm, mem, _) ->
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let rhs_r = mem#to_expr floc in
     let vrd = floc#env#mk_register_variable rt#to_register in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let baselhs = floc#env#mk_register_variable rn#to_register in
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let ucmds = floc#get_assign_commands_r (Ok baselhs) addr_r in
         let defupdatecmds = floc#get_vardef_commands ~defs:[baselhs] ctxtiaddr in
         defupdatecmds @ ucmds
       else
         [] in
     let cmds = floc#get_assign_commands_r ~size:1 lhs_r rhs_r in
     let cmds = cmds @ updatecmds in
     let usevars = get_register_vars [rn; rm] in
     let memvar_r = mem#to_variable floc in
     let (usevars, usehigh) =
       TR.tfold
         ~error:(fun _ ->
           (* elevate address variables to high-use *)
           let xrn_r = rn#to_expr floc in
           let xrm_r = rm#to_expr floc in
           (usevars, get_use_high_vars_r [xrn_r; xrm_r]))
         ~ok:(fun memvar ->
           (memvar :: usevars, get_use_high_vars_r [rhs_r]))
       memvar_r in
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

  | LoadRegisterDual (c, rt, rt2, rn, rm, mem, mem2) ->
     let lhs1_r = TR.tmap fst (rt#to_lhs floc) in
     let lhs2_r = TR.tmap fst (rt2#to_lhs floc) in
     let vrd1 = floc#env#mk_register_variable rt#to_register in
     let vrd2 = floc#env#mk_register_variable rt2#to_register in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let baselhs = floc#env#mk_register_variable rn#to_register in
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let ucmds = floc#get_assign_commands_r (Ok baselhs) addr_r in
         let defupdatecmds = floc#get_vardef_commands ~defs:[baselhs] ctxtiaddr in
         defupdatecmds @ ucmds
       else
         [] in
     let memvar1_r = mem#to_variable floc in
     let memvar2_r = mem2#to_variable floc in
     let rhs1_r = mem#to_expr floc in
     let rhs2_r = mem2#to_expr floc in
     let cmds1 = floc#get_assign_commands_r lhs1_r rhs1_r in
     let cmds2 = floc#get_assign_commands_r lhs2_r rhs2_r in
     let usevars = get_register_vars [rn; rm] in
     let usevars =
       TR.tfold_default (fun memvar1 -> memvar1 :: usevars) usevars memvar1_r in
     let usevars =
       TR.tfold_default (fun memvar2 -> memvar2 :: usevars) usevars memvar2_r in
     let usehigh = get_use_high_vars_r [rhs1_r; rhs2_r] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd1; vrd2]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds1 @ cmds2 @ updatecmds in
     let _ =
       (* record register restores *)
       List.iter (fun (rt, mem, rhs_r) ->
           TR.tfold_default
             (fun rhs ->
               let rhs = rewrite_expr floc rhs in
               match rhs with
               | XVar rhsvar ->
                  if floc#f#env#is_initial_register_value rhsvar then
                    let memreg =
                      TR.tget_ok
                        (floc#f#env#get_initial_register_value_register rhsvar) in
                    match memreg with
                    | ARMRegister r when r = rt#get_register ->
                       TR.tfold_default
                       (fun memaddr ->
                         let memaddr = floc#inv#rewrite_expr memaddr in
                         finfo#restore_register memaddr floc#cia rt#to_register)
                       ()
                       (mem#to_address floc)
                    | _ -> ()
                  else
                    ()
               | _ -> ())
             ()
             rhs_r) [(rt, mem, rhs1_r); (rt2, mem2, rhs2_r)] in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LoadRegisterExclusive (c, rt, rn, rm, mem) ->
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let rhs_r = mem#to_expr floc in
     let vrd = floc#env#mk_register_variable rt#to_register in
     let memvar_r = mem#to_variable floc in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usevars =
       TR.tfold_default (fun memvar -> memvar :: usevars) usevars memvar_r in
     let usehigh = get_use_high_vars_r [rhs_r] in
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

  | LoadRegisterHalfword (c, rt, rn,rm, mem, _) ->
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let rhs_r = mem#to_expr floc in
     let vrd = floc#env#mk_register_variable rt#to_register in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let baselhs = floc#env#mk_register_variable rn#to_register in
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let ucmds = floc#get_assign_commands_r (Ok baselhs) addr_r in
         let defupdatecmds = floc#get_vardef_commands ~defs:[baselhs] ctxtiaddr in
         defupdatecmds @ ucmds
       else
         [] in
     let cmds = floc#get_assign_commands_r ~size:2 lhs_r rhs_r in
     let memvar_r = mem#to_variable floc in
     let usevars = get_register_vars [rn; rm] in
     let (usevars, usehigh) =
       TR.tfold
         ~error:(fun _ ->
           (* elevate address variables to high-use *)
           let xrn_r = rn#to_expr floc in
           let xrm_r = rm#to_expr floc in
           (usevars, get_use_high_vars_r [xrn_r; xrm_r]))
         ~ok:(fun memvar ->
           (memvar :: usevars, get_use_high_vars_r [rhs_r]))
         memvar_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds @ updatecmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LoadRegisterSignedHalfword (c, rt, rn, rm, mem, _) ->
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let rhs_r = mem#to_expr floc in
     let vrd = floc#env#mk_register_variable rt#to_register in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let baselhs = floc#env#mk_register_variable rn#to_register in
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let ucmds = floc#get_assign_commands_r (Ok baselhs) addr_r in
         let defupdatecmds = floc#get_vardef_commands ~defs:[baselhs] ctxtiaddr in
         defupdatecmds @ ucmds
       else
         [] in
     let cmds = floc#get_assign_commands_r ~size:2 ~signed:true lhs_r rhs_r in
     let memvar_r = mem#to_variable floc in
     let usevars = get_register_vars [rn; rm] in
     let (usevars, usehigh) =
       TR.tfold
         ~error:(fun _ ->
           (* elevate address variables to high-use *)
           let xrn_r = rn#to_expr floc in
           let xrm_r = rm#to_expr floc in
           (usevars, get_use_high_vars_r [xrn_r; xrm_r]))
         ~ok:(fun memvar ->
           (memvar :: usevars, get_use_high_vars_r [rhs_r]))
         memvar_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds @ updatecmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LoadRegisterSignedByte (c, rt, rn, rm, mem, _) ->
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let rhs_r = mem#to_expr floc in
     let vrd = floc#env#mk_register_variable rt#to_register in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let baselhs = floc#env#mk_register_variable rn#to_register in
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let ucmds = floc#get_assign_commands_r (Ok baselhs) addr_r in
         let defupdatecmds = floc#get_vardef_commands ~defs:[baselhs] ctxtiaddr in
         defupdatecmds @ ucmds
       else
         [] in
     let cmds = floc#get_assign_commands_r ~size:1 ~signed:true lhs_r rhs_r in
     let memvar_r = mem#to_variable floc in
     let usevars = get_register_vars [rn; rm] in
     let (usevars, usehigh) =
       TR.tfold
         ~error:(fun _ ->
           (* elevate address variables to high-use *)
           let xrn_r = rn#to_expr floc in
           let xrm_r = rm#to_expr floc in
           (usevars, get_use_high_vars_r [xrn_r; xrm_r]))
         ~ok:(fun memvar ->
           (memvar :: usevars, get_use_high_vars_r [rhs_r]))
         memvar_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds @ updatecmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | LogicalShiftLeft _ when is_part_of_pseudo_instr () ->
     default []

  | LogicalShiftLeft (_, c, rd, rn, rm, _) when rm#is_small_immediate ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xxrn_r = TR.tmap (rewrite_expr floc) xrn_r in
     let m = rm#to_numerical#toInt in
     let factor = match m with
       | 0 -> 1
       | 1 -> 2
       | 2 -> 4
       | 3 -> 8
       | 4 -> 16
       | 5 -> 32
       | 6 -> 64
       | _ -> 1 in  (* not reachable by small immediate *)
     let usevars = get_register_vars [rn] in
     let usehigh = get_use_high_vars_r [xxrn_r] in
     let rhs_r =
       TR.tmap
         (fun xxrn -> XOp (XMult, [xxrn; int_constant_expr factor]))
         xxrn_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
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

  | LogicalShiftLeft (_, c, rd, rn, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let rhs_r = TR.tmap2 (fun xrn xrm ->  XOp (XLsl, [xrn; xrm])) xrn_r xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap2 (fun xrn xrm -> XOp (XLsr, [xrn; xrm])) xrn_r xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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
  | Move (_, _, rd, _, _, _) when instr#is_aggregate_anchor ->
     (match get_associated_test_instr finfo ctxtiaddr with
      | Some (testloc, testinstr) ->
         let movagg = get_aggregate loc#i in
         (match movagg#kind with
          | ARMPredicateAssignment (inverse, dstop) ->
             let (_, optpredicate, _) =
               make_conditional_predicate
                 ~condinstr:instr ~testinstr ~condloc:loc ~testloc in
             let cmds =
               let lhs_r = TR.tmap fst (dstop#to_lhs floc) in
               let vrd = floc#env#mk_register_variable dstop#to_register in
               match optpredicate with
               | Some p ->
                  let p = if inverse then XOp (XLNot, [p]) else p in
                  let cmds = floc#get_assign_commands_r lhs_r (Ok p) in
                  let usevars = vars_in_expr_list [p] in
                  let usehigh = get_use_high_vars [p] in
                  let defcmds =
                    floc#get_vardef_commands
                      ~defs:[vrd]
                      ~use:usevars
                      ~usehigh
                      ~flagdefs
                      ctxtiaddr in
                  defcmds @ cmds
               | _ ->
                  let _ =
                    chlog#add
                      "predicate assignment:no predicate"
                      (LBLOCK [floc#l#toPretty]) in
                  let cmds = floc#get_abstract_commands_r lhs_r in
                  let defcmds =
                    floc#get_vardef_commands ~defs:[vrd] ~flagdefs ctxtiaddr in
                  defcmds @ cmds in
             default cmds
          | ARMTernaryAssignment (dstop, n1, n2) ->
             let (_, optpredicate, _) =
               make_conditional_predicate
                 ~condinstr:instr ~testinstr ~condloc:loc ~testloc in
             let (_, tests) =
               make_instr_local_tests
                 ~condloc:loc ~testloc ~condinstr:instr ~testinstr in
             let cmds =
               let lhs_r = TR.tmap fst (dstop#to_lhs floc) in
               let vrd = floc#env#mk_register_variable dstop#to_register in
               match optpredicate with
               | Some p ->
                  let x1 = XConst (IntConst n1) in
                  let x2 = XConst (IntConst n2) in
                  let cmd1 = floc#get_assign_commands_r lhs_r (Ok x1) in
                  let cmd2 = floc#get_assign_commands_r lhs_r (Ok x2) in
                  let usevars = vars_in_expr_list [p] in
                  let usehigh = get_use_high_vars [p] in
                  let defcmds =
                    floc#get_vardef_commands
                      ~defs:[vrd]
                      ~use:usevars
                      ~usehigh
                      ~flagdefs
                      ctxtiaddr in
                  let brcmd =
                    match tests with
                    | Some (thentest, elsetest) ->
                       BRANCH [LF.mkCode (thentest @ cmd1);
                               LF.mkCode (elsetest @ cmd2)]
                    | _ ->
                       BRANCH [LF.mkCode cmd1; LF.mkCode cmd2] in
                  defcmds @ [brcmd]
               | _ ->
                  let _ =
                    chlog#add
                      "ternary assignment:no predicate"
                      (LBLOCK [floc#l#toPretty]) in
                  let cmds = floc#get_abstract_commands_r lhs_r in
                  let defcmds =
                    floc#get_vardef_commands ~defs:[vrd] ~flagdefs ctxtiaddr in
                  defcmds @ cmds in
             default cmds

          | _ ->
             (* should not be reachable *)
             raise
               (BCH_failure
                  (LBLOCK [floc#l#toPretty; STR ": Unknown MOV aggregate kind"])))
      | _ ->
         (* no predicate found *)
         let vrd = floc#env#mk_register_variable rd#to_register in
         let lhs_r = TR.tmap fst (rd#to_lhs floc) in
         let cmds = floc#get_abstract_commands_r lhs_r in
         let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
         let cmds = defcmds @ cmds in
         let _ =
           chlog#add
             "predicate assignment aggregate without predicate"
             (LBLOCK [loc#toPretty; STR ": "; instr#toPretty]) in
         default cmds)

  | Move _ when Option.is_some instr#is_in_aggregate ->
     default []

  (* Preempt spurious reaching definitions by vacuous assignment *)
  | Move (_, _, rd, rm, _, _)
       when rm#is_register && rd#get_register = rm#get_register ->
     default []

  | Move (_, c, rd, rm, _, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap floc#inv#rewrite_expr xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [rhs_r] in
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

  | MoveRegisterCoprocessor (c, _, _, rt, _, _, _) ->
     let vrd = floc#env#mk_register_variable rt#to_register in
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | MoveToCoprocessor _ -> default []

  (* ------------------------------------------------------------ MoveTop ---
   * R[d]<31:16> = imm16;
   * // R[d]<15:0> unchanged
   * ------------------------------------------------------------------------ *)
  | MoveTop (c, rd, imm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrd_r = rd#to_expr floc in
     let xrd_r = TR.tmap (rewrite_expr floc) xrd_r in
     let imm16_r = imm#to_expr floc in
     let ximm16_r =
       TR.tmap
         (fun imm16 -> XOp (XMult, [imm16; int_constant_expr e16])) imm16_r in
     let rhs_r = TR.tmap (fun xrd -> XOp (XXlsh, [xrd])) xrd_r in
     let rhs_r =
       TR.tmap2 (fun rhs ximm16 -> XOp (XPlus, [rhs; ximm16])) rhs_r ximm16_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rd] in
     let usehigh = get_use_high_vars_r [xrd_r] in
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

  | MoveTwoRegisterCoprocessor (c, _, _, rt, rt2, _) ->
     let lhs1_r = TR.tmap fst (rt#to_lhs floc) in
     let lhs2_r = TR.tmap fst (rt2#to_lhs floc) in
     let vrd1 = floc#env#mk_register_variable rt#to_register in
     let vrd2 = floc#env#mk_register_variable rt2#to_register in
     let cmds1 = floc#get_abstract_commands_r lhs1_r in
     let cmds2 = floc#get_abstract_commands_r lhs2_r in
     let defcmds = floc#get_vardef_commands ~defs:[vrd1; vrd2] ctxtiaddr in
     let cmds = defcmds @ cmds1 @ cmds2 in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | Multiply (_, c, rd, rn, rm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap2 (fun xrn xrm -> XOp (XMult, [xrn; xrm])) xrn_r xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let defcmds = floc#get_vardef_commands ~defs:[vrd] ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | MultiplyAccumulate (_, c, rd, rn, rm, ra) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let xra_r = ra#to_expr floc in
     let rhs_r =
       TR.tmap3 (fun xrn xrm xra ->
           XOp (XPlus, [XOp (XMult, [xrn; xrm]); xra])) xrn_r xrm_r xra_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rn; rm; ra] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r; xra_r] in
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

  | MultiplySubtract (c, rd, rn, rm, ra) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let xra_r = ra#to_expr floc in
     let rhs_r =
       TR.tmap3 (fun xrn xrm xra ->
           XOp (XMinus, [xra; XOp (XMult, [xrn; xrm])])) xrn_r xrm_r xra_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rn; rm; ra] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r; xra_r] in
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
     let is_restore_temporary (r: register_t) =
       if rl#includes_pc then
         match r with
         | ARMRegister armreg -> List.mem armreg arm_temporaries
         | _ -> false
       else
         false in
     let popcmds (): cmd_t list =
       let sprhs_r = sp#to_expr floc in
       let regs = rl#to_multiple_register in
       let (stackops, _) =
         List.fold_left
           (fun (acc, off) reg ->
             let reglhs = floc#env#mk_register_variable reg in
             let splhs = floc#env#mk_register_variable sp#to_register in
             let stackop = arm_sp_deref ~with_offset:off RD in
             let stackvar_r = stackop#to_variable floc in
             let stackrhs_r = stackop#to_expr floc in
             let cmds1 = floc#get_assign_commands_r (Ok reglhs) stackrhs_r in
             let usevars =
               TR.tfold_default (fun stackvar -> [stackvar]) [] stackvar_r in
             let usehigh =
               if is_restore_temporary reg then
                 let _ =
                   chlog#add
                     "register restore of temporary"
                     (LBLOCK [
                          floc#l#toPretty;
                          STR ": ";
                          STR (register_to_string reg);
                          STR " := ";
                          STR (x_r2s (TR.tmap (rewrite_expr floc) stackrhs_r))
                     ]) in
                 []
               else
                 get_use_high_vars_r ~is_pop:true [stackrhs_r] in
             let defcmds1 =
               floc#get_vardef_commands
                 ~defs:[reglhs; splhs]
                 ~use:usevars
                 ~usehigh:usehigh
                 ctxtiaddr in
             let _ =
               (* record register restore *)
               let rhs_r = TR.tmap (rewrite_expr floc) stackrhs_r in
               TR.tfold_default
                 (fun rhs ->
                   match rhs with
                   | XVar xvar ->
                      if floc#f#env#is_initial_register_value xvar then
                        let xreg =
                          TR.tget_ok
                            (floc#f#env#get_initial_register_value_register xvar) in
                        match (xreg, reg) with
                        | (ARMRegister r, ARMRegister g) when r = g ->
                           TR.tfold_default
                          (fun xmemaddr ->
                            let xmemaddr = floc#inv#rewrite_expr xmemaddr in
                            finfo#restore_register xmemaddr floc#cia reg)
                          ()
                          (stackop#to_address floc)
                        | (ARMRegister r, ARMRegister g)
                             when r = ARLR && g = ARPC ->
                           TR.tfold_default
                          (fun xmemaddr ->
                            let xmemaddr = floc#inv#rewrite_expr xmemaddr in
                            finfo#restore_register xmemaddr floc#cia xreg)
                          ()
                          (stackop#to_address floc)
                        | _ -> ()
                      else
                        ()
                   | _ ->
                      ())
                 ()
                 rhs_r in
             (acc @ defcmds1 @ cmds1, off+4)) ([], 0) regs in
       let splhs = floc#env#mk_register_variable (sp_r WR)#to_register in
       let increm = XConst (IntConst (mkNumerical (4 * regcount))) in
       let sprhs_r =
         TR.tmap (fun sprhs -> XOp (XPlus, [sprhs; increm])) sprhs_r in
       let popcmds = floc#get_assign_commands_r (Ok splhs) sprhs_r in
       let useshigh =
         let fsig = finfo#get_summary#get_function_signature in
         let rtype = fsig.fts_returntype in
         if rl#includes_pc then
           match rtype with
           | TVoid _ -> []
           | _ ->
              (* Return variables need to be treated somewhat differently
                 than other 'initial-value' variables, because in the
                 lifting to C code they get assigned to, while other
                 'initial-value' variables always have their values
                 and thus are by default not included in the use-high
                 variables. *)
              let r0_op = arm_register_op AR0 RD in
              let xr0_r = r0_op#to_expr floc in
              TR.tfold_default
                (fun xr0 ->
                  let xxr0 = floc#inv#rewrite_expr xr0 in
                  match xxr0 with
                  | XVar v when floc#env#is_return_value v ->
                     [floc#f#env#mk_arm_register_variable AR0]
                  | _ ->
                     get_use_high_vars_r ~is_pop:true [xr0_r])
                (get_use_high_vars_r ~is_pop:true [xr0_r])
                xr0_r
         else
           [] in
       let popdefcmds =
         floc#get_vardef_commands
           ~defs:[splhs]
           ~use:(get_register_vars [sp])
           ~usehigh:useshigh
           ctxtiaddr in
       stackops @ popdefcmds @ popcmds in

     let ccdefcmds (): cmd_t list =
       if is_cond_conditional c && finfo#has_associated_cc_setter ctxtiaddr then
         match get_associated_test_instr finfo ctxtiaddr with
         | Some (testloc, testinstr) ->
            let (_, optxpr, opsused) =
              make_conditional_predicate
                ~condinstr: instr
                ~testinstr: testinstr
                ~condloc:loc
                ~testloc in
            let use = get_register_vars opsused in
            let usehigh = match optxpr with
              | Some xpr -> get_use_high_vars [xpr]
              | _ -> [] in
            floc#get_vardef_commands ~use ~usehigh ctxtiaddr
         | _ ->
            []
       else
         [] in

     if is_cond_conditional c && rl#includes_pc then
       let ccvardefs = ccdefcmds () in

       let thenaddr =
         if (List.length codepc#get_block_successors) = 2 then
           (* this instruction is part of an inlined function; control flow
              is returned to the main function *)
           let _ =
             chlog#add
               "conditional return in inlined function"
               (LBLOCK [
                    floc#l#toPretty;
                    STR "  ";
                    STR codepc#get_true_branch_successor]) in
           codepc#get_true_branch_successor
         else
           (* this instruction is a genuine return instruction *)
           "exit" in

       let elseaddr = codepc#get_false_branch_successor in

       (* collect all previous commands in the block and the invariant anchor
          and package them together with the vardef commands in a transaction *)
       let cmds = cmds @ (invop :: ccvardefs) in
       let transaction = package_transaction finfo blocklabel cmds in

       (* create the branches according to the condition *)
       (match get_associated_test_instr finfo ctxtiaddr with
        | Some (testloc, testinstr) ->
           let (nodes, edges) =
             make_condition
               ~thencode:(popcmds ())
               ~condinstr:instr
               ~testinstr:testinstr
               ~condloc:loc
               ~testloc
               ~blocklabel
               ~thenaddr
               ~elseaddr () in
           ((blocklabel, [transaction]) :: nodes, edges, [])
        | _ ->
           let (poplabel, popnode) =
             let label = make_code_label ~modifier:"pop" thenaddr in
             let transaction = TRANSACTION (label, LF.mkCode (popcmds ()), None) in
             (label, [transaction]) in
           let thenlabel = make_code_label thenaddr in
           let elselabel = make_code_label elseaddr in
           let nodes = [(blocklabel, [transaction]); (poplabel, popnode)] in
           let edges = [
               (blocklabel, poplabel);
               (poplabel, thenlabel);
               (blocklabel, elselabel)] in
           (nodes, edges, []))

     else
       (* regular, unconditional Pop, or conditional pop without pc *)
       let cmds = popcmds () in
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
     let regcount = rl#get_register_count in
     let sprhs_r = sp#to_expr floc in
     let rhsvars_rl = rl#to_multiple_variable floc in
     let (stackops, _) =
       List.fold_left
         (fun (acc, off) rhsvar_r ->
           let cmds =
             TR.tfold
               ~ok:(fun rhsvar ->
                 let rhsreg = TR.tget_ok (finfo#env#get_register rhsvar) in
                 let stackop = arm_sp_deref ~with_offset:off WR in
                 TR.tfold
                   ~ok:(fun (stacklhs, stacklhscmds) ->
                     let _ =
                       if floc#has_initial_value rhsvar then
                         finfo#save_register stacklhs floc#cia rhsreg in
                     let rhsexpr = rewrite_expr floc (XVar rhsvar) in
                     let cmds1 = floc#get_assign_commands stacklhs rhsexpr in
                     let usehigh = get_use_high_vars [rhsexpr] in
                     let defcmds1 =
                       floc#get_vardef_commands
                         ~defs:[stacklhs]
                         ~use:[rhsvar]
                         ~usehigh
                         ctxtiaddr in
                   stacklhscmds @ defcmds1 @ cmds1)
                   ~error:(fun e ->
                     begin
                       log_dc_error_result __FILE__ __LINE__ e;
                       []
                     end)
                   (stackop#to_lhs floc))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   []
                 end)
               rhsvar_r in
           (acc @ cmds, off + 4)) ([], (- (4 * regcount))) rhsvars_rl in

     let splhs = floc#env#mk_register_variable (sp_r WR)#to_register in
     let decrem = XConst (IntConst (mkNumerical(4 * regcount))) in
     let sprhs_r = TR.tmap (fun sprhs -> XOp (XMinus, [sprhs; decrem])) sprhs_r in
     let cmds = floc#get_assign_commands_r (Ok splhs) sprhs_r in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap2 (fun xrn xrm -> XOp (XMinus, [xrm; xrn])) xrn_r xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap2 (fun xrn xrm -> XOp (XMinus, [xrm; xrn])) xrn_r xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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

  | RotateRight (_, c, rd, rn, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn] in
     let usehigh = get_use_high_vars_r [xrn_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap2 (fun xrn xrm -> XOp (XDiv, [xrn; xrm])) xrn_r xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let xrn_r = rn#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rm; rn] in
     let usehigh = get_use_high_vars_r [xrm_r; xrn_r] in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let xra_r = ra#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm; ra] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r; xra_r] in
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

  | SignedMultiplyLong (_, c, rdlo, rdhi, rn, rm) ->
     let vlo = floc#env#mk_register_variable rdlo#to_register in
     let vhi = floc#env#mk_register_variable rdhi#to_register in
     let lhslo_r = TR.tmap fst (rdlo#to_lhs floc) in
     let lhshi_r = TR.tmap fst (rdhi#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmdslo = floc#get_abstract_commands_r lhslo_r in
     let cmdshi = floc#get_abstract_commands_r lhshi_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vlo; vhi]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmdslo @ cmdshi in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SignedMultiplyWordB (c, rd, rn, rm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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

  | SignedMultiplyWordT (c, rd, rn, rm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
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
     let basereg = base#get_register in
     let regcount = rl#get_register_count in
     let rhsvars_rl = rl#to_multiple_variable floc in
     let (memassigns, _) =
       List.fold_left
         (fun (acc, off) rhsvar_r ->
           let cmds =
             TR.tfold
               ~ok:(fun rhsvar ->
                 let memop = arm_reg_deref ~with_offset:off basereg WR in
                 TR.tfold
                   ~ok:(fun (memlhs, memlhscmds) ->
                     let rhsexpr = rewrite_expr floc (XVar rhsvar) in
                     let cmds1 = floc#get_assign_commands memlhs rhsexpr in
                     let usehigh = get_use_high_vars [rhsexpr] in
                     let defcmds1 =
                       floc#get_vardef_commands
                         ~defs:[memlhs]
                         ~use:[rhsvar]
                         ~usehigh
                         ctxtiaddr in
                     memlhscmds @ defcmds1 @ cmds1)
                   ~error:(fun e ->
                     begin
                       log_dc_error_result __FILE__ __LINE__ e;
                       []
                     end)
                   (memop#to_lhs floc))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   []
                 end)
               rhsvar_r in
           (acc @ cmds, off + 4)) ([], 0) rhsvars_rl in

     let wbackassign =
       if wback then
         let lhs = floc#env#mk_register_variable base#to_register in
         let rhs_r = base#to_expr floc in
         let increm = int_constant_expr (4 * regcount) in
         let rhs_r = TR.tmap (fun rhs -> XOp (XPlus, [rhs; increm])) rhs_r in
         let wbackcmds = floc#get_assign_commands_r (Ok lhs) rhs_r in
         let wbackdefcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         wbackdefcmds @ wbackcmds
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
  | StoreMultipleIncrementBefore (wback, c, base, rl, _) ->
     let basereg = base#get_register in
     let regcount = rl#get_register_count in
     let rhsvars_rl = rl#to_multiple_variable floc in
     let (memassigns, _) =
       List.fold_left
         (fun (acc, off) rhsvar_r ->
           let cmds =
             TR.tfold
               ~ok:(fun rhsvar ->
                 let memop = arm_reg_deref ~with_offset:off basereg WR in
                 TR.tfold
                   ~ok:(fun (memlhs, memlhscmds) ->
                     let rhsexpr = rewrite_expr floc (XVar rhsvar) in
                     let cmds1 = floc#get_assign_commands memlhs rhsexpr in
                     let usehigh = get_use_high_vars [rhsexpr] in
                     let defcmds1 =
                       floc#get_vardef_commands
                         ~defs:[memlhs]
                         ~use:[rhsvar]
                         ~usehigh
                         ctxtiaddr in
                     memlhscmds @ defcmds1 @ cmds1)
                   ~error:(fun e ->
                     begin
                       log_dc_error_result __FILE__ __LINE__ e;
                       []
                     end)
                   (memop#to_lhs floc))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   []
                 end)
               rhsvar_r in
           (acc @ cmds, off + 4)) ([], 4) rhsvars_rl in

     let wbackassign =
       if wback then
         let lhs = floc#env#mk_register_variable base#to_register in
         let rhs_r = base#to_expr floc in
         let increm = int_constant_expr (4 + (4 * regcount)) in
         let rhs_r = TR.tmap (fun rhs -> XOp (XPlus, [rhs; increm])) rhs_r in
         let wbackcmds = floc#get_assign_commands_r (Ok lhs) rhs_r in
         let wbackdefcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         wbackdefcmds @ wbackcmds
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
  | StoreMultipleDecrementBefore (wback, c, base, rl, _) ->
     let basereg = base#get_register in
     let regcount = rl#get_register_count in
     let rhsvars_rl = rl#to_multiple_variable floc in
     let (memassigns, _) =
       List.fold_left
         (fun (acc, off) rhsvar_r ->
           let cmds =
             TR.tfold
               ~ok:(fun rhsvar ->
                 let memop = arm_reg_deref ~with_offset:off basereg WR in
                 TR.tfold
                   ~ok:(fun (memlhs, memlhscmds) ->
                     let rhsexpr = rewrite_expr floc (XVar rhsvar) in
                     let cmds1 = floc#get_assign_commands memlhs rhsexpr in
                     let usehigh = get_use_high_vars [rhsexpr] in
                     let defcmds1 =
                       floc#get_vardef_commands
                         ~defs:[memlhs]
                         ~use:[rhsvar]
                         ~usehigh
                         ctxtiaddr in
                     memlhscmds @ defcmds1 @ cmds1)
                   ~error:(fun e ->
                     begin
                       log_dc_error_result __FILE__ __LINE__ e;
                       []
                     end)
                   (memop#to_lhs floc))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   []
                 end)
               rhsvar_r in
           (acc @ cmds, off + 4)) ([], - (4 * regcount)) rhsvars_rl in

     let wbackassign =
       if wback then
         let lhs = floc#env#mk_register_variable base#to_register in
         let rhs_r = base#to_expr floc in
         let decrem = int_constant_expr (4 * regcount) in
         let rhs_r = TR.tmap (fun rhs -> XOp (XMinus, [rhs; decrem])) rhs_r in
         let wbackcmds = floc#get_assign_commands_r (Ok lhs) rhs_r in
         let wbackdefcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         wbackdefcmds @ wbackcmds
       else
         [] in
     let cmds = memassigns @ wbackassign in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)


  (* ------------------------------------------ StoreMultipleDecrementAfter ---
   * Stores multiple registers to consecutive memory locations using an address
   * from a base register. The consecutive memory locations end at this address,
   * and the address of the first of those locations may be written back to the
   * base register.
   *
   * address = R[n] - 4 * BitCount(registers) + 4;
   * for i = 0 to 14
   *   if registers<i> == '1' then
   *     MemA[address, 4] = R[i];
   *     address = address + 4;
   * if registers<15> == '1' then
   *   MemA[address, 4] = PCStoreValue();
   * if wback then R[n] = R[n] - 4 * BitCount(registers);
   * ------------------------------------------------------------------------ *)
  | StoreMultipleDecrementAfter (wback, c, base, rl, _) ->
     let basereg = base#get_register in
     let regcount = rl#get_register_count in
     let rhsvars_rl = rl#to_multiple_variable floc in
     let (memassigns, _) =
       List.fold_left
         (fun (acc, off) rhsvar_r ->
           let cmds =
             TR.tfold
               ~ok:(fun rhsvar ->
                 let memop = arm_reg_deref ~with_offset:off basereg WR in
                 TR.tfold
                   ~ok:(fun (memlhs, memlhscmds) ->
                     let rhsexpr = rewrite_expr floc (XVar rhsvar) in
                     let cmds1 = floc#get_assign_commands memlhs rhsexpr in
                     let usehigh = get_use_high_vars [rhsexpr] in
                     let defcmds1 =
                       floc#get_vardef_commands
                         ~defs:[memlhs]
                         ~use:[rhsvar]
                         ~usehigh
                         ctxtiaddr in
                     memlhscmds @ defcmds1 @ cmds1)
                   ~error:(fun e ->
                     begin
                       log_dc_error_result __FILE__ __LINE__ e;
                       []
                     end)
                   (memop#to_lhs floc))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   []
                 end)
               rhsvar_r in
           (acc @ cmds, off + 4)) ([], 4 - (4 * regcount)) rhsvars_rl in

     let wbackassign =
       if wback then
         let lhs = floc#env#mk_register_variable base#to_register in
         let rhs_r = base#to_expr floc in
         let decrem = int_constant_expr (4 * regcount) in
         let rhs_r = TR.tmap (fun rhs -> XOp (XMinus, [rhs; decrem])) rhs_r in
         let wbackcmds = floc#get_assign_commands_r (Ok lhs) rhs_r in
         let wbackdefcmds = floc#get_vardef_commands ~defs:[lhs] ctxtiaddr in
         wbackdefcmds @ wbackcmds
       else
         [] in
     let cmds = memassigns @ wbackassign in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegister (c, rt, rn, rm, mem, _) ->
     let xrt_r = rt#to_expr floc in
     let xrt_r = TR.tmap (floc#inv#rewrite_expr) xrt_r in
     let usevars = get_register_vars [rt; rn; rm] in
     let usehigh = get_use_high_vars_r [xrt_r] in
     let rdefcmds = floc#get_vardef_commands ~use:usevars ~usehigh ctxtiaddr in
     let cmds =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r (Ok memlhs) xrt_r in
           let memvardeps = floc#f#env#get_memvar_dependencies memlhs in
           let usehigh =
             List.filter (fun v -> not (floc#f#env#is_function_initial_value v))
               memvardeps in
           let _ =
             log_diagnostics_result
               ~msg:(p2s floc#l#toPretty)
               ~tag:"translate memlhs storeregister"
               __FILE__ __LINE__
               ["memlhs: " ^ (p2s memlhs#toPretty);
                "memvardeps: "
                ^ (String.concat
                     ", " (List.map (fun v -> p2s v#toPretty) memvardeps));
                "usehigh: "
                ^ (String.concat
                     ", " (List.map (fun v -> p2s v#toPretty) usehigh))] in
           let defcmds =
             floc#get_vardef_commands ~defs:[memlhs] ~usehigh ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           let xrn_r = rn#to_expr floc in
           let xrm_r = rm#to_expr floc in
           let usehigh = get_addr_use_high_vars_r [xrn_r; xrm_r] in
           let defcmds = floc#get_vardef_commands ~usehigh ctxtiaddr in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             defcmds
           end)
         (mem#to_lhs floc) in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let vrn = floc#env#mk_register_variable rn#to_register in
         let cmds = floc#get_assign_commands_r (Ok vrn) addr_r in
         let defcmds = floc#get_vardef_commands ~defs:[vrn] ctxtiaddr in
         defcmds @ cmds
       else
         [] in
     let cmds = cmds @ rdefcmds @ updatecmds in
     let _ =
       (* record register spill *)
       let vrt = floc#env#mk_register_variable rt#to_register in
       if floc#has_initial_value vrt then
         TR.tfold
           ~ok:(fun memlhs ->
             if finfo#env#is_local_stack_variable memlhs then
               finfo#save_register memlhs floc#cia rt#to_register)
           ~error:(fun e ->
             begin log_dc_error_result __FILE__ __LINE__ e; () end)
           (mem#to_variable floc) in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegisterByte (c, rt, rn, rm, mem, _) ->
     let xrt_r = rt#to_expr floc in
     let xrt_r = TR.tmap (floc#inv#rewrite_expr) xrt_r in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rt; rn; rm] in
     let usehigh = get_use_high_vars_r [xrt_r] in
     let rdefcmds = floc#get_vardef_commands ~use:usevars ~usehigh ctxtiaddr in
     let cmds =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r ~size:1 (Ok memlhs) xrt_r in
           let defcmds = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           let usehigh = get_addr_use_high_vars_r [xrn_r; xrm_r] in
           let defcmds = floc#get_vardef_commands ~usehigh ctxtiaddr in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             defcmds
           end)
         (mem#to_lhs floc) in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let vrn = floc#env#mk_register_variable rn#to_register in
         let cmds = floc#get_assign_commands_r (Ok vrn) addr_r in
         let defcmds = floc#get_vardef_commands ~defs:[vrn] ctxtiaddr in
         defcmds @ cmds
       else
         [] in
     let cmds = cmds @ rdefcmds @ updatecmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* --------------------------------------------------------- StoreRegisterDual
   * Calculates an address from a base register value and immediate or register
   * offset, and stores two words from two registers to memory. It can use
   * offset, post-indexed, ore pre-indexed addressing.
   *
   * offset_addr =
   *   (if immediate): if add then (R[n] + imm32) else (R[n] - imm32);
   *   (if register):  if add then (R[n] + R[m]) else (R[n] - R[m]);
   * address = if index then offset_addr else R[n];
   * MemA[address, 4] = R[t];
   * MemA[address+4, 4] = R[t2];
   * if wback then R[n] = offset_addr;
   * ------------------------------------------------------------------------- *)
  | StoreRegisterDual (c, rt, rt2,rn, rm, mem, mem2) ->
     let xrt_r = rt#to_expr floc in
     let xrt2_r = rt2#to_expr floc in
     let usevars = get_register_vars [rt; rt2; rn; rm] in
     let usehigh = get_use_high_vars_r [xrt_r; xrt2_r] in
     let rdefcmds = floc#get_vardef_commands ~use:usevars ~usehigh ctxtiaddr in
     let cmds1 =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r (Ok memlhs) xrt_r in
           let defcmds = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           let xrn_r = rn#to_expr floc in
           let xrm_r = rm#to_expr floc in
           let usehigh = get_addr_use_high_vars_r [xrn_r; xrm_r] in
           let defcmds = floc#get_vardef_commands ~usehigh ctxtiaddr in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             defcmds
           end)
         (mem#to_lhs floc) in
     let cmds2 =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r (Ok memlhs) xrt2_r in
           let defcmds = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           begin log_dc_error_result __FILE__ __LINE__ e; [] end)
         (mem2#to_lhs floc) in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let vrn = floc#env#mk_register_variable rn#to_register in
         let cmds = floc#get_assign_commands_r (Ok vrn) addr_r in
         let defcmds = floc#get_vardef_commands ~defs:[vrn] ctxtiaddr in
         defcmds @ cmds
       else
         [] in
     let cmds = cmds1 @ cmds2 @ rdefcmds @ updatecmds in
     let _ =
       (* record register spills *)
       let vrt = floc#env#mk_register_variable rt#to_register in
       let vrt2 = floc#env#mk_register_variable rt2#to_register in
       begin
         (if floc#has_initial_value vrt then
            TR.tfold
              ~ok:(fun memlhs ->
                finfo#save_register memlhs floc#cia rt#to_register)
              ~error:(fun e ->
                begin log_dc_error_result __FILE__ __LINE__ e; () end)
              (mem#to_variable floc));
         (if floc#has_initial_value vrt2 then
            TR.tfold
              ~ok:(fun memlhs ->
                finfo#save_register memlhs floc#cia rt2#to_register)
              ~error:(fun e ->
                begin log_dc_error_result __FILE__ __LINE__ e; () end)
              (mem2#to_variable floc))
       end in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegisterExclusive (c, rd, rt, rn, mem) ->
     let xrt_r = rt#to_expr floc in
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let usevars = get_register_vars [rt; rn] in
     let usehigh = get_use_high_vars_r [xrt_r] in
     let rdcmds = floc#get_abstract_commands_r lhs_r in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r (Ok memlhs) xrt_r in
           let defcmds = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           let xrn_r = rn#to_expr floc in
           let usehigh = get_addr_use_high_vars_r [xrn_r] in
           let defcmds = floc#get_vardef_commands ~usehigh ctxtiaddr in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             defcmds
           end)
         (mem#to_lhs floc) in
     let cmds = rdcmds @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | StoreRegisterHalfword (c, rt, rn, rm, mem, _) ->
     let xrt_r = rt#to_expr floc in
     let xrt_r = TR.tmap (floc#inv#rewrite_expr) xrt_r in
     let usevars = get_register_vars [rt; rn; rm] in
     let usehigh = get_use_high_vars_r [xrt_r] in
     let rdefcmds = floc#get_vardef_commands ~use:usevars ~usehigh ctxtiaddr in
     let cmds =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r ~size:2 (Ok memlhs) xrt_r in
           let defcmds = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           let xrn_r = rn#to_expr floc in
           let xrm_r = rm#to_expr floc in
           let usehigh = get_addr_use_high_vars_r [xrn_r; xrm_r] in
           let defcmds = floc#get_vardef_commands ~usehigh ctxtiaddr in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             defcmds
           end)
         (mem#to_lhs floc) in
     let updatecmds =
       if mem#is_offset_address_writeback then
         let addr_r = TR.tmap snd (mem#to_updated_offset_address floc) in
         let vrn = floc#env#mk_register_variable rn#to_register in
         let cmds = floc#get_assign_commands_r (Ok vrn) addr_r in
         let defcmds = floc#get_vardef_commands ~defs:[vrn] ctxtiaddr in
         defcmds @ cmds
       else
         [] in
     let cmds = cmds @ rdefcmds @ updatecmds in
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
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap2 (fun xrn xrm -> XOp (XMinus, [xrn; xrm])) xrn_r xrm_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | SubtractCarry(_, c, rd, rn, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrd]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds);

  (* ---------------------------------------------------------------- Swap --
   * Swaps a word between registers and memory.
   *
   * data = ZeroExtend(MemA[R[n], 4], 32)
   * MemA[R[n], 4] = R[t2];
   * R[t] = data;
   * ------------------------------------------------------------------------ *)
  | Swap (c, rt, rt2, rn, mem) ->
     let vrt = floc#env#mk_register_variable rt#to_register in
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let xrt2_r = rt2#to_expr floc in
     let memrhs_r = mem#to_expr floc in
     let cmds1 = floc#get_assign_commands_r lhs_r memrhs_r in
     let cmds2 =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r (Ok memlhs) xrt2_r in
           let defcmds = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           let usehigh = get_use_high_vars_r [xrt2_r] in
           let defs = floc#get_vardef_commands ~usehigh ctxtiaddr in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             defs
           end)
       (mem#to_lhs floc) in
     let usevars = get_register_vars [rt2; rn] in
     let usehigh = get_use_high_vars_r [memrhs_r] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrt]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     let cmds = cmds1 @ cmds2 @ defcmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* ------------------------------------------------------------ SwapByte --
   * Swaps a byte between registers and memory.
   *
   * data = ZeroExtend(MemA[R[n], 1], 32)
   * MemA[R[n], 1] = R[t2]<7:0>;
   * R[t] = data;
   * ------------------------------------------------------------------------ *)
  | SwapByte (c, rt, rt2, rn, mem) ->
     let vrt = floc#env#mk_register_variable rt#to_register in
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let xrt2_r = rt2#to_expr floc in
     let memrhs_r = mem#to_expr floc in
     let cmds1 = floc#get_assign_commands_r ~size:1 lhs_r memrhs_r in
     let cmds2 =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r ~size:1 (Ok memlhs) xrt2_r in
           let defcmds = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           let usehigh = get_use_high_vars_r [xrt2_r] in
           let defs = floc#get_vardef_commands ~usehigh ctxtiaddr in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             defs
           end)
       (mem#to_lhs floc) in
     let usevars = get_register_vars [rt2; rn] in
     let usehigh = get_use_high_vars_r [memrhs_r] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrt]
         ~use:usevars
         ~usehigh
         ctxtiaddr in
     let cmds = cmds1 @ cmds2 @ defcmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | TableBranchByte _ ->
     default cmds

  | TableBranchHalfword _ ->
     default cmds

  | Test (c, rn, rm, _) ->
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~use:usevars ~usehigh ~flagdefs ctxtiaddr in
     (match c with
      | ACCAlways -> default defcmds
      | _ -> make_conditional_commands c defcmds)

  | TestEquivalence (c, rn, rm) ->
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~use:usevars ~usehigh ~flagdefs ctxtiaddr in
     (match c with
      | ACCAlways -> default defcmds
      | _ -> make_conditional_commands c defcmds)

  | UnsignedAdd8 (c, rd, rn, rm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedBitFieldExtract (c, rd, rn) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn] in
     let usehigh = get_use_high_vars_r [xrn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedDivide (c, rd, rn, rm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedExtendAddByte (c, rd, rn, rm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedExtendAddHalfword (c, rd, rn, rm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedExtendByte (c, rd, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap (fun xrm -> XOp (XXlsb, [xrm])) xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedExtendHalfword (c, rd, rm, _) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrm_r = rm#to_expr floc in
     let rhs_r = TR.tmap (fun xrm -> XOp (XXlsh, [xrm])) xrm_r in
     let cmds = floc#get_assign_commands_r lhs_r rhs_r in
     let usevars = get_register_vars [rm] in
     let usehigh = get_use_high_vars_r [xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = cmds @ defcmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedMultiplyAccumulateLong (_, c, rdlo, rdhi, rn, rm) ->
     let vrlo = floc#env#mk_register_variable rdlo#to_register in
     let vrhi = floc#env#mk_register_variable rdhi#to_register in
     let lhslo_r = TR.tmap fst (rdlo#to_lhs floc) in
     let lhshi_r = TR.tmap fst (rdhi#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let xrdlo_r = rdlo#to_expr floc in
     let xrdhi_r = rdhi#to_expr floc in
     let cmdslo = floc#get_abstract_commands_r lhslo_r in
     let cmdshi = floc#get_abstract_commands_r lhshi_r in
     let usevars = get_register_vars [rn; rm; rdlo; rdhi] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r; xrdlo_r; xrdhi_r] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrlo; vrhi] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmdslo @ cmdshi in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedMultiplyLong (_, c, rdlo, rdhi, rn, rm) ->
     let vrlo = floc#env#mk_register_variable rdlo#to_register in
     let vrhi = floc#env#mk_register_variable rdhi#to_register in
     let lhslo_r = TR.tmap fst (rdlo#to_lhs floc) in
     let lhshi_r = TR.tmap fst (rdhi#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmdslo = floc#get_abstract_commands_r lhslo_r in
     let cmdshi = floc#get_abstract_commands_r lhshi_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vrlo; vrhi] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmdslo @ cmdshi in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedSaturate (c, rd, _, rn) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn] in
     let usehigh = get_use_high_vars_r [xrn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | UnsignedSaturatingSubtract8 (c, rd, rn, rm) ->
     let vrd = floc#env#mk_register_variable rd#to_register in
     let lhs_r = TR.tmap fst (rd#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let xrm_r = rm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [rn; rm] in
     let usehigh = get_use_high_vars_r [xrn_r; xrm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorAbsolute (c, _, qd, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qm] in
     let usehigh = get_use_high_vars_r [xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorAdd (c, _, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorAddLong (c, _, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorAddWide (c, _, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorBitwiseAnd (c, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorBitwiseBitClear (c, _, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorBitwiseExclusiveOr (c, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorBitwiseNot (c, _, qd, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qm] in
     let usehigh = get_use_high_vars_r [xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorBitwiseOr (c, _, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorBitwiseOrNot (c, _, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  (* NEON instruction *)
  | VectorBitwiseSelect (c, _, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VCompare (_, _, _, fdst, dd, dm) ->
     let xdd_r = dd#to_expr floc in
     let xdm_r = dm#to_expr floc in
     let fpscr_def = floc#env#mk_register_variable fdst#to_register in
     let usevars = get_register_vars [dd; dm] in
     let usehigh = get_use_high_vars_r [xdd_r; xdm_r] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[fpscr_def]
         ~use:usevars
         ~usehigh
         ~flagdefs
         ctxtiaddr in
     default defcmds

  | VectorConvert (_, _, c, _, _, dd, dm, _) ->
     let vdd = floc#env#mk_register_variable dd#to_register in
     let lhs_r = TR.tmap fst (dd#to_lhs floc) in
     let xdm_r = dm#to_expr floc in
     let cmds = floc#get_assign_commands_r lhs_r xdm_r in
     let usevars = get_register_vars [dm] in
     let usehigh = get_use_high_vars_r [xdm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vdd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VDivide (c, _dt, dd, dn, dm) ->
     let vdd = floc#env#mk_register_variable dd#to_register in
     let lhs_r = TR.tmap fst (dd#to_lhs floc) in
     let xdn_r = dn#to_expr floc in
     let xdm_r = dm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [dn; dm] in
     let usehigh = get_use_high_vars_r [xdm_r; xdn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vdd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorDuplicate _ -> default []

  | VectorMoveDS (c, _, dd, dm) ->
     let vdd = floc#env#mk_register_variable dd#to_register in
     let lhs_r = TR.tmap fst (dd#to_lhs floc) in
     let xdm_r = dm#to_expr floc in
     let cmds = floc#get_assign_commands_r lhs_r xdm_r in
     let usevars = get_register_vars [dm] in
     let usehigh = get_use_high_vars_r [xdm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vdd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorMoveDDSS (c, _, dst1, dst2, ddst, src1, src2, ssrc) ->
     let vdst1_r = dst1#to_variable floc in
     let vdst2_r = dst2#to_variable floc in
     let vddst_r = ddst#to_variable floc in
     let vdst1 = floc#env#mk_register_variable dst1#to_register in
     let vdst2 = floc#env#mk_register_variable dst2#to_register in
     let vddst = floc#env#mk_register_variable ddst#to_register in
     let xsrc1_r = src1#to_expr floc in
     let xsrc2_r = src2#to_expr floc in
     let xssrc_r = ssrc#to_expr floc in
     let usevars = get_register_vars [src1; src2; ssrc] in
     let usehigh = get_use_high_vars_r [xsrc1_r; xsrc2_r; xssrc_r] in
     let cmds1 = floc#get_abstract_commands_r vdst1_r in
     let cmds2 = floc#get_abstract_commands_r vdst2_r in
     let cmds3 = floc#get_abstract_commands_r vddst_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vdst1; vdst2; vddst] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds1 @ cmds2 @ cmds3 in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorMoveDSS (c, _, dst, src1, src2, ssrc) ->
     let vdst_r = dst#to_variable floc in
     let vdst = floc#env#mk_register_variable dst#to_register in
     let xsrc1_r = src1#to_expr floc in
     let xsrc2_r = src2#to_expr floc in
     let xssrc_r = ssrc#to_expr floc in
     let usevars = get_register_vars [src1; src2; ssrc] in
     let usehigh = get_use_high_vars_r [xsrc1_r; xsrc2_r; xssrc_r] in
     let cmds = floc#get_abstract_commands_r vdst_r in
     let defcmds =
       floc#get_vardef_commands ~defs:[vdst] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorMoveDDS (c, _, dst1, dst2, ddst, src) ->
     let vdst1_r = dst1#to_variable floc in
     let vdst2_r = dst2#to_variable floc in
     let ddst_r = ddst#to_variable floc in
     let xsrc_r = src#to_expr floc in
     let vdst1 = floc#env#mk_register_variable dst1#to_register in
     let vdst2 = floc#env#mk_register_variable dst2#to_register in
     let vddst = floc#env#mk_register_variable ddst#to_register in
     let usevars = get_register_vars [src] in
     let usehigh = get_use_high_vars_r [xsrc_r] in
     let cmds1 = floc#get_abstract_commands_r vdst1_r in
     let cmds2 = floc#get_abstract_commands_r vdst2_r in
     let cmds3 = floc#get_assign_commands_r ddst_r xsrc_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vdst1; vdst2; vddst] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds1 @ cmds2 @ cmds3 in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VLoadRegister(c, rt, rn, mem) ->
     let vrt = floc#env#mk_register_variable rt#to_register in
     let lhs_r = TR.tmap fst (rt#to_lhs floc) in
     let xrn_r = rn#to_expr floc in
     let rhs_r = mem#to_expr floc in
     let cmds = floc#get_assign_commands_r  lhs_r rhs_r in
     let usevars = get_register_vars [rn] in
     let usehigh =
       TR.tfold
         ~ok:(fun rhs -> get_use_high_vars [rhs])
         ~error:(fun e ->
           let usehigh = get_use_high_vars_r [xrn_r] in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             usehigh
           end)
         rhs_r in
     let defcmds =
       floc#get_vardef_commands ~defs:[vrt] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VMoveRegisterStatus (_, dst, src) ->
     let vdst_r = dst#to_variable floc in
     let vdst = floc#env#mk_register_variable dst#to_register in
     let xsrc_r = src#to_expr floc in
     let usevars = get_register_vars [src] in
     let usehigh = get_use_high_vars_r [xsrc_r] in
     let cmds = floc#get_abstract_commands_r vdst_r in
     let flagdefs =
       if dst#is_APSR_condition_flags then apsr_flagdefs else [] in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[vdst]
         ~flagdefs:flagdefs
         ~use:usevars
         ~usehigh:usehigh
         ctxtiaddr in
     default (defcmds @ cmds)

  | VectorMoveLong (c, _, qd, qm) ->
     let vqd_r = qd#to_variable floc in
     let vqd = floc#env#mk_register_variable qd#to_register in
     let cmds = floc#get_abstract_commands_r vqd_r in
     let usevars = get_register_vars [qm] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorMoveNarrow (c, _, qd, qm) ->
     let vqd_r = qd#to_variable floc in
     let vqd = floc#env#mk_register_variable qd#to_register in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vqd_r in
     let usevars = get_register_vars [qm] in
     let usehigh = get_use_high_vars_r [xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorMultiply (c, _, qd, qn, qm) ->
     let vqd_r = qd#to_variable floc in
     let vqd = floc#env#mk_register_variable qd#to_register in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vqd_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqn_r; xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorMultiplyAccumulateLong (c, _, qd, qn, qm) ->
     let vqd_r = qd#to_variable floc in
     let vqd = floc#env#mk_register_variable qd#to_register in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vqd_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqn_r; xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorMultiplyLong (c, _, qd, qn, qm) ->
     let vqd_r = qd#to_variable floc in
     let vqd = floc#env#mk_register_variable qd#to_register in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vqd_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqn_r; xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorMultiplySubtract (c, _, qd, qn, qm) ->
     let vqd_r = qd#to_variable floc in
     let vqd = floc#env#mk_register_variable qd#to_register in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vqd_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqn_r; xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorNegate (c, _, qd, qm) ->
     let vqd_r = qd#to_variable floc in
     let vqd = floc#env#mk_register_variable qd#to_register in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vqd_r in
     let usevars = get_register_vars [qm] in
     let usehigh = get_use_high_vars_r [xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorNegateMultiply (c, _, dd, dn, dm) ->
     let vdd_r = dd#to_variable floc in
     let vdd = floc#env#mk_register_variable dd#to_register in
     let xdn_r = dn#to_expr floc in
     let xdm_r = dm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vdd_r in
     let usevars = get_register_vars [dn; dm] in
     let usehigh = get_use_high_vars_r [xdn_r; xdm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vdd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorNegateMultiplyAccumulate (c, _, dd, dn, dm) ->
     let vdd_r = dd#to_variable floc in
     let vdd = floc#env#mk_register_variable dd#to_register in
     let xdn_r = dn#to_expr floc in
     let xdm_r = dm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vdd_r in
     let usevars = get_register_vars [dn; dm] in
     let usehigh = get_use_high_vars_r [xdn_r; xdm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vdd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorNegateMultiplySubtract (c, _, dd, dn, dm) ->
     let vdd_r = dd#to_variable floc in
     let vdd = floc#env#mk_register_variable dd#to_register in
     let xdn_r = dn#to_expr floc in
     let xdm_r = dm#to_expr floc in
     let cmds = floc#get_abstract_commands_r vdd_r in
     let usevars = get_register_vars [dn; dm] in
     let usehigh = get_use_high_vars_r [xdn_r; xdm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vdd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorPop (c, sp, rl, _) ->
     let regcount =rl#get_register_count in
     let regsize =
       if rl#is_double_extension_register_list then 8 else 4 in
     let regs = rl#to_multiple_register in
     let (stackops, _) =
       List.fold_left
         (fun (acc, off) reg ->
           let reglhs = floc#env#mk_register_variable reg in
           let splhs = floc#env#mk_register_variable sp#to_register in
           let stackop = arm_sp_deref ~with_offset:off RD in
           let stackvar_r = stackop#to_variable floc in
           let stackrhs_r = stackop#to_expr floc in
           let cmds1 = floc#get_assign_commands_r (Ok reglhs) stackrhs_r in
           let usevars =
             TR.tfold_default (fun stackvar -> [stackvar]) [] stackvar_r in
           let usehigh = get_use_high_vars_r ~is_pop:true [stackrhs_r] in
           let defcmds1 =
             floc#get_vardef_commands
               ~defs:[splhs; reglhs] ~use:usevars ~usehigh ctxtiaddr in
           (acc @ defcmds1 @ cmds1, off + regsize)) ([], 0) regs in
     let splhs = floc#env#mk_register_variable (sp_r WR)#to_register in
     let increm = XConst (IntConst (mkNumerical (regsize * regcount))) in
     let sprhs_r =
       TR.tmap (fun sprhs -> XOp (XPlus, [sprhs; increm])) (sp#to_expr floc) in
     let cmds = floc#get_assign_commands_r (Ok splhs) sprhs_r in
     let usevars = get_register_vars [sp] in
     let defcmds =
       floc#get_vardef_commands ~defs:[splhs] ~use:usevars ctxtiaddr in
     let cmds = stackops @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorPush (c, sp, rl, _) ->
     let regcount = rl#get_register_count in
     let regsize =
       if rl#is_double_extension_register_list then 8 else 4 in
     let sprhs_r = sp#to_expr floc in
     let rhsvars_rl = rl#to_multiple_variable floc in
     let (stackops, _) =
       List.fold_left
         (fun (acc, off) rhsvar_r ->
           let cmds =
             TR.tfold
               ~ok:(fun rhsvar ->
                 let stackop = arm_sp_deref ~with_offset:off WR in
                 TR.tfold
                   ~ok:(fun (stacklhs, stacklhscmds) ->
                     let rhsexpr = rewrite_expr floc (XVar rhsvar) in
                     let cmds1 = floc#get_assign_commands stacklhs rhsexpr in
                     let usehigh = get_use_high_vars [rhsexpr] in
                     let defcmds1 =
                       floc#get_vardef_commands
                         ~defs:[stacklhs]
                         ~use:[rhsvar]
                         ~usehigh
                         ctxtiaddr in
                   stacklhscmds @ defcmds1 @ cmds1)
                   ~error:(fun e ->
                     begin
                       log_dc_error_result __FILE__ __LINE__ e;
                       []
                     end)
                   (stackop#to_lhs floc))
               ~error:(fun e ->
                 begin
                   log_dc_error_result __FILE__ __LINE__ e;
                   []
                 end)
               rhsvar_r in
           (acc @ cmds, off + regsize))
         ([], (- (regsize * regcount))) rhsvars_rl in

     let splhs = floc#env#mk_register_variable (sp_r WR)#to_register in
     let decrem = XConst (IntConst (mkNumerical (regsize * regcount))) in
     let sprhs_r = TR.tmap (fun sprhs -> XOp (XMinus, [sprhs; decrem])) sprhs_r in
     let cmds = floc#get_assign_commands_r (Ok splhs) sprhs_r in
     let defcmds =
       floc#get_vardef_commands
         ~defs:[splhs]
         ~use:(get_register_vars [sp])
         ctxtiaddr in
     let cmds = stackops @ defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorReverseDoublewords (c, _, qd, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qm] in
     let usehigh = get_use_high_vars_r [xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorReverseHalfwords (c, _, qd, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qm] in
     let usehigh = get_use_high_vars_r [xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorReverseWords (c, _, qd, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qm] in
     let usehigh = get_use_high_vars_r [xqm_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorShiftRightNarrow _ -> default []

  | VStoreRegister(c, dd, rn, mem) ->
     let xdd_r = dd#to_expr floc in
     let xrn_r = rn#to_expr floc in
     let xrn_r = TR.tmap (rewrite_expr floc) xrn_r in
     let usevars = get_register_vars [dd; rn] in
     let usehigh = get_use_high_vars_r [xdd_r] in
     let rdefcmds = floc#get_vardef_commands ~use:usevars ~usehigh ctxtiaddr in
     let cmds =
       TR.tfold
         ~ok:(fun (memlhs, memcmds) ->
           let cmds = floc#get_assign_commands_r (Ok memlhs) xdd_r in
           let defcmds = floc#get_vardef_commands ~defs:[memlhs] ctxtiaddr in
           memcmds @ cmds @ defcmds)
         ~error:(fun e ->
           let usehigh = get_use_high_vars_r [xrn_r] in
           let defcmds = floc#get_vardef_commands ~usehigh ctxtiaddr in
           begin
             log_dc_error_result __FILE__ __LINE__ e;
             defcmds
           end)
         (mem#to_lhs floc) in
     let cmds = rdefcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorSubtract (c, _, qd, qn, qm) ->
     let vqd = floc#env#mk_register_variable qd#to_register in
     let lhs_r = TR.tmap fst (qd#to_lhs floc) in
     let xqn_r = qn#to_expr floc in
     let xqm_r = qm#to_expr floc in
     let cmds = floc#get_abstract_commands_r lhs_r in
     let usevars = get_register_vars [qn; qm] in
     let usehigh = get_use_high_vars_r [xqm_r; xqn_r] in
     let defcmds =
       floc#get_vardef_commands ~defs:[vqd] ~use:usevars ~usehigh ctxtiaddr in
     let cmds = defcmds @ cmds in
     (match c with
      | ACCAlways -> default cmds
      | _ -> make_conditional_commands c cmds)

  | VectorTranspose _ -> default []

  | NotRecognized (desc, dw) ->
     begin
       log_error_result
         ~msg:"instruction not recognized"
         __FILE__ __LINE__
         [(p2s floc#l#toPretty);
          (p2s dw#toPretty) ^ ":" ^ desc];
       default []
     end

  | instr ->
     begin
       log_error_result
         ~msg:"no instruction semantics"
         __FILE__ __LINE__
         [(p2s floc#l#toPretty); (arm_opcode_to_string instr)];
       default []
     end

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
          translate_arm_instruction ~funloc ~codepc ~blocklabel ~cmds
        with
        | BCH_failure p ->
           let msg =
             LBLOCK [
                 STR "function: ";
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
    log_tfold
      (log_error "create_arg_deref_asserts" "invalid base variable")
      ~ok:(fun rbase ->
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
        | _ -> [])
      ~error:(fun _ -> [])
      (env#mk_base_variable_reference ri)

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
      let namedw =
        fail_tvalue
          (trerror_record
             (LBLOCK [STR "create_arg_asserts: "; STR name]))
          (string_to_doubleword name) in
      let loc = BCHLocation.make_location_by_address finfo#a finfo#a in
      let gv = TR.tget_ok (finfo#env#mk_global_variable loc namedw#to_numerical) in
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
      ASSERT (EQ (regVar, initVar)) in
    let freeze_initial_extension_register_values (reg: arm_extension_register_t) =
      let regVar = env#mk_arm_extension_register_variable reg in
      let initVar = env#mk_initial_register_value (ARMExtensionRegister reg) in
      ASSERT (EQ (regVar, initVar)) in
    let freeze_external_memory_values (v:variable_t) =
      TR.tfold
        ~ok:(fun initVar -> ASSERT (EQ (v, initVar)))
        ~error:(fun e ->
          begin
            log_error_result __FILE__ __LINE__ e;
            SKIP
          end)
        (env#mk_initial_memory_value v) in
    let rAsserts = List.map freeze_initial_register_value arm_regular_registers in
    let xAsserts =
      let xregsused =
        env#get_selected_variables env#varmgr#is_arm_extension_register_variable in
      if (List.length xregsused) > 0 then
        List.map freeze_initial_extension_register_values
          (arm_xsingle_extension_registers @ arm_xdouble_extension_registers)
      else
        [] in
    let externalMemvars = env#get_external_memory_variables in
    let externalMemvars = List.filter env#has_constant_offset externalMemvars in
    let _ =
      if collect_diagnostics () then
        ch_diagnostics_log#add
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
      @ xAsserts
      @ mAsserts
      @ [initializeScalar]
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
              log_tfold
                (log_error "get_exit_cmd" "invalid symbolic variable")
                ~ok:(fun numvar ->
                  not (finfo#env#is_register_variable numvar
                       || finfo#env#is_local_variable numvar))
                ~error:(fun _ -> false)
                (finfo#env#get_symbolic_num_variable v)
            else
              false) symvars in
      List.map (fun v ->
          DOMAIN_OPERATION
            (["defusehigh"],
             {op_name = new symbol_t ~atts:["exit"] "use_high";
              op_args = [("dst", v, WRITE)]})) symvars in
    let exitname = new symbol_t ~atts:["exit"] "invariant" in
    let cmdinvop = OPERATION {op_name = exitname; op_args = []} in
    let constantAssigns = env#end_transaction in
    let cmds = constantAssigns @ [cmdinvop] @ cmds @ cmdshigh in
    let returnvar = finfo#env#mk_arm_register_variable AR0 in
    let _ = finfo#add_use_loc returnvar "exit" in
    let _ = finfo#add_use_high_loc returnvar "exit" in
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
    let proc = LF.mkProcedure procname ~signature:[] ~bindings:[] ~scope ~body in
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

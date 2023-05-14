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
open BCHVariableType

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

let get_invariant_label (loc:location_int) =
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
    [ (blocklabel, thentestlabel); (thentestlabel, thensucclabel) ] in
  let elseedges =
    [ (blocklabel, elsetestlabel); (elsetestlabel, elsesucclabel) ] in
  ([ (thentestlabel, thennode); (elsetestlabel, elsenode) ], thenedges @ elseedges )
  

let translate_mips_instruction
      ~(funloc:location_int)      
      ~(codepc:mips_code_pc_int)
      ~(blocklabel:symbol_t)
      ~(exitlabel:symbol_t)
      ~(cmds:cmd_t list) =                            (* commands carried over *)
  let (ctxtiaddr,instr) = codepc#get_next_instruction in
  let faddr = funloc#f in
  let loc = ctxt_string_to_location faddr ctxtiaddr in  (* instruction location *)
  let finfo = get_function_info faddr in
  let env = finfo#env in                       (* function variable environment *)
  let invlabel = get_invariant_label loc in
  let invop = OPERATION { op_name = invlabel ; op_args = [] } in
  let frozenasserts =
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
  let default newcmds = ([],[], cmds @ frozenasserts @ (invop :: newcmds)) in
  match instr#get_opcode with
  | Add (dst,src1,src2) ->
     let floc = get_floc loc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs (XOp (XPlus, [rhs1; rhs2])) in
     default (lhscmds @ cmds)
     
  | AddImmediate (dst,src,imm) ->
     let floc = get_floc loc in
     let rhs1 = src#to_expr floc in
     let rhs2 = imm#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs (XOp (XPlus, [ rhs1 ; rhs2 ])) in
     default (lhscmds @ cmds)
     
  | AddImmediateUnsigned (dst,src,imm) ->
     let floc = get_floc loc in
     let rhs1 = src#to_expr floc in
     let rhs2 = imm#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs  (XOp (XPlus, [ rhs1 ; rhs2 ])) in
     default (lhscmds @ cmds)

  | AddUpperImmediate (dst,src,imm) ->
     let floc = get_floc loc in
     let rhs1 = src#to_expr floc in
     let rhs2 = num_constant_expr (imm#to_numerical#mult (mkNumerical (256 * 256))) in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs (XOp (XPlus, [ rhs1 ; rhs2 ])) in
     default (lhscmds @ cmds)

  | AddUnsigned (dst,src1,src2) ->
     let floc = get_floc loc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs (XOp (XPlus, [ rhs1 ; rhs2 ])) in
     default (lhscmds @ cmds)

  | CountLeadingZeros (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)
     
  | And (dst,src1,src2) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let result = XOp (XBAnd, [rhs1; rhs2]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | AndImmediate (dst,src,imm) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src#to_expr floc in
     let rhs2 = imm#to_expr floc in
     let result = XOp (XBAnd, [rhs1; rhs2]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | ControlWordFromFP (rt,fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rt#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | DivideWord (hi,lo,rs,rt) ->
     let floc = get_floc loc in
     let (lhs1,lhs1cmds) = hi#to_lhs floc in
     let (lhs2,lhs2cmds) = lo#to_lhs floc in
     let rhs1 = rs#to_expr floc in
     let rhs2 = rt#to_expr floc in
     let result = XOp (XDiv, [rhs1; rhs2]) in
     let cmds1 = floc#get_abstract_commands lhs1 () in
     let cmds2 = floc#get_assign_commands lhs2 result in
     default (lhs1cmds @ lhs2cmds @ cmds1 @ cmds2)

  | DivideUnsignedWord (hi,lo,rs,rt) ->
     let floc = get_floc loc in
     let (lhs1,lhs1cmds) = hi#to_lhs floc in
     let (lhs2,lhs2cmds) = lo#to_lhs floc in
     let rhs1 = rs#to_expr floc in
     let rhs2 = rt#to_expr floc in
     let result = XOp (XDiv, [rhs1; rhs2]) in
     let cmds1 = floc#get_abstract_commands lhs1 () in
     let cmds2 = floc#get_assign_commands lhs2 result in
     default (lhs1cmds @ lhs2cmds @ cmds1 @ cmds2)

  | ExtractBitField (dst,src,pos,size) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | InsertBitField (dst,src,pos,size) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPAbsfmt (fmt,fd,fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)
     
  | FPAddfmt (fmt,fd,fs,ft) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPDivfmt (fmd,fd,fs,ft) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPMovfmt (fmt,fd,fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let rhs = fs#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | FPMulfmt (fmt,fd,fs,ft) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPSqrtfmt (fmt,fd,fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | FPSubfmt (fmt,fd,fs,ft) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fd#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | LoadByte (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | LoadByteUnsigned (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | LoadDoublewordToFP (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | LoadHalfWord (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | LoadHalfWordUnsigned (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | LoadImmediate (dst,imm) ->
     let floc = get_floc loc in
     let rhs = imm#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | LoadUpperImmediate (dst,imm)  ->
     let floc = get_floc loc in
     let rhs = num_constant_expr (imm#to_numerical#mult (mkNumerical (256 * 256))) in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)
     
  | LoadWord (dst,src) ->
     let floc = get_floc loc in
     let rhs = floc#inv#rewrite_expr (src#to_expr floc) floc#env#get_variable_comparator in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     let _ =
       if dst#is_register then
         match rhs with
         | XVar rhsvar ->
            if env#is_initial_register_value rhsvar then
              match env#get_initial_register_value_register rhsvar with
              | MIPSRegister r when r = dst#get_register ->
                 finfo#restore_register floc#cia (MIPSRegister dst#get_register)
              | _ -> ()
            else ()
         | _ -> () in
     default (lhscmds @ cmds)

  | LoadLinkedWord (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | LoadWordFP (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | LoadWordLeft (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | LoadWordRight (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MoveConditionalNotZero (dst,src,cond) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let testxpr = cond#to_expr floc in
     let testxpr = XOp (XNe, [ testxpr; zero_constant_expr ]) in
     let cmds = floc#get_conditional_assign_commands testxpr lhs rhs in
     default (lhscmds @ cmds)

  | MoveConditionalZero (dst,src,cond) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let testxpr = cond#to_expr floc in
     let testxpr = XOp (XEq, [ testxpr; zero_constant_expr ]) in
     let cmds = floc#get_conditional_assign_commands testxpr lhs rhs in
     default (lhscmds @ cmds)

  | MovF (cc,dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MovT (cc,dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | Move (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs = src#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | MoveFromHi (rd,hi) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs = hi#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | MoveToHi (hi,rs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = hi#to_lhs floc in
     let rhs = rs#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | MoveFromLo (rd,lo) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs = lo#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | MoveToLo (lo,rs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = lo#to_lhs floc in
     let rhs = rs#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | MoveWordFromFP (rt,fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rt#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MoveWordFromHighHalfFP (rt,fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rt#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MoveWordToHighHalfFP (rt,fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fs#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MoveWordToFP (rt,fs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = fs#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MoveFromCoprocessor0 (dst,_,_) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MoveToCoprocessor0 _ -> default []

  | MoveFromHighCoprocessor0 (dst,_,_) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MoveToHighCoprocessor0 _ -> default []

  | MoveWordFromCoprocessor2 (dst,_,_) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MoveWordToCoprocessor2 _ -> default []

  | MoveWordFromHighHalfCoprocessor2 (dst,_,_) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | MultiplyWord (hi,lo,rs,rt) ->
     let floc = get_floc loc in
     let (lhs1,lhs1cmds) = hi#to_lhs floc in
     let (lhs2,lhs2cmds) = lo#to_lhs floc in
     let rhs1 = rs#to_expr floc in
     let rhs2 = rt#to_expr floc in
     let xpr = XOp (XMult, [rhs1; rhs2]) in
     let cmd1 = floc#get_assign_commands lhs2 xpr in
     let cmd2 = floc#get_abstract_commands lhs1 () in
     default (lhs1cmds @ lhs2cmds @ cmd1 @ cmd2 )

  | MultiplyAddWord (hi,lo,rs,rt) ->
     let floc = get_floc loc in
     let (lhs1,lhs1cmds) = hi#to_lhs floc in
     let (lhs2,lhs2cmds) = lo#to_lhs floc in
     let rhs1 = rs#to_expr floc in
     let rhs2 = rt#to_expr floc in
     let rhslo = lo#to_expr floc in
     let xpr = XOp (XPlus, [rhslo; XOp (XMult, [rhs1; rhs2])])  in
     let cmd1 = floc#get_assign_commands lhs2 xpr in
     let cmd2 = floc#get_abstract_commands lhs1 () in
     default (lhs1cmds @ lhs2cmds @ cmd1 @ cmd2 )

  | MultiplyAddUnsignedWord (hi,lo,rs,rt) ->
     let floc = get_floc loc in
     let (lhs1,lhs1cmds) = hi#to_lhs floc in
     let (lhs2,lhs2cmds) = lo#to_lhs floc in
     let rhs1 = rs#to_expr floc in
     let rhs2 = rt#to_expr floc in
     let rhslo = lo#to_expr floc in
     let xpr = XOp (XPlus, [rhslo; XOp (XMult, [rhs1; rhs2])]) in
     let cmd1 = floc#get_assign_commands lhs2 xpr in
     let cmd2 = floc#get_abstract_commands lhs1 () in
     default (lhs1cmds @ lhs2cmds @ cmd1 @ cmd2)

  | MultiplyWordToGPR (rd,rs,rt) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs1 = rs#to_expr floc in
     let rhs2 = rt#to_expr floc in
     let result = XOp (XMult, [rhs1; rhs2]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | MultiplyUnsignedWord (hi,lo,rs,rt) ->
     let floc = get_floc loc in
     let (lhs1,lhs1cmds) = hi#to_lhs floc in
     let (lhs2,lhs2cmds) = lo#to_lhs floc in
     let rhs1 = rs#to_expr floc in
     let rhs2 = rt#to_expr floc in
     let result = XOp (XMult, [rhs1; rhs2]) in
     let cmd1 = floc#get_abstract_commands lhs1 () in
     let cmd2 = floc#get_assign_commands lhs2 result in
     default (lhs1cmds @ lhs2cmds @ cmd1 @ cmd2 )

  | Nor (rd,rs,rt) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs1 = rs#to_expr floc in
     let rhs2 = rt#to_expr floc in
     let result = XOp (XBNor, [rhs1; rhs2]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | Or (dst,src1,src2) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let result = XOp (XBOr, [rhs1; rhs2])  in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | OrImmediate (dst,src,imm) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src#to_expr floc in
     let rhs2 = imm#to_expr floc in
     let result = XOp (XBOr, [rhs1 ;rhs2]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | Prefetch _ -> default []

  | ReadHardwareRegister (dst,index) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | SetLT (dst,src1,src2) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let result = XOp (XLt, [ rhs1 ; rhs2 ]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)
     
  | SetLTImmediate (dst,src1,src2) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let result = XOp (XLt, [ rhs1 ; rhs2 ]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | SetLTImmediateUnsigned (dst,src1,src2) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let result = XOp (XLt, [ rhs1 ; rhs2 ]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | SetLTUnsigned (dst,src1,src2) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let result = XOp (XLt, [ rhs1 ; rhs2 ]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)
     
  | ShiftLeftLogical (dst,src,imm) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs = src#to_expr floc in
     (match imm#to_expr floc with
      | XConst (IntConst n) ->
         let m = get_multiplier n in
         let result = XOp (XMult, [ rhs ; m ]) in
         let cmds = floc#get_assign_commands lhs result in
         default (lhscmds @ cmds)
      | _ ->
         raise (BCH_failure
                  (LBLOCK [ STR "Unexpected operand in ShiftLeftLogical: " ;
                            imm#toPretty ])))

  | ShiftLeftLogicalVariable (rd, rt, rs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs1 = rt#to_expr floc in
     let rhs2 = rs#to_expr floc in
     let cmds =
       (match rhs1 with
        | XConst (IntConst n) when n#equal numerical_one ->
           let result = XOp (XPow, [ int_constant_expr 2 ; rhs2 ]) in
           floc#get_assign_commands lhs result
        | _ ->
           let result = XOp (XLsl, [rhs1; rhs2]) in
           floc#get_assign_commands lhs result) in
     default (lhscmds @ cmds)

  | ShiftRightLogical (dst, src, imm) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src#to_expr floc in
     let rhs2 = imm#to_expr floc in
     let cmds =
       match rhs2 with
       | XConst (IntConst n) when n#toInt = 31 ->
          (match rewrite_expr floc rhs1 with
           | XOp (XBNor, [x1; x2]) when is_zero x1 ->
              floc#get_assign_commands lhs (XOp (XGe, [x2; x1]))
           | XOp (XBNor, [x1; x2]) when is_zero x2 ->
              floc#get_assign_commands lhs (XOp (XGe, [x1; x2]))
           | _ ->
              let result = XOp (XGe, [rhs1; zero_constant_expr]) in
              floc#get_assign_commands lhs result)
       | _ ->
          let result = XOp (XLsr, [rhs1; rhs2]) in
          floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | ShiftRightLogicalVariable (rd, rt, rs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs1 = rt#to_expr floc in
     let rhs2 = rs#to_expr floc in
     let result = XOp (XLsr, [rhs1; rhs2]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | ShiftRightArithmetic (dst, src, imm) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs = src#to_expr floc in
     (match imm#to_expr floc with
      | XConst (IntConst n) ->
         let m = get_multiplier n in
         let result = XOp (XDiv, [rhs; m]) in
         let cmds = floc#get_assign_commands lhs result in
         default (lhscmds @ cmds)
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Unexpected operand in ShiftRightArithmetic: ";
                   imm#toPretty])))

  | ShiftRightArithmeticVariable (rd, rt, rs) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs1 = rt#to_expr floc in
     let rhs2 = rs#to_expr floc in
     let result = XOp (XAsr, [rhs1; rhs2]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | SignExtendByte (rd,rt) ->        (* TODO: constrain rhs to byte *)
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs = rt#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | SignExtendHalfword (rd,rt) ->    (* TODO: constrain rhs to half word *)
     let floc = get_floc loc in
     let (lhs,lhscmds) = rd#to_lhs floc in
     let rhs = rt#to_expr floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | StoreByte (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | StoreHalfWord (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     default (lhscmds @ cmds)

  | StoreWord (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs rhs in
     let _ =
       if src#is_register then
         let var = env#mk_mips_register_variable src#get_register in
         if floc#has_initial_value var then
           finfo#save_register floc#cia (MIPSRegister src#get_register) in
     default (lhscmds @ cmds)

  (* Assume that the write succeeds, that is, no concurrent conflicting accesses *)
  | StoreConditionalWord (dst,src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs1,lhscmds1) = dst#to_lhs floc in
     let (lhs2,lhscmds2) = src#to_lhs floc in
     let cmds1 = floc#get_assign_commands lhs1 rhs in
     let cmds2 = floc#get_assign_commands lhs2 one_constant_expr in
     default (lhscmds1 @ lhscmds2 @ cmds1 @ cmds2)

  | StoreWordFromFP (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | StoreDoublewordFromFP (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | StoreWordLeft (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | StoreWordRight (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | Subtract (dst,src1,src2) ->
     let floc = get_floc loc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs (XOp (XMinus, [ rhs1 ; rhs2 ])) in
     default (lhscmds @ cmds)     

  | SubtractUnsigned (dst,src1,src2) ->
     let floc = get_floc loc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_assign_commands lhs (XOp (XMinus, [ rhs1 ; rhs2 ])) in
     default (lhscmds @ cmds)

  | Xor (dst,src1,src2) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let rhs1 = src1#to_expr floc in
     let rhs2 = src2#to_expr floc in
     let result = XOp (XBXor, [ rhs1 ; rhs2 ]) in
     let cmds = floc#get_assign_commands lhs result in
     default (lhscmds @ cmds)

  | XorImmediate (dst,src,imm) ->
     let floc = get_floc loc in
     let rhs1 = src#to_expr floc in
     let rhs2 = imm#to_expr floc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds =
       match rhs2 with
       | XConst (IntConst n) when n#equal numerical_one ->
          (match rewrite_expr floc rhs1 with
           | XOp (XLt, [ x1 ; x2 ]) ->
              let result = XOp (XGe, [ x1 ; x2 ]) in
              floc#get_assign_commands lhs result
           | _ -> floc#get_abstract_commands lhs ())
       | _ -> floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | WordSwapBytesHalfwords (dst,src) ->
     let floc = get_floc loc in
     let (lhs,lhscmds) = dst#to_lhs floc in
     let cmds = floc#get_abstract_commands lhs () in
     default (lhscmds @ cmds)

  | JumpLinkRegister _ ->
     default (get_floc loc)#get_mips_call_commands

  | JumpLink _ |  BranchLink _ ->
     default (get_floc loc)#get_mips_call_commands

  | Syscall _ ->
     let floc = get_floc loc in
     if floc#has_call_target then
       default (get_floc loc)#get_mips_syscall_commands
     else
       default []

  | Branch _
    | BranchLEZero _
    | BranchLEZeroLikely _
    | BranchLTZero _
    | BranchLTZeroLikely _
    | BranchGEZero _
    | BranchGEZeroLikely _
    | BranchLTZeroLink _
    | BranchGEZeroLink _
    | BranchGTZero _
    | BranchGTZeroLikely _
    | BranchEqual _
    | BranchEqualLikely _
    | BranchNotEqual _
    | BranchNotEqualLikely _
    | Jump _
    | JumpRegister _
    | TrapIfEqualImmediate _
    | TrapIfEqual _ -> default []

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
  val exitlabel =
    make_code_label
      ~modifier:"exit"
      (make_location {loc_faddr = f#get_address; loc_iaddr = f#get_address})#ci
  val codegraph = make_code_graph ()
  val specialization =
    let faddr = f#get_address#to_hex_string in
    if specializations#has_specialization faddr then
      Some (specializations#get_specialization faddr)
    else
      None

  method translate_block (block:mips_assembly_block_int) =
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
      let (nodes,edges,newcmds) =
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
           let (testloc,jumploc,theniaddr,elseiaddr,testexpr) =
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
           let nodes = [ (blocklabel, [ transaction ]) ] in
           let edges =
             List.map
               (fun succ ->
                 let succlabel = make_code_label succ in
                 (blocklabel, succlabel)) codepc#get_block_successors in
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
      ASSERT (EQ (regVar, initVar)) in
    let freeze_external_memory_values (v:variable_t) =
      let initVar = env#mk_initial_memory_value v in
      ASSERT (EQ (v, initVar)) in
    let t9Assign =
      let t9Var = env#mk_mips_register_variable MRt9 in
      let reqN () = env#mk_num_temp in
      let reqC = env#request_num_constant in
      let (rhsCmds,rhs) = xpr_to_numexpr reqN reqC (num_constant_expr f#get_address#to_numerical)  in
      rhsCmds @ [ASSIGN_NUM (t9Var, rhs)] in
    let rAsserts = List.map freeze_initial_register_value mips_regular_registers in
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
    let constantAssigns = env#end_transaction in
    let cmds =
      constantAssigns
      @ t9Assign
      @ rAsserts
      @ mAsserts
      @ [initializeScalar]
      @ initializeBasePointerOperations  in
    TRANSACTION (new symbol_t "entry", LF.mkCode cmds, None)

  method translate =
    let faddr = f#get_address in
    let firstInstrLabel = make_code_label funloc#ci in
    let entryLabel = make_code_label ~modifier:"entry" funloc#ci in
    let exitLabel = make_code_label ~modifier:"exit" funloc#ci in
    let procname = make_mips_proc_name faddr in
    let _ = f#iter self#translate_block in
    let entrycmd = self#get_entry_cmd in
    let scope = finfo#env#get_scope in
    let _ = codegraph#add_node entryLabel [entrycmd] in
    let _ = codegraph#add_node exitlabel [SKIP] in
    let _ = codegraph#add_edge entryLabel firstInstrLabel in
    let cfg = codegraph#to_cfg entryLabel exitLabel in
    let body = LF.mkCode [ CFG (procname,cfg)] in
    let proc = LF.mkProcedure  procname ~signature:[] ~bindings:[] ~scope ~body in
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

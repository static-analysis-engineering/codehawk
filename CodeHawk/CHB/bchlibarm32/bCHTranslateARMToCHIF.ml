(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2021 Aarno Labs LLC

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

(* bchlibarm32 *)
open BCHARMAssemblyBlock
open BCHARMAssemblyFunction
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMCHIFSystem
open BCHARMCodePC
open BCHARMOpcodeRecords
open BCHARMOperand
open BCHARMTypes
open BCHDisassembleARM

module LF = CHOnlineCodeSet.LanguageFactory

let valueset_domain = "valuesets"
let x2p = xpr_formatter#pr_expr

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
      ~(testexpr:xpr_t) =
  ([], [], [])

let make_condition
      ~(testloc:location_int)
      ~(jumploc:location_int)
      ~(theniaddr:ctxt_iaddress_t)
      ~(elseiaddr:ctxt_iaddress_t)
      ~(blocklabel:symbol_t)
      ~(testexpr:xpr_t) =
  let thensucclabel = make_code_label theniaddr in
  let elsesucclabel = make_code_label elseiaddr in
  let (frozenvars, thentest, elsetest) = make_tests ~testloc ~jumploc ~testexpr in
  let make_node_and_label testcode tgtaddr modifier =
    let src = jumploc#i in
    let nextlabel = make_code_label ~src ~modifier tgtaddr in
    let testcode = testcode @ [ABSTRACT_VARS frozenvars] in
    let transaction = TRANSACTION (nextlabel, LF.mkCode testcode, None) in
    (nextlabel, [transaction]) in
  let (thentestlabel, thennode) =
    make_node_and_label thentest theniaddr "then" in
  let (elsetestlabel, elsenode) =
    make_node_and_label elsetest elseiaddr "else" in
  let thenedges =
    [(blocklabel, thentestlabel); (thentestlabel, thensucclabel)] in
  let elseedges =
    [(blocklabel, elsetestlabel); (elsetestlabel, elsesucclabel)] in
  ([(thentestlabel, thennode); (elsetestlabel, elsenode)], thenedges @ elseedges)
    

let translate_arm_instruction
      ~(funloc:location_int)
      ~(codepc:arm_code_pc_int)
      ~(blocklabel:symbol_t)
      ~(exitlabel:symbol_t)
      ~(cmds:cmd_t list) =
  let (ctxtiaddr,instr) = codepc#get_next_instruction in
  let faddr = funloc#f in
  let loc = ctxt_string_to_location faddr ctxtiaddr in  (* instr location *)
  let invlabel = get_invariant_label loc in
  let invop = OPERATION { op_name = invlabel ; op_args = [] } in
  let default newcmds = ([], [], cmds @ (invop :: newcmds)) in
  match instr#get_opcode with
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
  | BitwiseNot (setflags, ACCAlways, dst, src) when src#is_immediate ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let notrhs =
       match rhs with
       | XConst (IntConst n) -> XConst (IntConst ((nume32#sub n)#sub numerical_one))
       | _ -> XConst XRandom in
     let (lhs, lhscmds) = dst#to_lhs floc in
     let cmd = floc#get_assign_commands lhs notrhs in
     default (cmd @ lhscmds)

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
  | BranchLink (ACCAlways, tgt) when tgt#is_absolute_address ->
     default (get_floc loc)#get_arm_call_commands
     
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
  | LoadRegister (ACCAlways, dst, base, src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs, lhscmds) = dst#to_lhs floc in
     let cmd = floc#get_assign_commands lhs rhs in
     default (cmd @ lhscmds)

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
  | Move (setflags, ACCAlways, dst, src) ->
     let floc = get_floc loc in
     let rhs = src#to_expr floc in
     let (lhs, lhscmds) = dst#to_lhs floc in
     let cmd = floc#get_assign_commands lhs rhs in
     default (cmd @ lhscmds)

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

  | Pop (ACCAlways, sp, rl) ->
     let floc = get_floc loc in
     let regcount = rl#get_register_count in
     let sprhs = sp#to_expr floc in
     let reglhss = rl#to_multiple_variable floc in
     let (stackops,_) =
       List.fold_left
         (fun (acc,off) reglhs ->
           let (splhs,splhscmds) = (sp_r RD)#to_lhs floc in
           let stackop = arm_sp_deref ~with_offset:off RD in
           let stackrhs = stackop#to_expr floc in
           let cmds1 = floc#get_assign_commands reglhs stackrhs in
           (acc @ cmds1 @ splhscmds, off+4)) ([],0) reglhss in
     let (splhs,splhscmds) = (sp_r WR)#to_lhs floc in
     let increm = XConst (IntConst (mkNumerical (4 * regcount))) in
     let cmds = floc#get_assign_commands splhs (XOp (XPlus, [sprhs; increm])) in
     default (stackops @ cmds)

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
  | Push (ACCAlways, sp, rl) ->
     let floc = get_floc loc in
     let regcount = rl#get_register_count in
     let sprhs = sp#to_expr floc in     
     let rhsexprs = rl#to_multiple_expr floc in
     let (stackops,_) =
       List.fold_left
         (fun (acc,off) rhsexpr ->
           let (splhs,splhscmds) = (sp_r RD)#to_lhs floc in
           let stackop = arm_sp_deref ~with_offset:off WR in
           let (stacklhs, stacklhscmds) = stackop#to_lhs floc in
           let cmds1 = floc#get_assign_commands stacklhs rhsexpr in
           (acc @ cmds1 @ stacklhscmds @ splhscmds, off+4)) ([],(-(4*regcount))) rhsexprs in
     let (splhs,splhscmds) = (sp_r WR)#to_lhs floc in
     let decrem = XConst (IntConst (mkNumerical(4 * regcount))) in
     let cmds = floc#get_assign_commands splhs (XOp (XMinus, [sprhs; decrem])) in
     default (stackops @ cmds)
       
     
  | _ -> default []
        

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

  method translate_block (block:arm_assembly_block_int) =
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
         else if codepc#has_conditional_successor then
           let (testloc,jumploc,theniaddr,elseiaddr,testexpr) =
             codepc#get_conditional_successor_info in
           let transaction = package_transaction finfo blocklabel newcmds in
           let (nodes,edges) =
             make_condition
               ~testloc ~jumploc ~theniaddr ~elseiaddr ~blocklabel ~testexpr in
           ((blocklabel, [transaction])::nodes, edges)
         else
           let transaction = package_transaction finfo blocklabel newcmds in
           let nodes = [(blocklabel, [transaction])] in
           let edges =
             List.map
               (fun succ ->
                 let succlabel = make_code_label succ in
                 (blocklabel, succlabel)) codepc#get_block_successors in
           (nodes, edges)
      | _ -> (nodes,edges) in
    let _ = finfo#env#start_transaction in
    let (nodes, edges) = aux [] in
    begin
      List.iter (fun (label, node) -> codegraph#add_node label node) nodes;
      List.iter (fun (src, tgt) -> codegraph#add_edge src tgt) edges
    end

  method private get_entry_cmd =
    let env = finfo#env in
    let _ = env#start_transaction in
    let freeze_initial_register_value (reg:arm_reg_t) =
      let regVar = env#mk_arm_register_variable reg in
      let initVar = env#mk_initial_register_value (ARMRegister reg) in
      ASSERT (EQ (regVar, initVar)) in
    let freeze_external_memory_values (v:variable_t) =
      let initVar = env#mk_initial_memory_value v in
      ASSERT (EQ (v, initVar)) in
    let rAsserts = List.map freeze_initial_register_value arm_regular_registers in
    let externalMemvars = env#get_external_memory_variables in
    let externalMemvars = List.filter env#has_constant_offset externalMemvars in
    let mAsserts = List.map freeze_external_memory_values externalMemvars in
    let sp0 = env#mk_initial_register_value (ARMRegister ARSP) in
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
      @ rAsserts
      @ mAsserts
      @ [ initializeScalar ]
      @ initializeBasePointerOperations in
    TRANSACTION (new symbol_t "entry", LF.mkCode cmds, None)

  method translate =
    let faddr = f#get_address in
    let firstInstrLabel = make_code_label funloc#ci in
    let entryLabel = make_code_label ~modifier:"entry" funloc#ci in
    let exitLabel = make_code_label ~modifier:"exit" funloc#ci in
    let procname = make_arm_proc_name faddr in
    let _ = f#iter self#translate_block in
    let entrycmd = self#get_entry_cmd in
    let scope = finfo#env#get_scope in
    let _ = codegraph#add_node entryLabel [entrycmd] in
    let _ = codegraph#add_node exitLabel [SKIP] in
    let _ = codegraph#add_edge entryLabel firstInstrLabel in
    let cfg = codegraph#to_cfg entryLabel exitLabel in
    let body = LF.mkCode [CFG (procname, cfg)] in
    let proc = LF.mkProcedure procname [] [] scope body in
    (* let _ = pr_debug [ proc#toPretty; NL ] in *)
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

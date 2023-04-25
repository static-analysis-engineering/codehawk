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

(* bchcil *)
open BCHCBasicTypes

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

(* bchlibpower32 *)
open BCHPowerAssemblyBlock
open BCHPowerAssemblyFunction
open BCHPowerAssemblyFunctions
open BCHPowerAssemblyInstruction
open BCHPowerAssemblyInstructions
open BCHPowerCHIFSystem
open BCHPowerCodePC
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
  let floc = get_floc loc in
  let default newcmds = ([], [], cmds @ (invop :: newcmds) @ [bwdinvop]) in

  match instr#get_opcode with
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
    let rAsserts =
      List.map freeze_initial_gp_register_value (List.init 32 (fun i -> i)) in
    let unknown_scalar = env#mk_special_variable "unknown_scalar" in
    let initialize_scalar =
      DOMAIN_OPERATION
        ([valueset_domain],
         {op_name = new symbol_t "set_unknown_scalar";
          op_args = [("unknown_scalar", unknown_scalar, WRITE)]}) in
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
      @ rAsserts
      @ [initialize_scalar]
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
    let proc = LF.mkProcedure procname [] [] scope body in
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

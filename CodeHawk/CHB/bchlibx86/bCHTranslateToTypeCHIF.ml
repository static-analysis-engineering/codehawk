(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2022-2023 Aarno Labs LLC

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

(* bchlib *)
open BCHCodegraph
open BCHCPURegisters
open BCHDoubleword
open BCHFloc
open BCHFunctionInfo
open BCHLibTypes
open BCHLocation

(* bchlibx86 *)
open BCHCodePC
open BCHIFSystem
open BCHLibx86Types
open BCHOperand
open BCHX86OpcodeRecords

module LF = CHOnlineCodeSet.LanguageFactory


let make_code_label ?src ?modifier (address:ctxt_iaddress_t) = 
  let name = "pc_" ^ address in
  let atts = match modifier with
    | Some s -> [s]
    | _ -> [] in
  let atts = match src with
    | Some s -> s#to_fixed_length_hex_string :: atts | _ -> atts in
  ctxt_string_to_symbol name ~atts address


let package_transaction
      (finfo:function_info_int) (label:symbol_t) (commands:cmd_t list) =
  let commands =
    List.filter (fun cmd ->
        match cmd with | SKIP -> false | _ -> true) commands in
  let constantAssignments = finfo#env#end_transaction in
  TRANSACTION (label, LF.mkCode (constantAssignments @ commands), None)


let get_invariant_label (loc:location_int) =
  doubleword_to_symbol "invariant" loc#i


let translate_instruction
    ~(function_location:location_int)
    ~(code_pc:code_pc_int)
    ~(_block_label:symbol_t)
    ~(_exit_label:symbol_t)
    ~(commands:cmd_t list) = 
  let (ctxtiaddr,instruction) = code_pc#get_next_instruction in
  let faddr = function_location#f in
  let loc = ctxt_string_to_location faddr ctxtiaddr in
  let finfo = get_function_info faddr in
  let floc = get_floc loc in
  let invLabel = get_invariant_label loc in
  let invOp = OPERATION { op_name = invLabel ; op_args = [] } in
  let opcode = instruction#get_opcode in
  let operands = match opcode with Lea _ -> [] | _ -> get_operands opcode in
  let addrRegs = List.concat (List.map (fun op -> op#get_address_registers) operands) in
  let ptrSym = new symbol_t "pointer" in
  let fptrSym = new symbol_t "fpointer" in
  let scalarSym = new symbol_t "scalar" in
  let zeroSym = new symbol_t "zero" in
  let addrAsserts = List.map (fun reg ->
    let v = finfo#env#mk_cpu_register_variable reg in
    ASSERT (SUBSET (v, [ ptrSym ]))) addrRegs in
  let default newCommands =
    ([],[],commands @ (invOp :: (addrAsserts @ newCommands))) in
  match instruction#get_opcode with
  | Mov (_, dst, src) ->
    let (lhs, lhsCmds) = dst#to_lhs floc in
    let rhs = src#to_expr floc in
    let cmd = match rhs with
      | XVar v -> ASSIGN_SYM (lhs, SYM_VAR v)
      | _ -> ABSTRACT_VARS [ lhs ] in
    default (lhsCmds @ [ cmd ])
  | IndirectCall op ->
    let rhs = op#to_expr floc in
    let eax = finfo#env#mk_cpu_register_variable Eax in
    let cmd = match rhs with
      | XVar v -> ASSERT (SUBSET (v, [ fptrSym ]))
      | _ -> SKIP in
    let retcmd =
      if floc#has_call_target
         && floc#get_call_target#is_signature_valid then
	match floc#get_call_target#get_returntype with
	| TPtr _ -> ASSIGN_SYM (eax, SYM fptrSym)
	| _ -> SKIP 
      else
	SKIP in
    default [ cmd ; retcmd ]
  | IMul (_, op1, op2, _op3) ->
    let (lhs,lhsCmds) = op1#to_lhs floc in
    let rhs2 = op2#to_expr floc in
    let rhs3 = op2#to_expr floc in
    let cmd2 = match rhs2 with
      | XVar v -> ASSERT (SUBSET (v, [ scalarSym ]))
      | _ -> SKIP in
    let cmd3 = match rhs3 with
      | XVar v -> ASSERT (SUBSET (v, [ scalarSym ]))
      | _ -> SKIP in
    default  ((ASSERT ( SUBSET (lhs, [scalarSym]))) :: cmd2 :: cmd3 :: lhsCmds)
  | Push (_, _op) ->
    let (lhs,lhsCmds) = (esp_deref ~with_offset:(-4) WR)#to_lhs floc in
    default ( (ABSTRACT_VARS [ lhs ]) :: lhsCmds )
  | Pop (_,op) ->
    let (lhs,lhsCmds) = op#to_lhs floc in
    default ( (ABSTRACT_VARS [ lhs ]) :: lhsCmds )
  | Xor (dst, src) when (dst#equal src) && dst#is_register ->
    let subRegisters = registers_zeroed_by dst#get_cpureg in
    let cmds = List.map (fun r ->
      let rVar = finfo#env#mk_cpu_register_variable r in
      ASSIGN_SYM (rVar, SYM zeroSym)) subRegisters in
    default cmds
  | _ -> 
    let abstracts = List.fold_left (fun acc (op:operand_int) ->
      if op#is_write then 
	let (lhs,lhsCmds) = op#to_lhs floc in
	(lhsCmds @ [ ABSTRACT_VARS [ lhs ] ]) @ acc
      else
	acc) [] operands in
    default abstracts
      
class assembly_fn_type_chif_translator_t (f:assembly_function_int) =
object (self)

  val finfo = get_function_info f#get_address
  val function_location =
    make_location { loc_faddr = f#get_address; loc_iaddr = f#get_address }
  val exit_label =
    make_code_label
      ~modifier:"exit"
      (make_location  { loc_faddr = f#get_address ; loc_iaddr = f#get_address })#ci
  val code_graph = make_code_graph ()

  method translate_block (block:assembly_block_int) =
    let codePc = make_code_pc block in
    let blockLabel = make_code_label block#get_context_string in
    let rec aux commands =
      let (nodes,edges,newCommands) =
	translate_instruction
          ~function_location
          ~code_pc:codePc
          ~_block_label:blockLabel
	  ~_exit_label:exit_label
          ~commands in
      match nodes with
      | [] ->
	if codePc#has_more_instructions then
	  aux newCommands
	else
	  let transaction = package_transaction finfo blockLabel newCommands in
	  let nodes = [ (blockLabel, [ transaction ] ) ] in
	  let edges = List.map 
	    (fun successor ->
	      let successorLabel = make_code_label successor in
	      (blockLabel, successorLabel)) codePc#get_block_successors in
	  (nodes,edges)
      | _ -> (nodes,edges) in
    let _ = finfo#env#start_transaction in
    let (nodes,edges) = aux [] in
    begin
      List.iter (fun (label,node) -> code_graph#add_node label node) nodes ;
      List.iter (fun (src,dst) -> code_graph#add_edge src dst) edges
    end

  method translate =
    let faddr = f#get_address in
    let firstInstructionLabel = make_code_label function_location#ci in
    let entryLabel = make_code_label ~modifier:"entry" function_location#ci in
    let exitLabel = make_code_label ~modifier:"exit" function_location#ci in
    let procName = make_proc_name faddr in
    let _ = f#iter self#translate_block in
    let scope = finfo#env#get_scope in
    let _ = code_graph#add_node entryLabel [ SKIP ] in
    let _ = code_graph#add_node exitLabel [ SKIP ] in
    let _ = code_graph#add_edge entryLabel firstInstructionLabel in
    let cfg = code_graph#to_cfg entryLabel exitLabel in
    let body = LF.mkCode [ CFG (procName, cfg) ] in
    let proc = LF.mkProcedure procName ~signature:[] ~bindings:[] ~scope ~body in
    chif_system#add_procedure proc

end

let translate_to_type_chif (f:assembly_function_int) =
  let translator = new assembly_fn_type_chif_translator_t f in
  translator#translate

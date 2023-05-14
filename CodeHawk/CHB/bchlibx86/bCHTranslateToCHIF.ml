(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2021-2023 Aarno Labss LLC

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
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities
open BCHVariable
open BCHVariableType

(* bchlibx86 *)
open BCHAssemblyBlock
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHAssemblyInstruction
open BCHAssemblyInstructions
open BCHCodePC
open BCHConditionalJumpExpr
open BCHIFSystem
open BCHLibx86Types
open BCHOperand
open BCHPredefinedCallSemantics
open BCHX86OpcodeRecords
open BCHX86Opcodes

module B = Big_int_Z
module LF = CHOnlineCodeSet.LanguageFactory
module FFU = BCHFileFormatUtil

let cmd_to_pretty = CHLanguage.command_to_pretty 0

let type_domain = "types"
let valueset_domain = "valuesets"

(* special operation semantics *)
let op_not         = new symbol_t "bitwise_complement"
let op_bitwise_or  = new symbol_t "bitwise_or"
let op_bitwise_and = new symbol_t "bitwise_and"
let op_bitwise_xor = new symbol_t "bitwise_xor"
let op_rotate_left = new symbol_t "rotate_left"
let op_rotate_right= new symbol_t "rotate_right"
let op_rotate_carry_left = new symbol_t "rotate_carry_left"
let op_rotate_carry_right= new symbol_t "rotate_carry_right"
let op_shift_left  = new symbol_t "shift_left"
let op_shift_right = new symbol_t "shift_right"
let op_shift_left_double_precision = new symbol_t "shift_left_double_precision"
let op_shift_right_double_precision = new symbol_t "shift_right_double_precision"
let op_arithmetic_shift_right = new symbol_t "arithmetic_shift_right"
let op_realignment = new symbol_t "alignment"
let op_array_write = new symbol_t "array_write"

let trace_function (faddr:doubleword_int) =
  if system_info#is_elf then
    BCHDisassembleELF.trace_function faddr
  else
    BCHDisassemble.trace_function faddr

let cFour = int_constant_expr 4
let voidPtr = t_voidptr
let int_type (width:int) = get_ikind_from_size width
let get_exp (n:int) = Const (CInt (Int64.of_int n, IInt,None))

let make_code_label ?src ?modifier (address:ctxt_iaddress_t) = 
  let name = "pc_" ^ address in
  let atts = match modifier with
    | Some s -> [s] | _ -> [] in
  let atts = match src with
    | Some s -> s#to_fixed_length_hex_string :: atts | _ -> atts in
  ctxt_string_to_symbol name ~atts address

let get_invariant_label (loc:location_int) =
  ctxt_string_to_symbol "invariant" loc#ci

let is_invariant_opname (name:symbol_t) = name#getBaseName = "invariant"

let is_eh_prolog (finfo:function_info_int) (iaddr:ctxt_iaddress_t) =
  let loc = ctxt_string_to_location finfo#a iaddr in
  let floc = get_floc loc in
  floc#has_call_target && floc#get_call_target#get_name = "_EH_prolog"
  
let package_transaction (finfo:function_info_int) (label:symbol_t) (commands:cmd_t list) =
  let commands = List.filter (fun cmd -> match cmd with SKIP -> false | _ -> true) commands in
  let constantAssignments = finfo#env#end_transaction in
  TRANSACTION (label, LF.mkCode (constantAssignments @ commands), None)

let countInstructions = ref 0
let count_instruction () = countInstructions := !countInstructions + 1

let unprocessed_instructions = ref []
let add_unprocessed_instruction (function_location:location_int) (instruction:assembly_instruction_int) =
  unprocessed_instructions := instruction :: !unprocessed_instructions
let get_unprocessed_instructions () = !unprocessed_instructions

let get_number_of_instructions_processed () = 
  let numNotProcessed = List.length (get_unprocessed_instructions ()) in
  (!countInstructions - numNotProcessed , !countInstructions)

let reset_translation_to_chif () =
  begin
    countInstructions := 0 ;
    unprocessed_instructions := []
  end


let check_range ?low ?high (msg:pretty_t) value =
  let returnValue = ref value in
  begin
    (match low with Some low -> if value < low then
	begin ch_error_log#add "range error" msg ; returnValue := low end else ()  | _ -> ()) ;
    (match high with Some high -> if value > high then
	begin ch_error_log#add "range error" msg ; returnValue := high end else () | _ -> ()) ;
    !returnValue
  end

let dec_ecx_commands (floc:floc_int) =
  let (lhs,lhsCmds) = (ecx_r RW)#to_lhs floc in
  let rhs = (ecx_r RD)#to_expr floc in
  let cmds = floc#get_assign_commands lhs (XOp (XMinus, [ rhs ; int_constant_expr 1 ])) in
  (lhsCmds @ cmds)

let zero_ecx_commands (floc:floc_int) =
  let (lhs,lhsCmds) = (ecx_r WR)#to_lhs floc in
  (lhsCmds @ floc#get_assign_commands lhs zero_constant_expr)

let get_string_instruction_type (size:xpr_t) (width:int):btype_t =
  let optNumSize = match size with XConst (IntConst num) -> Some num#toInt | _ -> None in
  match optNumSize with
    Some n -> TArray (TInt (int_type width,[]), Some (get_exp (n/width)),[])
  | _ -> TArray (TInt (int_type width,[]), None,[]) 
    
let get_string_instruction_destination
    (floc:floc_int) 
    (dst:operand_int) 
    (size:xpr_t) 
    (width:int) =
  let env = floc#f#env in
  let dfVar = env#mk_flag_variable (X86Flag DFlag) in
  let dfVal = floc#rewrite_variable_to_external dfVar in
  if is_zero dfVal then
    dst#to_lhs floc
  else if is_one dfVal then
    let (lhs,lhsCmds) = dst#to_lhs floc in
    if env#is_memory_variable lhs then
      if env#is_unknown_memory_variable lhs then
	(lhs,lhsCmds)
      else
	match size with
	  XConst (IntConst num) ->
	      (env#mk_unknown_memory_variable "string-instrs",lhsCmds)
	| _ -> 
	  (env#mk_unknown_memory_variable "string-instrs", lhsCmds)
    else
      (lhs,lhsCmds)
  else
    let (lhs,lhsCmds) = dst#to_lhs floc in
    if env#is_memory_variable lhs then
      (env#mk_unknown_memory_variable "string-instr", lhsCmds)
    else
      (lhs,lhsCmds)
      
(* commands that increment or decrement a register based on the value of the direction flag *)
let advance_string_pointer (reg:cpureg_t) (floc:floc_int) (size:xpr_t) =
  let regOp = register_op reg 4 WR in
  let env = floc#f#env in
  let dfVar = env#mk_flag_variable (X86Flag DFlag) in
  let zero = env#request_num_constant numerical_zero in
  let one = env#request_num_constant numerical_one in
  let dfZero = ASSERT (EQ (dfVar, zero)) in
  let dfOne = ASSERT (EQ (dfVar, one)) in
  let edi = env#mk_cpu_register_variable reg in
  let (lhs,lhsCmds) = regOp#to_lhs floc in
  let incCmds = floc#get_assign_commands lhs (XOp (XPlus, [ XVar edi ; size ])) in
  let decCmds = floc#get_assign_commands lhs (XOp (XMinus, [ XVar edi ; size ])) in
  let branch = BRANCH [ LF.mkCode (dfZero :: incCmds) ; LF.mkCode (dfOne :: decCmds) ] in
  lhsCmds @ [ branch ]
    
(* commands that increment or decrement Esi and Edi based on the value of the direction flag *)
let advance_string_pointers (floc:floc_int) (size:xpr_t) =
  let env = floc#f#env in
  let edi = env#mk_cpu_register_variable Edi in
  let esi = env#mk_cpu_register_variable Esi in
  let (ediLhs,ediLhsCmds) = (edi_r WR)#to_lhs floc in
  let (esiLhs,esiLhsCmds) = (esi_r WR)#to_lhs floc in
  let dfVar = env#mk_flag_variable (X86Flag DFlag) in
  let zero = env#request_num_constant numerical_zero in
  let one = env#request_num_constant numerical_one in
  let dfZero = ASSERT (EQ (dfVar, zero)) in
  let dfOne = ASSERT (EQ (dfVar, one)) in
  let ediIncCmds = floc#get_assign_commands ediLhs (XOp (XPlus, [ XVar edi ; size ])) in
  let esiIncCmds = floc#get_assign_commands esiLhs (XOp (XPlus, [ XVar esi ; size ])) in
  let ediDecCmds = floc#get_assign_commands ediLhs (XOp (XMinus, [ XVar edi ; size ])) in
  let esiDecCmds = floc#get_assign_commands esiLhs (XOp (XMinus, [ XVar esi ; size ])) in
  let branch = BRANCH [ LF.mkCode (dfZero :: (ediIncCmds @ esiIncCmds)) ;
			LF.mkCode (dfOne  :: (ediDecCmds @ esiDecCmds)) ] in
  (ediLhsCmds @ esiLhsCmds @ [ branch ])

class type assembly_function_translator_int =
object
  method translate: unit
end

let check_pic_target (floc:floc_int) instr =
  if system_info#is_elf then
    begin
      chlog#add "attempt resolve pic" floc#l#toPretty ;
      BCHDisassembleELF.resolve_pic_target floc instr ;
      if floc#has_call_target && floc#get_call_target#is_nonreturning then
        let _ = chlog#add "request retrace" floc#l#toPretty in
        raise Request_function_retracing
    end
  else
    ()
	
let make_tests 
    ~(jump_instruction:assembly_instruction_int)
    ~(test_instruction:assembly_instruction_int)
    ~(jump_location:location_int)
    ~(test_location:location_int) = 
  let testFloc = get_floc test_location in
  let jumpFloc = get_floc jump_location in
  let env = testFloc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let (frozenVars,optBooleanExpr) = 
    conditional_jump_expr ~jumpopc:jump_instruction#get_opcode 
      ~testopc:test_instruction#get_opcode ~jumploc:jump_location ~testloc:test_location in
  let convert_to_chif expr =
    let (cmds,bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ [ ASSERT bxpr ] in
  let convert_to_assert expr  =
    let vars = variables_in_expr expr in
    let varssize = List.length vars in
    let xprs = 
      if varssize = 1 then
	let var = List.hd vars in
	let extExprs = jumpFloc#inv#get_external_exprs var in
	let extExprs = List.map (fun e -> substitute_expr (fun v -> e) expr) extExprs in
	expr :: extExprs
      else if varssize = 2 then
	let varList = vars in
	let var1 = List.nth varList 0 in
	let var2 = List.nth varList 1 in
	let externalExprs1 = jumpFloc#inv#get_external_exprs var1 in
	let externalExprs2 = jumpFloc#inv#get_external_exprs var2 in
	let xprs = List.concat
	  (List.map 
	     (fun e1 ->
	       List.map
		 (fun e2 ->
		   substitute_expr (fun w -> if w#equal var1 then e1 else e2) expr)
		 externalExprs2)
	     externalExprs1) in
	expr :: xprs
      else
	[ expr ] in
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
    const_assigns @ [ branch ] in
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
  match optBooleanExpr with 
    Some booleanExpr ->
      let thenCode = make_test_code booleanExpr in
      let elseCode = make_test_code (simplify_xpr (XOp (XLNot, [ booleanExpr ]))) in
      (frozenVars,Some (thenCode, elseCode))
  | _ -> (frozenVars,None)
    
    
let make_condition 
    ~(jump_instruction:assembly_instruction_int)
    ~(test_instruction:assembly_instruction_int)
    ~(jump_location:location_int)
    ~(test_location:location_int)
    ~(block_label:symbol_t)
    ~(then_successor_address:ctxt_iaddress_t)
    ~(else_successor_address:ctxt_iaddress_t) =
  let thenSuccessorLabel = make_code_label then_successor_address in
  let elseSuccessorLabel = make_code_label else_successor_address in
  let (frozenVars,tests) = 
    make_tests ~jump_location ~test_location ~jump_instruction ~test_instruction in
  match tests with
    Some (then_test, else_test) ->
      let make_node_and_label testCode targetAddress modifier =
	let src = jump_location#i in
	let nextLabel = make_code_label ~src ~modifier targetAddress in
	let testCode = testCode @ [ ABSTRACT_VARS frozenVars ] in
	let transaction = TRANSACTION ( nextLabel, LF.mkCode testCode, None) in
	(nextLabel, [ transaction ] ) in
      let (thenTestLabel, thenNode) = 
	make_node_and_label then_test then_successor_address "then" in
      let (elseTestLabel, elseNode) = 
	make_node_and_label else_test else_successor_address "else" in
      let thenEdges = 
	[ (block_label, thenTestLabel) ; (thenTestLabel, thenSuccessorLabel) ] in
      let elseEdges = 
	[ (block_label, elseTestLabel) ; (elseTestLabel, elseSuccessorLabel) ] in
      ( [ (thenTestLabel, thenNode) ; (elseTestLabel, elseNode) ], thenEdges @ elseEdges )
  | _ ->
    let abstractLabel = 
      make_code_label ~modifier:"abstract" test_location#ci in
    let transaction = 
      TRANSACTION (abstractLabel, LF.mkCode [ ABSTRACT_VARS frozenVars ], None) in
    let edges = [ (block_label, abstractLabel) ; (abstractLabel, thenSuccessorLabel) ;
		  (abstractLabel, elseSuccessorLabel) ] in
    ([ (abstractLabel, [transaction])], edges) 

let record_operand_address_types finfo (iaddr:string) opcode =
  let add r =
    let rvar = finfo#env#mk_cpu_register_variable  r in
    let ftinv:type_invariant_io_int = finfo#ftinv in
    ftinv#add_var_fact iaddr rvar t_voidptr in
  List.iter add 
    (List.concat (List.map (fun op -> op#get_address_registers) (get_operands opcode)))
      
let translate_instruction
    ~(function_location:location_int)
    ~(code_pc:code_pc_int)
    ~(block_label:symbol_t)
    ~(exit_label:symbol_t)
    ~(commands:cmd_t list) =
  let _ = count_instruction () in
  let (ctxtiaddr,instruction) = code_pc#get_next_instruction in
  let faddr = function_location#f in
  let loc = ctxt_string_to_location faddr ctxtiaddr in  
  let finfo = get_function_info faddr in
  let inv = finfo#iinv ctxtiaddr in
  let env = finfo#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let invariantLabel = get_invariant_label loc in
  let invariantOperation = OPERATION { op_name = invariantLabel ; op_args = [] } in
  let frozenAsserts = List.map (fun (v,fv) -> ASSERT (EQ (v,fv)))
    (finfo#get_test_variables ctxtiaddr) in
  let default newCommands = 
    ([], [], commands @ frozenAsserts @ (invariantOperation :: newCommands)) in
  let _ = record_operand_address_types finfo ctxtiaddr instruction#get_opcode in
  match instruction#get_opcode with
    (* control flow is handled separately *)
  | Jcc _ when system_info#is_fixed_true_branch loc#i -> default []
  | Jecxz op
  | DirectLoop op
  | Jcc (_, op) ->
    if op#is_absolute_address then
      let thenAddress = (make_i_location loc op#get_absolute_address)#ci in
      let elseAddress = code_pc#get_false_branch_successor in
      let decCmds = match instruction#get_opcode with 
	| DirectLoop _ -> dec_ecx_commands (get_floc loc) | _ -> [] in
      let cmds = commands @ [ invariantOperation ] @ decCmds in
      let transaction = package_transaction finfo block_label cmds in
      if finfo#has_associated_cc_setter ctxtiaddr then
	let testIAddress = finfo#get_associated_cc_setter ctxtiaddr in
        let testloc = ctxt_string_to_location faddr testIAddress in
        let testAddress = (ctxt_string_to_location faddr testIAddress)#i in
	let (nodes,edges) = make_condition 
	  ~jump_instruction:instruction
	  ~test_instruction:(!assembly_instructions#at_address testAddress)
	  ~jump_location:loc
	  ~test_location:testloc
	  ~block_label:block_label
	  ~then_successor_address:thenAddress
	  ~else_successor_address:elseAddress in
	((block_label, [ transaction ])::nodes, edges, [])
      else
	let thenSuccessorLabel = make_code_label thenAddress in
	let elseSuccessorLabel = make_code_label elseAddress in
	let nodes = [ (block_label, [ transaction ]) ] in
	let edges = [ (block_label, thenSuccessorLabel) ; 
		      (block_label, elseSuccessorLabel) ] in
	(nodes, edges, [])
    else
      begin
	ch_error_log#add "internal error" 
	  (LBLOCK [ STR "Unexpected operand in conditional jump: " ; op#toPretty]) ;
	raise (BCH_failure (LBLOCK [ STR "translate_instruction:conditional jump"]))
      end
  | DirectCall op when instruction#is_inlined_call ->
     let floc = get_floc loc in
     let espRhs = env#mk_cpu_register_variable Esp in
     let rhs = XVar (env#mk_special_variable "inline-return-address") in
     let (espLhs,espLhsCmds) = (esp_r WR)#to_lhs floc in
     let stackOperand = esp_deref ~with_offset:(-4) WR in
     let (stackLhs, stackLhsCmds) = stackOperand#to_lhs floc in
     let four = num_constant_expr (mkNumerical 4) in
     let cmds1 = floc#get_assign_commands espLhs (XOp (XMinus, [ XVar espRhs ; four ])) in
     let cmds2 = floc#get_assign_commands stackLhs rhs in
     let cmds = espLhsCmds @ stackLhsCmds @ cmds1 @ cmds2 in
     let _ = chlog#add "replace inlined call instr"
           (LBLOCK [ pretty_print_list cmds (fun c -> cmd_to_pretty c) "[" "," "]" ]) in
     default cmds

  | DirectCall op when op#is_absolute_address && has_callsemantics op#get_absolute_address ->
    let semantics = get_callsemantics op#get_absolute_address in
    default ( semantics#get_commands (get_floc loc) )

  (* _EH_prolog:
     0   push -1
     -4  push eax
     -8  mov eax, large fs:0
     -12 push eax
     -12 mov eax, [esp_in]
     -12 mov large fs:0, esp
     -12 mov [esp_in] ebp
     -12 lea ebp [esp_in]
     -16 push eax
         rtn
  *)
  | DirectCall _ | IndirectCall _ when is_eh_prolog finfo ctxtiaddr ->
    let floc = get_floc loc in
    let esp = env#mk_cpu_register_variable Esp in
    let ebp = env#mk_cpu_register_variable Ebp in
    let eax = env#mk_cpu_register_variable Eax in
    let four = num_constant_expr (mkNumerical 4) in
    let sixteen = num_constant_expr (mkNumerical 16) in
    let (loc1,lcmds1) = (esp_deref ~with_offset:(-4) WR)#to_lhs floc in
    let (loc2,lcmds2) = (esp_deref ~with_offset:(-8) WR)#to_lhs floc in
    let (loc3,lcmds3) = (esp_deref ~with_offset:(-12) WR)#to_lhs floc in
    let cmds1 = floc#get_assign_commands loc2 (num_constant_expr (mkNumerical (-1))) in
    let cmds2 = floc#get_assign_commands loc3 (XVar eax) in
    let cmds3 = ABSTRACT_VARS [ eax ] in
    let cmds4 = floc#get_assign_commands loc1 (XVar ebp) in
    let cmds5 = floc#get_assign_commands ebp (XOp (XMinus, [ XVar esp ; four ])) in
    let cmds6 = floc#get_assign_commands esp (XOp (XMinus, [ XVar esp ; sixteen ])) in
    default ( lcmds1 @ lcmds2 @ lcmds3 @ cmds1 @ cmds2  @ [ cmds3 ] @
		cmds4 @ cmds5 @ cmds6 )

  | IndirectCall op ->
    let floc = get_floc loc in
    let _ = 
      floc#add_xpr_type_fact (op#to_expr floc) (t_ptrto (t_function_anon t_unknown)) in
    let string_retriever = FFU.get_string_reference in
    default ((get_floc loc)#get_call_commands string_retriever)

  | DirectCall _ ->
     let floc =  get_floc loc in
     begin
       (if (not floc#has_call_target) ||
             floc#get_call_target#is_unknown then
          check_pic_target floc instruction) ;
       let string_retriever = FFU.get_string_reference in
       default (floc#get_call_commands string_retriever)
     end
      
  (* ------------------------------------------------ op1 := effective address of op2 *)
  | Lea (op1, op2) ->
	  (* let typeOps = get_operand_type_inferences [ op1 ; op2 ] in *)
    let floc = get_floc loc in
    let rhs = op2#to_address floc in
    let (lhs, lhsCmds) = op1#to_lhs floc in
    let cmds = floc#get_assign_commands lhs ~size:cFour rhs in
    default (cmds @ lhsCmds )
      
  | ConvertLongToDouble _ ->      
    let edx = env#mk_cpu_register_variable Edx in
    default [ ABSTRACT_VARS [ edx ] ]
      
  | ConvertWordToDoubleword _ ->
    let eax = env#mk_cpu_register_variable Eax in
    default [ ABSTRACT_VARS [ eax ] ]

  | SetALC -> 
    let floc = get_floc loc in
    let eax = eax_r WR in
    let (lhs,cmds) = eax#to_lhs floc in
    let abscmds = floc#get_abstract_commands lhs () in
    default (cmds @ abscmds)
      
    (* move operations                                                                  *)
    (* --------------------------------------------------------------------- op1 := op2 *)
  | Mov (width, dst, src) when src#is_function_argument ->
    let floc = get_floc loc in
    let size = int_constant_expr width in
    let (callAddress, argIndex) = src#get_function_argument in
    let bridgeVariable = env#mk_bridge_value callAddress argIndex in
    let rhs = src#to_expr floc in
    let (lhs, lhsCmds) = dst#to_lhs floc in
    let argCommands = if src#is_immediate_value then
	let constant = src#get_immediate_value#to_numerical in
	let _ = finfo#add_constant bridgeVariable constant in
	[]
      else
	floc#get_assign_commands bridgeVariable ~size rhs in
    let cmds = floc#get_assign_commands lhs ~size rhs in
    default ( cmds @ argCommands @ lhsCmds  )
	    
    (* ----------------------------------------------------------------------- op1 := op2 *)
  | Movdw (size, op1, op2) 
  | Mov (size, op1, op2) -> (* let typeOps = get_operand_type_inferences [ op1 ; op2 ] in *)
    let floc = get_floc loc in
    let rhs = op2#to_expr floc in
    let (lhs, lhsCmds) = op1#to_lhs floc in
    let cmd = floc#get_assign_commands lhs ~size:(int_constant_expr size) rhs in
    default ( cmd @ lhsCmds  )
      
    (* -------------------------------------------- op1 := zero-extend register op2 (byte) *)
  | Movzx (w, op1, op2) when op1#is_register && op2#is_register &&
      op1#get_cpureg = full_reg_of_reg op2#get_cpureg ->
    let floc = get_floc loc in
    let rhs = op2#to_expr (* ~src_size:1 ~dst_size:w ~zero_extend:true *) floc in
    let (lhs,lhsCmds) = op1#to_lhs floc in
    let cmds = floc#get_assign_commands lhs ~size:(int_constant_expr w) rhs in
    default ( cmds @ lhsCmds )
      
    (* ------------------------------------------------`-- op1 = zero-extend op2 (byte) *)
  | Movzx (w, op1, op2) ->
    let floc = get_floc loc in
    let rhs = op2#to_expr  (* ~src_size:1 ~dst_size:w ~zero_extend:true *) floc in
    let (lhs, lhsCmds) = op1#to_lhs floc in
    let cmds = floc#get_assign_commands lhs ~size:(int_constant_expr w) rhs in
    default ( cmds @ lhsCmds )
	    
    (* ------------------------------------------------`-- op1 = sign-extend op2 (byte) *)
  | Movsx (w, op1, op2) ->
    let floc = get_floc loc in
    let rhs = op2#to_expr (* ~src_size:1 ~dst_size:w ~sign_extend:true *) floc in
    let (lhs, lhsCmds) = op1#to_lhs floc in
    let cmds = floc#get_assign_commands lhs ~size:(int_constant_expr w) rhs in
    default ( cmds @ lhsCmds )     

  (* ---------------------------------------------------- load Al with value from table *)
  | TableLookupTranslation ->
    let floc = get_floc loc in
    let (lhs,lhsCmds) = (al_r WR)#to_lhs floc in
    let cmds = lhsCmds @ (floc#get_abstract_commands lhs ()) in
    default cmds
      
    (* ----------------------------------------------------------`if cc then op1 := op2 *)
    (* Conditional move: only performed if condition is true, currently modeled by
		   nondeterminstic choice                                               *)
  | CMovcc (_,w, op1, op2) ->
    let floc = get_floc loc in
    let rhs = op2#to_expr floc in
    let (lhs,lhsCmds) = op1#to_lhs floc in
    let cmds = floc#get_assign_commands lhs ~size:(int_constant_expr w) rhs in
    let branch = BRANCH [ LF.mkCode [] ; LF.mkCode cmds ] in
    default ([ branch ] @ lhsCmds )
      
    (* -----------------------------------------------------------------------------------
     * IF al/ax/eax = DEST
     * THEN
     *   ZF <- 1
     *   DEST <- SRC
     * ELSE
     *   ZF <- 0
     *   al/ax/eax <- DEST
     * ----------------------------------------------------------------------------------- *)
  | CmpExchange (width, dst, src) ->
    let floc = get_floc loc in
    let acc = register_op (sized_reg_of_reg Eax width) width RW in
    let size = int_constant_expr width in
    let accRhs = acc#to_expr floc in
    let srcRhs = src#to_expr floc in
    let dstRhs = dst#to_expr floc in
    let (dstLhs,dstLhsCmds) = dst#to_lhs floc in
    let (accLhs,accLhsCmds) = acc#to_lhs floc in
    let eqtestExpr  = XOp (XEq, [ accRhs ; dstRhs ]) in
    let neqtestExpr = XOp (XNe, [ accRhs ; dstRhs ]) in
    let (eqtestCmds,eqxpr)   = xpr_to_boolexpr reqN reqC eqtestExpr in
    let (neqtestCmds,neqxpr) = xpr_to_boolexpr reqN reqC neqtestExpr in
    let eqAssignCmds  = floc#get_assign_commands dstLhs ~size srcRhs in
    let neqAssignCmds = floc#get_assign_commands accLhs ~size dstRhs in
    let eqCmds  = eqtestCmds  @ [ ASSERT eqxpr ]  @ eqAssignCmds in
    let neqCmds = neqtestCmds @ [ ASSERT neqxpr ] @ neqAssignCmds in
    let branch = BRANCH [ LF.mkCode eqCmds ; LF.mkCode neqCmds ] in
    default ( branch :: (dstLhsCmds @ accLhsCmds) )

    (* -----------------------------------------------------------------------------------
     * TEMP64 <- DEST;
     * IF (EDX:EAX = TEMP64) 
     *   THEN
     *      ZF <- 1;
     *      DEST <- ECX:EBX; 
     *   ELSE
     *      ZF <- 0;
     *      EDX:EAX <- TEMP64; 
     *      DEST <- TEMP64;
     *   FI;
     * FI;
     * ----------------------------------------------------------------------------------- *)
  | CmpExchange8B (op, edxeax, ecxebx) ->
    let size = int_constant_expr 8 in
    let floc = get_floc loc in
    let tmpRhs = op#to_expr floc in
    let (tmpLhs,tmpLhsCmds) = op#to_lhs floc in
    let opEdxEaxRhs = edxeax#to_expr floc in
    let (opEdxEaxLhs,opEdxEaxLhsCmds) = edxeax#to_lhs floc in
    let opEcxEbxRhs = ecxebx#to_expr floc in
    let eqtestExpr = XOp (XEq, [ tmpRhs ; opEdxEaxRhs ]) in
    let neqtestExpr = XOp (XNe, [ tmpRhs ; opEdxEaxRhs ]) in
    let (eqtestCmds, eqxpr) = xpr_to_boolexpr reqN reqC eqtestExpr in
    let (neqtestCmds, neqxpr) = xpr_to_boolexpr reqN reqC neqtestExpr in
    let eqAssignCmds = floc#get_assign_commands tmpLhs ~size opEcxEbxRhs in
    let neqAssignCmds1 = floc#get_assign_commands tmpLhs ~size tmpRhs in
    let neqAssignCmds2 = floc#get_assign_commands opEdxEaxLhs ~size tmpRhs in
    let eqCmds = eqtestCmds @ [ ASSERT eqxpr ] @ eqAssignCmds in
    let neqCmds = neqtestCmds @ [ ASSERT neqxpr ] @ neqAssignCmds1 @ neqAssignCmds2 in
    let branch = BRANCH [ LF.mkCode eqCmds ; LF.mkCode neqCmds ] in
    default ( branch :: (tmpLhsCmds @ opEdxEaxLhsCmds))
    

    (* ------------------------------------------------------------------------------ 
     * Move string
     *   mem [ ES:EDI ] <- mem [ DS:ESI ]
     *   IF DF = 0 THEN 
     *     EDI <- EDI + width
     *   ELSE
     *     EDI <- EDI - width
     * ------------------------------------------------------------------------------ *)
  | Movs (width, op1, op2,srcptr,dstptr) ->
    let floc = get_floc loc in
    let size = int_constant_expr width in
    let (lhs,lhsCmds) = op1#to_lhs floc in
    let rhs = op2#to_expr floc in
    let cmds = floc#get_assign_commands lhs ~size rhs in
    let stringPtrCmds = advance_string_pointers floc size in
    default (cmds @ stringPtrCmds @ lhsCmds )

    (* ------------------------------------------------------------------------------ 
     * Move floating-point values between xmm registers and memory
     * ------------------------------------------------------------------------------ *)
  | FXmmMove (_,scalar,single,dst,_) ->
    let floc = get_floc loc in
    let size = int_constant_expr dst#size in
    let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
    let vtype = get_float_type scalar single in
    let cmds = floc#get_abstract_commands dstLhs ~size	~vtype () in
    default ( cmds @ dstLhsCmds )

    (* ------------------------------------------------------------------------------ 
     * Compare floating point values and store result in dst
     * ------------------------------------------------------------------------------ *)
  | FXmmCompare (_,_,dst,_,_) ->
    let floc = get_floc loc in
    let size = int_constant_expr dst#size in
    let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
    let cmds = floc#get_abstract_commands dstLhs ~size () in
    default ( cmds @ dstLhsCmds )

    (* ------------------------------------------------------------------------------ 
     * Convert floating point values between single, double precision, integers
     * ------------------------------------------------------------------------------ *)
  | FConvert (_,_,_,dst,_) ->
    let floc = get_floc loc in
    let size = int_constant_expr dst#size in
    let (dstLhs,dstLhsCmds) = dst#to_lhs floc in
    let cmds = floc#get_abstract_commands dstLhs ~size () in
    default ( cmds @ dstLhsCmds )

    (* ------------------------------------------------------------------------------ 
     * Compare string operands
     *   SetStatusFlags ( mem [ DS:ESI ] - mem [ ES:EDI ] )
     *   IF DF = 0 THEN 
     *     EDI <- EDI + width
     *     ESI <- ESI + width
     *   ELSE
     *     EDI <- EDI - width
     *     ESI <- ESI - width
     * ------------------------------------------------------------------------------ *)
  | Cmps (width,_,_) -> 
    let floc = get_floc loc in
    let size = int_constant_expr width in
    default (advance_string_pointers floc size)

  (* ------------------------------------------------------------------------------ 
   * Input byte/word/dword from port: dest <- I/O data
   * ------------------------------------------------------------------------------ *)
  | InputFromPort (_,op,_) ->
    let floc = get_floc loc in
    let (lhs,lhsCmds) = op#to_lhs floc in
    let abstrCmds = floc#get_abstract_commands lhs () in
    default (lhsCmds @ abstrCmds)

    (* ------------------------------------------------------------------------------ 
     * Input data from port
     *   mem [ ES:EDI ] <- SRC (read from I/O port)
     *   IF DF = 0 THEN 
     *     EDI <- EDI + width
     *   ELSE
     *     EDI <- EDI - width
     * ------------------------------------------------------------------------------ *)
  | InputStringFromPort (width,op) ->
    let floc = get_floc loc in
    let size = int_constant_expr width in
    let (lhs,lhsCmds) = op#to_lhs floc in
    let stringPtrCmds = advance_string_pointer Edi floc size in
    let abstrCmds = floc#get_abstract_commands lhs () in
    default (lhsCmds @ stringPtrCmds @ abstrCmds)

  (* ------------------------------------------------------------------------------ 
   * Output byte/word/dword to port
   * ------------------------------------------------------------------------------ *)
  | OutputToPort _ -> default []

    (* ------------------------------------------------------------------------------ 
     * Output data to port
     *   I/O port <- mem [ DS:ESI ]
     *   IF DF = 0 THEN 
     *     EDI <- ESI + width
     *   ELSE
     *     EDI <- ESI - width
     * ------------------------------------------------------------------------------ *)
  | OutputStringToPort (width,op) ->
    let floc = get_floc loc in
    let size = int_constant_expr width in
    default (advance_string_pointer Esi floc size)

    (* ------------------------------------------------------------------------------ 
     * Load string
     *   DEST <- mem [ DS:ESI ]
     *   IF DF = 0 THEN 
     *     ESI <- ESI + width
     *   ELSE
     *     ESI <- ESI - width
     * ------------------------------------------------------------------------------ *)
    | Lods (width, op) ->
      let floc = get_floc loc in
      let size = int_constant_expr width in
      let lhs = register_op (sized_reg_of_reg Eax width) width WR in
      let (lhs, lhsCmds) = lhs#to_lhs floc in
      let rhs = op#to_expr floc in
      let cmds = floc#get_assign_commands lhs ~size rhs in
      let stringPtrCmds = advance_string_pointer Esi floc size in
      default (lhsCmds @ cmds @ stringPtrCmds)

    (* ------------------------------------------------------------------------------ 
     * Scan string
     *   SetStatusFlags ( al/ax/eax - mem [ ES:EDI ] )
     *   IF DF = 0 THEN 
     *     EDI <- EDI + width
     *   ELSE
     *     EDI <- EDI - width
     * ------------------------------------------------------------------------------ *)
    | Scas (width,_) -> 
      let floc = get_floc loc in
      let size = int_constant_expr width in
      default (advance_string_pointer Edi floc size)

    (* ------------------------------------------------------------------------------ 
     * Store string
     *   mem [ ES:EDI ] <- al/ax/eax
     *   IF DF = 0 THEN 
     *     EDI <- EDI + width
     *   ELSE
     *     EDI <- EDI - width
     * ------------------------------------------------------------------------------ *)
    | Stos (width, dst, src, opedi,opdf) ->
      let floc = get_floc loc in
      let size = int_constant_expr width in
      (* let src = if width = 1 then al_r RD else if width = 2 then ax_r RD else eax_r RD in *)
      let (lhs, lhsCmds) = dst#to_lhs floc in
      let rhs = src#to_expr floc in
      let stringPtrCmds = advance_string_pointer Edi floc size in
      let cmds = floc#get_assign_commands lhs ~size rhs in
      default (lhsCmds @ stringPtrCmds @ cmds)

    (* -----------------------------------------------------------------------------------
     * RepECmps: Find non-matching bytes in DS:[ESI] and ES:[EDI]
     *  terminating condition: ECX = 0 or ZF = 0
     * RepNeCmps: Find matching bytes in DS:[ESI] and ES:[EDI]
     *  terminating condition: ECX = 0 or ZF = 1
     * Semantics (parallel)
     *   let size = ECX * width in
     *   ECX' >= 0
     *   if DF = 0 :
     *     ESI' > ESI and ESI' <= ESI + size
     *     EDI' > EDI and EDI' <= EDI + size
     *   if DF = 1 :
     *     ESI' < ESI and ESI' >= ESI - size
     *     EDI' < EDI and EDI' >= EDI - size
     * ----------------------------------------------------------------------------------- *)
    | RepECmps (width, _, _) 
    | RepNeCmps (width, _, _) ->
      let floc = get_floc loc in
      let abstractRegs = floc#get_abstract_cpu_registers_command [ Ecx ; Esi ; Edi ] in
      default ( [ abstractRegs ])

    (* -----------------------------------------------------------------------------------
     * RepEScas: Find non-al/ax/eax byte/word/doubleword starting at ES:[EDI]
     *  terminating condition: ECX = 0 or ZF = 0
     * RepNeScas: Find al/ax/eax byte/word/doubleword start at ES:[EDI]
     *  terminating condition: ECX = 0 or ZF = 1
     * Semantics (parallel)
     *   let size = ECX * width in
     *   ECX' >= 0
     *   if DF = 0 :
     *     EDI' > EDI and EDI' <= EDI + size
     *   if DF = 1 :
     *     EDI' < EDI and EDI' >= EDI - size
     * ----------------------------------------------------------------------------------- *)
    | RepEScas (width, _) 
    | RepNeScas (width, _) ->
      let floc = get_floc loc in
      let abstractRegs = floc#get_abstract_cpu_registers_command [ Ecx ; Edi ] in
      default ([ abstractRegs ] )

    (* -----------------------------------------------------------------------------------
     * RepIns: Input ECX bytes/words/doublewords from port DX into ES:[EDI]
     * Semantics (parallel)
     *   let size = ECX * width in
     *   EXC := 0
     *   if DF = 0 :
     *     EDI := EDI + size
     *     mem [ EDI ; EDI + size - width ] := input data
     *   if DF = 1 ;
     *     EDI := EDI - size
     *     mem [ EDI - size + width ; EDI ] := input data
     * ----------------------------------------------------------------------------------- *)
    | RepIns (width, dst) ->
      let floc = get_floc loc in
      let size = simplify_xpr (XOp (XMult, [ int_constant_expr width ; 
					     (ecx_r RD)#to_expr floc ])) in
      let (lhs, lhsCmds) = get_string_instruction_destination floc dst size width in
      let zeroEcxCmds = zero_ecx_commands floc in
      let stringPtrCmds = advance_string_pointer Edi floc size in
      let dstType = get_string_instruction_type size width in
      let rhs = env#mk_side_effect_value floc#cia "repins" in
      let cmds = floc#get_assign_commands lhs ~size ~vtype:dstType (XVar rhs) in
      let cmds = lhsCmds @ stringPtrCmds @ zeroEcxCmds @ cmds in
      default cmds

    (* -----------------------------------------------------------------------------------
     * RepLods: Load ECX bytes/words/doublewords from DS:[ESI] to al/ax/eax
     * note: this is mostly considered a useless instruction, because the data keeps being
     *       overwritten without further processing; some obscure uses have been reported.
     * Semantics (parallel)
     *   let size = ECX * width in
     *   EXC := 0
     *   if DF = 0 :
     *     ESI := ESI + size
     *     al/ax/eax := mem [ EDI ; EDI + size - width ] 
     *   if DF = 1 ;
     *     ESI := ESI - size
     *     al/ax/eax := mem [ EDI - size + width ; EDI ] 
     * ----------------------------------------------------------------------------------- *)
    | RepLods (width, src) ->
      let floc = get_floc loc in
      let size = simplify_xpr (XOp (XMult, [ int_constant_expr width ; 
					     (ecx_r RD)#to_expr floc ])) in
      let zeroEcxCmds = zero_ecx_commands floc in
      let stringPtrCmds = advance_string_pointer Esi floc size in
      let dst = if width = 1 then al_r WR else if width = 2 then ax_r WR else eax_r WR in
      let (lhs,lhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_abstract_commands lhs () in
      default (cmds @ stringPtrCmds @ zeroEcxCmds @ lhsCmds )			
	
    (* -----------------------------------------------------------------------------------
     * RepMovs: Move ECX bytes/words/doublewords from DS:[ESI] to ES:[EDI]
     * Semantics (parallel)
     *   let size = ECX * width in
     *   ECX := 0
     *   if DF = 0 :
     *     ESI := ESI + size
     *     EDI := EDI + size
     *     mem [ EDI ; EDI + size - width ] := mem [ ESI ; ESI + size - width ]
     *   if DF = 1 :
     *     ESI := ESI - size
     *     EDI := EDI - size
     *     mem [ EDI - size + width ; EDI ] := mem [ ESI - size + width ; ESI ]
     * ----------------------------------------------------------------------------------- *)
    | RepMovs (width, dst, src) | RepNeMovs (width, dst, src) ->
      let floc = get_floc loc in
      let size = simplify_xpr (XOp (XMult, [ int_constant_expr width ; 
					     (ecx_r RD)#to_expr floc ])) in
      let (lhs, lhsCmds) = get_string_instruction_destination floc dst size width in
      let zeroEcxCmds = zero_ecx_commands floc in
      let stringPtrCmds = advance_string_pointers floc size in
      let dstType = get_string_instruction_type size width in
      let rhs = env#mk_side_effect_value floc#cia "repmovs" in
      let cmds = floc#get_assign_commands lhs ~size ~vtype:dstType (XVar rhs) in
      let cmds = lhsCmds @ stringPtrCmds @ zeroEcxCmds @ cmds in
      default cmds

    (* -----------------------------------------------------------------------------------
     * RepOuts: Output ECX bytes/words/doublewords from DS:[ESI] to port DX 
     * Semantics (parallel)
     *   let size = ECX * width in
     *   EXC := 0
     *   if DF = 0 :
     *     ESI := ESI + size
     *     output := mem [ EDI ; EDI + size - width ] 
     *   if DF = 1 ;
     *     ESI := ESI - size
     *     output := mem [ EDI - size + width ; EDI ] 
     * ----------------------------------------------------------------------------------- *)
    | RepOuts (width, dst) ->
      let floc = get_floc loc in
      let size = simplify_xpr (XOp (XMult, [ int_constant_expr width ; 
					     (ecx_r RD)#to_expr floc ])) in
      let zeroEcxCmds = zero_ecx_commands floc in
      let stringPtrCmds = advance_string_pointer Esi floc size in
      default (stringPtrCmds @ zeroEcxCmds)

    (* -----------------------------------------------------------------------------------
     * RepStos: Fill ECX bytes/words/doublewords at ES:[EDI] with al/ax/eax
     * Semantics (parallel)
     *   let size = ECX * width in
     *   EXC := 0
     *   if DF = 0 :
     *     EDI := EDI + size
     *     mem [ EDI ; EDI + size - width ] := al/ax/eax
     *   if DF = 1 ;
     *     EDI := EDI - size
     *     mem [ EDI - size + width ; EDI ] := al/ax/eax
     * ----------------------------------------------------------------------------------- *)
    | RepStos (width, dst) | RepNeStos (width, dst) ->
      let floc = get_floc loc in
      let size = simplify_xpr (XOp (XMult, [ int_constant_expr width ; 
					     (ecx_r RD)#to_expr floc ])) in
      let (lhs, lhsCmds) = get_string_instruction_destination floc dst size width in
      let zeroEcxCmds = zero_ecx_commands floc in
      let stringPtrCmds = advance_string_pointer Edi floc size in
      let dstType = get_string_instruction_type size width in
      let rhs = env#mk_side_effect_value floc#cia "repstos" in
      let cmds = floc#get_assign_commands lhs ~size ~vtype:dstType (XVar rhs) in
      let cmds = lhsCmds @ stringPtrCmds @ zeroEcxCmds @ cmds in
      default cmds
	

    | XCrypt _ ->
      let floc = get_floc loc in
      let (lhs,lhsCmds) = (es_edi WR)#to_lhs floc in
      let rhs = env#mk_cpu_register_variable Esi in
      let width = 16 in
      let (cntrlLhs,cntrlCmds) = (ecx_r WR)#to_lhs floc in
      let (srcRegLhs,srcCmds) = (esi_r WR)#to_lhs floc in
      let (dstRegLhs,dstCmds) = (edi_r WR)#to_lhs floc in
      let cntrlVar = env#mk_cpu_register_variable Ecx in
      let srcRegVar = env#mk_cpu_register_variable Esi in
      let dstRegVar = env#mk_cpu_register_variable Edi in
      let zero = env#request_num_constant numerical_zero in
      let incConstant = env#request_num_constant (mkNumerical width) in
      let (incVar,incCmds) =
	let tmpVar = env#mk_num_temp in
	let tmpVar2 = env#mk_num_temp in
	let lbAssert = ASSERT (GEQ (tmpVar, zero)) in
	let cmd = ASSIGN_NUM (tmpVar2, MULT (cntrlVar, incConstant)) in
	let ubAssert = ASSERT (LT (tmpVar, tmpVar2)) in
	(tmpVar, [ cmd ; lbAssert ; ubAssert ]) in
      let finalIncVar = env#mk_num_temp in
      let cmd = ASSIGN_NUM (finalIncVar, MULT (cntrlVar, incConstant)) in
      let tmpSrcRegInc = ASSIGN_NUM (srcRegLhs, PLUS (srcRegVar, incVar)) in
      let tmpDstRegInc = ASSIGN_NUM (dstRegLhs, PLUS (dstRegVar, incVar)) in
      let srcRegInc = ASSIGN_NUM (srcRegLhs, PLUS (srcRegVar, finalIncVar)) in
      let dstRegInc = ASSIGN_NUM (dstRegLhs, PLUS (dstRegVar, finalIncVar)) in
      let memAssignCmds = floc#get_assign_commands lhs (XVar rhs) in
      let cntrlAssign = ASSIGN_NUM (cntrlVar, NUM numerical_zero) in
      let cmds = lhsCmds @ cntrlCmds @ srcCmds @ dstCmds @ incCmds @ 
	[ tmpSrcRegInc ; tmpDstRegInc ] @ memAssignCmds @ 
	[ cmd ; srcRegInc ; dstRegInc ; cntrlAssign ] in
      default cmds

    (* ------------------------------------------------------------------------------ 
     * Exchange register/memory with register
     *    TEMP <- DEST
     *	  DEST <- SRC
     *    SRC <- TEMP
     * -------------------------------------------------------------------------------- *)
    | Xchg (dst, src) when dst#equal src -> default []
    | Xchg (dst, src) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let dstRhs = dst#to_variable floc in
      let srcRhs = src#to_expr floc in
      let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
      let (srcLhs, srcLhsCmds) = src#to_lhs floc in
      let temp = env#mk_num_temp in
      let tempCmd = ASSIGN_NUM (temp, NUM_VAR dstRhs) in
      let dstCmds = floc#get_assign_commands dstLhs ~size srcRhs in
      let srcCmds = floc#get_assign_commands srcLhs ~size (XVar temp)  in
      default (dstLhsCmds @ srcLhsCmds @ [ tempCmd ] @ dstCmds @ srcCmds)
      
    (* -----------------------------------------------------------------------------
     * ENTER (size,nesting):  (nesting = 0)
     *    ESP <- ESP - 4
     *    SS:ESP <- EBP
     *    EBP <- ESP
     *    ESP <- ESP - size
     * ----------------------------------------------------------------------------- *)
    | Enter (op1,op2) ->
       let floc = get_floc loc in
       let esp = env#mk_cpu_register_variable Esp in
       let ebp = env#mk_cpu_register_variable Ebp in
       let stackOperand = esp_deref ~with_offset:(-4) WR in
       let (ebpLhs,ebpLhsCommands) = (ebp_r WR)#to_lhs floc in
       let (espLhs,espLhsCommands) = (esp_r WR)#to_lhs floc in
       let (stackLhs, stackLhsCommands) = stackOperand#to_lhs floc in
       let size = num_constant_expr op1#get_immediate_value#to_numerical in
       let cmds1 = floc#get_assign_commands stackLhs (XVar ebp) in
       let cmds2 =
         floc#get_assign_commands
           ebpLhs (XOp (XMinus, [ XVar esp ; int_constant_expr 4 ])) in
       let cmds3 =
         floc#get_assign_commands
           espLhs (XOp (XMinus, [ XVar esp ;
                                  (XOp (XPlus, [ size ; int_constant_expr 4 ])) ])) in
       let cmds =
         espLhsCommands @ ebpLhsCommands @ stackLhsCommands @ cmds1 @ cmds2 @ cmds3 in
       let _ =
         if floc#has_initial_value ebp then
           finfo#save_register floc#cia (CPURegister Ebp) in
       default cmds
    
    (* ------------------------------------------------------------------------------ 
     * LEAVE:
     *    ESP <- EBP
     *	  EBP <- SS:ESP
     *    ESP <- ESP + 4
     * -------------------------------------------------------------------------------- *)
    | Leave ->
      let floc = get_floc loc in
      let esp = env#mk_cpu_register_variable Esp in
      let (espLhs,espLhsCommands) = (esp_r WR)#to_lhs floc in
      let ebp = env#mk_cpu_register_variable Ebp in
      let (ebpLhs,ebpLhsCommands) = (ebp_r WR)#to_lhs floc in
      let restoredValue= (ebp_deref RD)#to_expr floc in
      let _ = finfo#restore_register floc#cia (CPURegister Ebp) in
      let size = int_constant_expr 4 in
      let reqN () = floc#f#env#mk_num_temp in
      let reqC = floc#f#env#request_num_constant in
      let cmds1 = floc#get_assign_commands espLhs ~size (XVar ebp) in
      let cmds2 = floc#get_assign_commands ebpLhs ~size restoredValue in
      let (newEspCmds,newEsp) = 
	xpr_to_numexpr reqN reqC (XOp (XPlus, [ XVar esp ; size ])) in
      let cmd3 = ASSIGN_NUM (espLhs, newEsp) in
      let cmds =
        espLhsCommands @ ebpLhsCommands @ cmds1 @ cmds2 @ newEspCmds @ [ cmd3 ] in
      default cmds

    (* arithmetic operations *)
    (* ------------------------------------------------------------------- op = op + 1 *)
    | Increment op ->
      let floc = get_floc loc in
      let size = int_constant_expr op#size in
      let rhs = op#to_expr floc in
      let (lhs, lhsCommands) = op#to_lhs floc in
      let one = num_constant_expr (mkNumerical 1) in
      let cmds = floc#get_assign_commands lhs ~size (XOp (XPlus, [rhs ; one])) in
      default  (lhsCommands @ cmds)

    (* ------------------------------------------------------------------- op = op - 1 *)
    | Decrement op ->
      let floc = get_floc loc in
      let size = int_constant_expr op#size in
      let rhs = op#to_expr floc in
      let (lhs, lhsCmds) = op#to_lhs floc in
      let one = int_constant_expr 1 in
      let cmds = floc#get_assign_commands lhs ~size (XOp (XMinus, [rhs ; one])) in
      default (lhsCmds @ cmds)

    (* --------------------------------------------------------------- op1 = op1 + op2 *)
    | Add (op1, op2) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let rhs1 = op1#to_expr floc in
      let rhs2 = op2#to_expr floc in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_assign_commands lhs ~size (XOp (XPlus, [ rhs1 ; rhs2 ])) in
      default (lhsCmds @ cmds)

    (* ------------------------------------------------------------------------------
     * TEMP <- SRC + DEST
     * SRC <- DEST
     * DEST <- TEMP
     * ------------------------------------------------------------------------------- *)
    | XAdd (dst, src) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let srcRhs = src#to_variable floc in
      let dstRhs = dst#to_variable floc in
      let (srcLhs, srcLhsCmds) = src#to_lhs floc in
      let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
      let temp = env#mk_num_temp in
      let sum = ASSIGN_NUM (temp, PLUS (srcRhs, dstRhs)) in
      let srcCmds = floc#get_assign_commands srcLhs ~size (XVar dstRhs) in
      let dstCmds = floc#get_assign_commands dstLhs ~size (XVar temp) in
      let cmds = srcLhsCmds @ dstLhsCmds @ [ sum ] @ srcCmds @ dstCmds in
      default cmds

    (* --------------------------------------------------------------------------------
     * DEST <- DEST + SRC + CF
     * -- carry modeled nondeterministically as 0 or 1
     * -------------------------------------------------------------------------------- *)
    | AddCarry (dst, src) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let dstRhs = dst#to_expr floc in
      let srcRhs = src#to_expr floc in
      let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
      let one  = int_constant_expr 1 in
      let xpr1 = XOp (XPlus, [ XOp (XPlus, [ dstRhs ; srcRhs ]); one ]) in
      let xpr0 = XOp (XPlus, [ dstRhs ; srcRhs ]) in
      let cmds1 = floc#get_assign_commands dstLhs ~size xpr1 in
      let cmds0 = floc#get_assign_commands dstLhs ~size xpr0 in
      let branch = BRANCH [ LF.mkCode cmds0 ; LF.mkCode cmds1 ] in
      default (dstLhsCmds @ [ branch ])

    (* --------------------------------------------------------------------------------
     * DEST <- (DEST - SRC)
     * -------------------------------------------------------------------------------- *)
    | Sub (dst, src) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let dstRhs = dst#to_expr floc in
      let srcRhs = src#to_expr floc in
      let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_assign_commands dstLhs ~size (XOp (XMinus, [ dstRhs ; srcRhs ]))  in
      default (dstLhsCmds @ cmds)

    (* --------------------------------------------------------------------------------
     * DEST <- [ -(DEST) ]
     * -------------------------------------------------------------------------------- *)
    | TwosComplementNegate dst ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let dstRhs = dst#to_expr floc in
      let (dstLhs,dstLhsCmds) = dst#to_lhs floc in
      let cmds =
        floc#get_assign_commands
          dstLhs ~size	(XOp (XMinus, [ zero_constant_expr ; dstRhs ])) in
      default (dstLhsCmds @ cmds)

    (* --------------------------------------------------------------------------------
     * Integer subtraction with borrow
     * DEST <- (DEST - (SRC + CF))
     * -- when src = dst (same operand) nondeterministically assign 0 or -1 to DEST
     * -- otherwise nondeterministically assign 0 or 1 to CF
     * -------------------------------------------------------------------------------- *)
    | SubBorrow (dst, src) when dst#equal src ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
      let cmds0 = floc#get_assign_commands dstLhs ~size zero_constant_expr in
      let cmds1 =
        floc#get_assign_commands dstLhs ~size (num_constant_expr numerical_one#neg) in
      let branch = BRANCH [ LF.mkCode cmds0 ; LF.mkCode cmds1 ] in
      default (dstLhsCmds @ [ branch ])

    | SubBorrow (dst, src) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let dstRhs = dst#to_expr floc in
      let srcRhs = src#to_expr floc in
      let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
      let one  = int_constant_expr 1 in
      let cmds0 =
        floc#get_assign_commands dstLhs ~size (XOp (XMinus, [ dstRhs ; srcRhs ])) in
      let cmds1 = floc#get_assign_commands dstLhs ~size 
	(XOp (XMinus, [ dstRhs ; XOp (XPlus, [ srcRhs ; one ]) ])) in
      let branch = BRANCH [ LF.mkCode cmds0 ; LF.mkCode cmds1 ] in
      default (dstLhsCmds @ [ branch ])

    (* --------------------------------------------------------------- op1 = op2 * op3 *)
    | IMul (width, op1, op2, op3) ->
      let floc = get_floc loc in
      let size = int_constant_expr width in
      let vtype = TInt (int_type width,[]) in
      let rhs1 = op2#to_expr floc in
      let rhs2 = op3#to_expr floc in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds =
        floc#get_assign_commands lhs ~size ~vtype (XOp (XMult, [ rhs1 ; rhs2 ]))  in
      default (lhsCmds @ cmds)

    (* --------------------------------------------------------------- dst = src * op *)
    | Mul (width, dst,src, op) ->
      let floc = get_floc loc in
      let size = int_constant_expr width in
      let vtype = TInt (int_type width,[]) in
      let rhs1 = src#to_expr floc in
      let rhs2 = op#to_expr floc in
      let (lhs,lhsCmds) = dst#to_lhs floc in
      let cmds =
        floc#get_assign_commands lhs ~size ~vtype (XOp (XMult, [ rhs1 ; rhs2 ])) in
      default (lhsCmds @ cmds)

    (* --------------------------------------------------- (quot,rem) := dividend / op *)
    | IDiv (width,quot,rem,dividend,op)        (* need to distinguish between signed and unsigned *)
    | Div  (width,quot,rem,dividend,op) ->
      let floc = get_floc loc in
      let vtype = TInt (int_type width,[]) in
      let size = int_constant_expr width in
      let (quotLhs,quotLhsCmds) = quot#to_lhs floc in
      let (remLhs,remLhsCmds) = rem#to_lhs floc in
      let dividendRhs = dividend#to_expr floc in
      let divisorRhs = op#to_expr floc in
      let quotCmds = floc#get_assign_commands quotLhs ~size ~vtype 
	(XOp (XDiv, [dividendRhs ; divisorRhs ])) in
      let remCmds = floc#get_assign_commands remLhs ~size ~vtype
	(XOp (XMod, [ dividendRhs ; divisorRhs ])) in
      let cmds = quotLhsCmds @ remLhsCmds @ quotCmds @ remCmds in
      default cmds

    (* bitwise operations *)
    (* ------------------------------------------------------------------- op = not op *)
    | OnesComplementNegate op ->
      let floc = get_floc loc in
      let (lhs, lhsCmds) = op#to_lhs floc in
      let cmds = floc#get_operation_commands lhs 
	~size:(int_constant_expr op#size) op_not [ ] in
      let cmds = lhsCmds @ cmds in
      default cmds

    (* --------------------------------------------------------------- op2 = op1 & op2 *) 
    (* likely stack realignment operation                                              *)
    | LogicalAnd (dst, src) when (dst#equal (esp_r WR)) && src#is_immediate_value ->
      let floc = get_floc loc in
      let esp = env#mk_cpu_register_variable Esp in
      let esp1 = env#mk_initial_register_value ~level:1 (CPURegister Esp) in
      let cmds1 = floc#get_operation_commands esp op_realignment 
	[ ("arg1", esp, READ) ; ("result", esp, WRITE) ] in
      let cmd2 = ASSERT (EQ (esp, esp1)) in
      let _ = finfo#add_base_pointer esp1 in
      let cmds = cmds1 @ [ cmd2 ] in
      default cmds
      
    (* when one of the operands is zero and the other a register                       *)
    | LogicalAnd (dst, src) when (dst#is_zero || src#is_zero) && dst#is_register ->
      let floc = get_floc loc in
      let subRegisters = registers_zeroed_by dst#get_cpureg in
      let cmds = List.concat (List.map (fun register ->
	let registerVariable = env#mk_cpu_register_variable register in
	floc#get_assign_commands registerVariable zero_constant_expr) subRegisters) in
      default cmds

    | LogicalAnd (dst, src) when (dst#is_zero || src#is_zero) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let vtype = TInt (int_type dst#size,[]) in
      let (lhs, lhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_assign_commands lhs ~size ~vtype zero_constant_expr in
      default (lhsCmds @ cmds)
   
    (* if one of the operands has one bit set the result is either that value or zero *)
    | LogicalAnd (dst, src) when src#has_one_bit_set ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let rhs = src#to_expr floc in
      let (lhs, lhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_assign_commands lhs ~size rhs in
      let zCmds = floc#get_assign_commands lhs ~size zero_constant_expr in
      let branch = BRANCH [ LF.mkCode cmds ; LF.mkCode zCmds ] in
      default (lhsCmds @ [ branch ])

    (* if the src is a constant value then the result is less than or equal to that value *)
    | LogicalAnd (dst, src) when src#is_immediate_value ->
      let floc = get_floc loc in
      let rhs = num_constant_expr src#get_immediate_value#to_unsigned#to_numerical in
      let (rhsCmds,rhsVar) = xpr_to_numvar reqN reqC rhs in
      let (lhs, lhsCmds) = dst#to_lhs floc in
      let absCmd = ABSTRACT_VARS [ lhs ] in
      let assCmd = ASSERT (LEQ (lhs, rhsVar)) in
      default ( absCmd :: (lhsCmds @ rhsCmds @ [ assCmd ]))
	
    | LogicalAnd (dst, src) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (lhs, lhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_bitwise_and [] in
      default (lhsCmds @ cmds)

    (* --------------------------------------------------------------- op1 = op1 | op2 *)
    | LogicalOr (dst, src) when src#is_immediate_value &&
	(src#get_immediate_value#to_numerical#equal (mkNumerical (-1))) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (lhs, lhsCmds) = dst#to_lhs floc in
      let cmds =
        floc#get_assign_commands lhs ~size (num_constant_expr (mkNumerical (-1))) in
      default (lhsCmds @ cmds)

    | LogicalOr (dst, src) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (lhs, lhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_bitwise_or [] in
      default (lhsCmds @ cmds)

    (* ------------------------------------------------------------------------------- *
     * Exclusive Logical Or
     *   DEST <- DEST XOR SRC
     * -- when the two operands are the same register the register and its subregisters
     *    are set to zero
     * ------------------------------------------------------------------------------- *)
    | Xor (dst, src) when (dst#equal src) && dst#is_register ->
      let floc = get_floc loc in
      let subRegisters = registers_zeroed_by dst#get_cpureg in
      let cmds = List.concat (List.map (fun r ->
	let rVar = env#mk_cpu_register_variable r in
	floc#get_assign_commands rVar zero_constant_expr) subRegisters) in
      default cmds

    | Xor (dst, src) when dst#equal src ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_assign_commands dstLhs ~size zero_constant_expr  in
      default (dstLhsCmds @ cmds)

    | Xor (dst, src) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (dstLhs, dstLhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_operation_commands dstLhs ~size op_bitwise_xor [] in
      default (dstLhsCmds @ cmds)

    (* ------------------------------------------------------------------------------- *
     * shift and rotate operations                                                     *
     * ------------------------------------------------------------------------------- *)
    | Rcl (op1, op2) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_rotate_carry_left [] in
      default (lhsCmds @ cmds)

    | Rcr (op1, op2) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_rotate_carry_right [] in
      default (lhsCmds @ cmds)

    | Rol (op1, op2) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_rotate_left [] in
      default (lhsCmds @ cmds)

    | Ror (op1, op2) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_rotate_right [] in
      default (lhsCmds @ cmds)

    (* -------------------------------------------------------------------------------
     * note: not the same as signed division IDiv (Sar rounds to negative infinity, 
     * IDiv rounds to zero). Currently not accounted for.
     * ------------------------------------------------------------- op1 = op1 / 2^op2 *) 
    | Sar (op1, op2) when op2#is_immediate_value -> 
      let floc = get_floc loc in   
      let size = int_constant_expr op1#size in
      let exponent = match op2#get_immediate_value#to_int with
	  Some i -> check_range ~high:31 ~low:0 instruction#toPretty i
	| _ ->
	  let msg = LBLOCK [ STR "Instruction operand of " ; 
			     instruction#toPretty ; STR " is out of range " ;
			     STR "(does not fit in 32 bit integer); assign 0" ] in
	  begin
	    ch_error_log#add "translation" (LBLOCK [ floc#l#toPretty ; STR ": " ; msg ]) ;
	    0
	  end in
      let divisor = mkNumerical_big (B.power_int_positive_int 2 exponent) in
      let divisor = num_constant_expr divisor in
      let rhs = op1#to_expr floc in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_assign_commands lhs ~size (XOp (XDiv, [ rhs ; divisor ])) in
      default (lhsCmds @ cmds)

    | Sar (op1, op2) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_arithmetic_shift_right [] in
      default (lhsCmds @ cmds)

    (* ------------------------------------------------------------- op1 = op1 * 2^op2 *)
    | Shl (op1, op2) when op2#is_immediate_value ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let rhs = op1#to_expr floc in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let exponent = match op2#get_immediate_value#to_int with
	  Some i -> check_range ~high:31 ~low:0 instruction#toPretty i
	| _ ->
	  let msg = LBLOCK [ STR "Instruction operand of " ; instruction#toPretty ; 
			     STR " is out of range " ;
			     STR "(does not fit in 32 bit integer); assign 0" ] in
	  begin
	    ch_error_log#add "translation" (LBLOCK [ floc#l#toPretty ; STR ": " ; msg ]) ;
	    0 
	  end in
      let cmds =
	match exponent with
	  0 -> [ ]
	| 1 -> floc#get_assign_commands lhs ~size (XOp (XPlus, [rhs ; rhs]))
	| _ ->
	  let multiplier = mkNumerical_big (B.power_int_positive_int 2 exponent) in
	  floc#get_assign_commands
            lhs ~size (XOp (XMult, [ num_constant_expr multiplier ; rhs ])) in
      default (lhsCmds @ cmds )
	
    | Shl (op1, op2) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_shift_left [] in
      default (lhsCmds @ cmds)

    | Shld (op1, op2, op3) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds =
        floc#get_operation_commands lhs ~size op_shift_left_double_precision [] in
      default (lhsCmds @ cmds)

    (* ----------------------------------------------------------------------------------- *
     * divide by 2^31; result is either 0 or 1                                             *
     * ----------------------------------------------------------------------------------- *)
    | Shr (op1, op2) when (op2#is_immediate_value && 
			     match op2#get_immediate_value#to_int with 
			       Some i -> i=31 | _ -> false) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let setZero = floc#get_assign_commands lhs ~size zero_constant_expr in
      let setOne = floc#get_assign_commands lhs ~size one_constant_expr in
      let branch = BRANCH [ LF.mkCode setZero ; LF.mkCode setOne ] in
      default (lhsCmds @ [ branch ])

    | Shr (op1, op2) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds = floc#get_operation_commands lhs ~size op_shift_right [] in
      default (lhsCmds @ cmds)

    | Shrd (op1, op2, op3) ->
      let floc = get_floc loc in
      let size = int_constant_expr op1#size in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cmds =
        floc#get_operation_commands lhs ~size op_shift_right_double_precision [] in
      default (lhsCmds @ cmds)

    (* bit test operations *)
    | BitTest (op1, op2) ->
      let cfVar = env#mk_flag_variable (X86Flag CFlag) in
      let cmd = ABSTRACT_VARS [ cfVar ] in
      default [ cmd ]
	
    (* BitScanForward:
       searches the source (2nd) operand for the least significant set bit. 
       If a least significant 1 bit is found, its bit index is stored in the 
       destination (first) operand. The bit index is an unsigned offset from 
       bit 0 of the source operand. If the content of the source operand is
       0, the content of the destination operand is undefined 
 
       BitScanReverse: 
       searches the source for the most significant set bit.
       
       Over-approximating semantics is the same for both instructions: if the rhs 
       value is non-zero, assert that the destination value is between 0 and 31, 
       if the rhs value is zero, abstract the destination variable.
    *)
    | BitScanReverse (op1, op2)
    | BitScanForward (op1, op2) ->
      let floc = get_floc loc in
      let (lhs,lhsCmds) = op1#to_lhs floc in
      let rhs = op2#to_expr floc in
      let zeroTestExpr = XOp (XEq, [ rhs ; zero_constant_expr ]) in
      let notzeroTestExpr = XOp (XNe, [ rhs ; zero_constant_expr ]) in
      let (zeroTestCmds,zeroBoolExpr) = xpr_to_boolexpr reqN reqC zeroTestExpr in
      let (notzeroTestCmds,notzeroBoolExpr) = xpr_to_boolexpr reqN reqC notzeroTestExpr in
      let abstractCmds = floc#get_abstract_commands lhs () in
      let zeroCmds = zeroTestCmds @ [ ASSERT zeroBoolExpr ] @ abstractCmds in			
      let notzeroCmds = 
	let xpr = XOp (XNumRange, [ zero_constant_expr; int_constant_expr 31 ]) in
	let assignCmds = floc#get_assign_commands lhs xpr in
	notzeroTestCmds @ [ ASSERT notzeroBoolExpr ] @ assignCmds in
      let branchCmd = BRANCH [ LF.mkCode zeroCmds ; LF.mkCode notzeroCmds ] in
      default (lhsCmds @ [ branchCmd ])
	
    (* Reverses the byte order of a 32 bit register *)
    | BSwap op ->
      let floc = get_floc loc in
      let (lhs,lhsCmds) = op#to_lhs floc in
      let abstractCmds = floc#get_abstract_commands lhs () in
      default (lhsCmds @ abstractCmds)
	
    (* ------------------------------------------------------------ sets a bit in op1 *)
    | BitTestComplement (op1, op2) 
    | BitTestAndSet (op1, op2)
    | BitTestReset (op1, op2) ->
      let floc = get_floc loc in
      let (lhs, lhsCmds) = op1#to_lhs floc in
      let cfVar = env#mk_flag_variable (X86Flag CFlag) in
      let cmds = floc#get_abstract_commands lhs	~size:(int_constant_expr op1#size) () in
      let cfAbstract = ABSTRACT_VARS [ cfVar ] in
      let cmds = lhsCmds @ [ cfAbstract ] @ cmds in
      default cmds

    (* stack operations *)
    (* ------------------------------------------------- esp = esp - 4 ; mem[esp] = op *)
    (* ESP <- (ESP - 4); 
         IF (SRC is FS or GS) THEN
            TEMP = ZeroExtend32(SRC);
         ELSE IF (SRC is IMMEDIATE) THEN
            TEMP = SignExtend32(SRC); FI; 
         ELSE
            TEMP = SRC; FI;
         SS:ESP <- TEMP;
    *)
    (* Compute the stackLhs with an offset of -4 to account for the value of Esp at the
       location of the invariant, at the start of the instruction *)
    | Push (size,op) ->
      let floc = get_floc loc in
      let rhs = op#to_expr floc in
      let espRhs = env#mk_cpu_register_variable Esp in
      let (espLhs, espLhsCommands) = (esp_r WR)#to_lhs floc in
      let stackOperand = esp_deref ~with_offset:(-4) WR in
      let (stackLhs, stackLhsCommands) = stackOperand#to_lhs floc in
      let opsize = num_constant_expr (mkNumerical size) in
      let cmds1 = floc#get_assign_commands espLhs (XOp (XMinus, [ XVar espRhs ; opsize ] )) in
      let cmds2 = floc#get_assign_commands stackLhs  rhs in
      let argCmds = if op#is_function_argument then
	  let (callAddress, argIndex) = op#get_function_argument in
	  let bridgeVariable = env#mk_bridge_value callAddress argIndex in
	  if op#is_immediate_value then
	    let constant = op#get_immediate_value#to_numerical in
	    let _ = finfo#add_constant bridgeVariable constant in
	    []
	  else
	    floc#get_assign_commands bridgeVariable rhs
	else
	  [] in
      let cmds = espLhsCommands @ stackLhsCommands @ argCmds @ cmds1 @ cmds2 in
      let _ = (* inform function-info if this instruction saves a register *)
	if op#is_register then
	  let var = env#mk_cpu_register_variable op#get_cpureg in
	  if floc#has_initial_value var then
	    finfo#save_register floc#cia (CPURegister op#get_cpureg) in
      default cmds

    (* ------------------------------------------------------------ load flags into AH *)
    | LoadFlags ->
      let floc = get_floc loc in
      let (lhs,lhsCmds) = (ah_r WR)#to_lhs floc in
      let cmds = floc#get_abstract_commands lhs () in
      default (lhsCmds @ cmds)

    (* --------------------------------------------- esp = esp - 4 ; mem[esp] = eflags *)
    | PushFlags ->
      let floc = get_floc loc in
      let espRhs = env#mk_cpu_register_variable Esp in
      let (espLhs, espLhsCommands) = (esp_r WR)#to_lhs floc in
      let stackOperand = esp_deref ~with_offset:(-4) WR in
      let (stackLhs, stackLhsCommands) = stackOperand#to_lhs floc in
      let four = int_constant_expr 4 in
      let cmds1 = floc#get_assign_commands espLhs (XOp (XMinus, [ XVar espRhs ; four ] )) in
      let cmds2 = floc#get_abstract_commands stackLhs () in
      let cmds = espLhsCommands @ stackLhsCommands @ cmds1 @ cmds2  in
      default cmds

    (* ------------------------------------------- esp = esp - 32 ; push all registers *)
    | PushRegisters ->
      let floc = get_floc loc in
      let espRhs = env#mk_cpu_register_variable Esp in
      let (espLhs, espLhsCmds) = (esp_r WR)#to_lhs floc in
      let regs = [ Eax ; Ecx ; Edx ; Ebx ; Esp ; Ebp ; Esi ; Edi ] in
      let regRhss = List.map env#mk_cpu_register_variable regs in
      let stLhss = List.mapi (fun i _ ->
	let op = esp_deref ~with_offset:((-4)*(i+1)) WR in
	op#to_lhs floc) regs in
      let decr = int_constant_expr 32 in
      let espCmds = floc#get_assign_commands espLhs (XOp (XMinus, [ XVar espRhs ; decr ])) in
      let regCmds = List.map2 
	(fun lhs rhs -> floc#get_assign_commands lhs rhs) 
	(List.map fst stLhss) (List.map (fun v -> XVar v) regRhss) in
      let cmds = espLhsCmds @ (List.concat (List.map snd stLhss)) @ espCmds @ 
	(List.concat regCmds) in
      default cmds

    (* ---------------------------------------- op = mem[esp] ; esp = esp + 4 *)
    | Pop (size,op) ->
      let floc = get_floc loc in
      let (lhs, lhsCmds) = op#to_lhs floc in
      let espRhs = env#mk_cpu_register_variable Esp in
      let (espLhs, espLhsCommands) = (esp_r WR)#to_lhs floc in
      let stackRhs = (esp_deref RD)#to_variable floc in
      let opsize = int_constant_expr size in
      let cmds1 = floc#get_assign_commands lhs (XVar stackRhs) in
      let cmds2 =
        floc#get_assign_commands espLhs (XOp (XPlus, [XVar espRhs; opsize ])) in
      let cmds = espLhsCommands @ lhsCmds @ cmds1 @ cmds2 in
      let _ =   (* inform function-info if this instruction restores a register *)
	if op#is_register then 
	  if inv#are_equal stackRhs 
	    (env#mk_initial_register_value (CPURegister op#get_cpureg)) then
	    finfo#restore_register floc#cia (CPURegister op#get_cpureg) in
      default cmds

    (* ------------------------------------- flags = mem[esp] ; esp = esp + 4 *)
    | PopFlags ->
      let floc = get_floc loc in
      let espRhs = env#mk_cpu_register_variable Esp in
      let (espLhs, espLhsCommands) = (esp_r WR)#to_lhs floc in
      let four = int_constant_expr 4 in
      let popCmds =
        floc#get_assign_commands espLhs (XOp (XPlus, [XVar espRhs; four])) in
      let ofVar = env#mk_flag_variable (X86Flag OFlag) in
      let cfVar = env#mk_flag_variable (X86Flag CFlag) in
      let zfVar = env#mk_flag_variable (X86Flag ZFlag) in
      let sfVar = env#mk_flag_variable (X86Flag SFlag) in
      let pfVar = env#mk_flag_variable (X86Flag PFlag) in
      let flagCmd = ABSTRACT_VARS [ofVar; cfVar; zfVar; sfVar; pfVar] in
      let cmds = espLhsCommands @ popCmds @ [flagCmd] in
      default cmds

    (* --------------------------------------- pop registers ; esp = esp + 32 *)
    (* Esp is not being reloaded from the stack                               *)
    | PopRegisters ->
      let floc = get_floc loc in
      let espRhs = env#mk_cpu_register_variable Esp in
      let (espLhs, espLhsCmds) = (esp_r WR)#to_lhs floc in
      let incr = int_constant_expr 32 in
      let regs2 = List.rev [ Eax ; Ecx ; Edx ; Ebx ] in
      let regs1 = List.rev [ Ebp ; Esi ; Edi ] in
      let regVars1 = List.map env#mk_cpu_register_variable regs1 in
      let regVars2 = List.map env#mk_cpu_register_variable regs2 in
      let stRhs1 = List.mapi 
	(fun i _ -> (esp_deref ~with_offset:(4*i) RD)#to_expr floc) regs1 in
      let stRhs2 = List.mapi
	(fun i _ -> (esp_deref ~with_offset:((4*i) + 16) RD)#to_expr floc) regs2 in
      let espCmds = floc#get_assign_commands espLhs (XOp (XPlus, [ XVar espRhs ; incr ])) in
      let regCmds1 = List.map2 
	(fun lhs rhs -> floc#get_assign_commands lhs rhs) regVars1 stRhs1 in
      let regCmds2 = List.map2 
	(fun lhs rhs -> floc#get_assign_commands lhs rhs) regVars2 stRhs2 in
      let cmds = espLhsCmds  @ espCmds @ (List.concat regCmds1) @ (List.concat regCmds2) in
      default cmds
	
    (* ---------------------------------------------------------------------------- setcc op *)
    (* sets the operand to zero or one depending on the status bit in the eflags register    *)
    | Setcc (_, op) ->
      let floc = get_floc loc in
      let size = int_constant_expr 1 in
      let (lhs, lhsCmds) = op#to_lhs ~size:1 floc in
      let zCmds = floc#get_assign_commands lhs ~size zero_constant_expr in
      let oCmds = floc#get_assign_commands lhs ~size one_constant_expr in
      let branch = BRANCH [ LF.mkCode zCmds ; LF.mkCode oCmds ] in
      default (lhsCmds @ [ branch ])

    (* --------------------------------------------------------------- CF := 1 *)
    | SetCF ->
      let cfVar = env#mk_flag_variable (X86Flag CFlag) in
      let cmd = ASSIGN_NUM (cfVar, NUM numerical_one) in
      default [ cmd ]

    (* -------------------------------------------------------------- DF := 1 *)
    | SetDF ->
      let dfVar = env#mk_flag_variable (X86Flag DFlag) in
      let cmd = ASSIGN_NUM (dfVar, NUM numerical_one) in
      default [ cmd ]

    (* -------------------------------------------------------------- IF := 1 *)
    | SetInterruptFlag ->
      let ifVar = env#mk_flag_variable (X86Flag IFlag) in
      let cmd = ASSIGN_NUM (ifVar, NUM numerical_one) in
      default [ cmd ]
	
    (* -------------------------------------------------------------- DF := 0 *)
    | ClearDF ->
      let dfVar = env#mk_flag_variable (X86Flag DFlag) in
      let cmd = ASSIGN_NUM (dfVar, NUM numerical_zero) in
      default [ cmd ]

    (* -------------------------------------------------------------- CF := 0 *)
    | ClearCF ->
      let cfVar = env#mk_flag_variable (X86Flag CFlag) in
      let cmd = ASSIGN_NUM (cfVar, NUM numerical_zero) in
      default [ cmd ]
	
    (* ------------------------ ---------------------------------- CF := 1-CF *)
    | ComplementCF ->
      let cfVar = env#mk_flag_variable (X86Flag DFlag) in
      let one = env#request_num_constant numerical_one in
      let cmd = ASSIGN_NUM (cfVar, MINUS (one, cfVar)) in
      default [ cmd ]
	
    (* -------------------------------------------------- store AH into flags *)
    | StoreFlags ->
      let ofVar = env#mk_flag_variable (X86Flag OFlag) in
      let cfVar = env#mk_flag_variable (X86Flag CFlag) in
      let zfVar = env#mk_flag_variable (X86Flag ZFlag) in
      let sfVar = env#mk_flag_variable (X86Flag SFlag) in
      let pfVar = env#mk_flag_variable (X86Flag PFlag) in
      default [ABSTRACT_VARS [ofVar; cfVar; zfVar; sfVar; pfVar]]

    (* special instructions *)
    (* --------------------------------------------------- cpu identification *)
    | Cpuid ->                                                    
      let eax = env#mk_cpu_register_variable Eax in
      let ebx = env#mk_cpu_register_variable Ebx in
      let ecx = env#mk_cpu_register_variable Ecx in
      let edx = env#mk_cpu_register_variable Edx in
      let idA = env#mk_runtime_constant "cpuId_A" in
      let idB = env#mk_runtime_constant "cpuId_B" in
      let idC = env#mk_runtime_constant "cpuId_C" in
      let idD = env#mk_runtime_constant "cpuId_D" in
      let cmds =
        [ASSIGN_NUM (eax, NUM_VAR idA);
         ASSIGN_NUM (ebx, NUM_VAR idB);
	 ASSIGN_NUM (ecx, NUM_VAR idC);
         ASSIGN_NUM (edx, NUM_VAR idD)] in
      default cmds
	
    (* return instruction is used as an indirect jump *)
    | Ret None | BndRet None when system_info#is_goto_return loc#i ->
      let floc = get_floc loc in
      let espRhs = env#mk_cpu_register_variable Esp in
      let (espLhs, espLhsCommands) = (esp_r WR)#to_lhs floc in
      let four = int_constant_expr 4 in
      let cmds =
        floc#get_assign_commands espLhs (XOp (XPlus, [XVar espRhs; four])) in
      let cmds = espLhsCommands @ cmds in
      default cmds

    | Ret adj when (not (is_iaddress loc#ci)) ->
       let floc = get_floc loc in
       let espRhs = env#mk_cpu_register_variable Esp in
       let (espLhs, espLhsCommands) = (esp_r WR)#to_lhs floc in
       let adj =
         match adj with
         | None -> int_constant_expr 4
         | Some a -> int_constant_expr (4 + a) in
       let cmds =
         floc#get_assign_commands espLhs (XOp (XPlus, [XVar espRhs; adj])) in
       let cmds = espLhsCommands @ cmds in
       let _ =
         chlog#add
           "inline-return"
           (LBLOCK [pretty_print_list cmds cmd_to_pretty "[" ", " "]" ]) in
       default cmds       

    (* different control flow *)
    | RepzRet | Ret _ | BndRet _ ->
      let floc = get_floc loc in
      let _ = floc#record_return_value in
      let transaction = package_transaction finfo block_label 
	(commands @ [ invariantOperation ]) in
      let nodes = [ (block_label, [transaction]) ] in
      let edges = [ (block_label, exit_label) ] in
      (nodes, edges, [])
	
    | PackedAlignRight (dst,_,_)
    | PackedExtract (_,dst,_,_)
    | PackedInsert (_,dst,_,_)
    | PackedShift (_,_,dst,_)
    | PackedCompare (_,_,dst,_)
    | PackedAdd (_,_,_,dst,_)
    | PackedSubtract (_,_,_,dst,_)
    | PackedMultiply (_,dst,_)
    | PackedRoundScalarDouble(dst,_,_)
    | PackedOp (_,_,dst,_) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (dstLhs,dstLhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_assign_commands dstLhs ~size (XConst XRandom) in
      default (dstLhsCmds @ cmds)

    (* if an index is generated, abstract ecx *)
    | PackedCompareString (_,true,_,_,_) ->
      let floc = get_floc loc in
      let lhs = ecx_r WR in
      let (dstLhs,dstLhsCmds) = lhs#to_lhs floc in
      let cmds = floc#get_assign_commands dstLhs (XConst XRandom) in
      default (dstLhsCmds @ cmds)
	
    | VPackedAdd (_,_,_,dst,_,_)
    | VPackedOp (_,_,dst,_,_)
    | VPackedShift (_,_,dst,_,_)
    | VPackedShuffle (_,dst,_,_)
    | VMovdq (_,dst,_) ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (lhs,lhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_assign_commands lhs ~size (XConst XRandom) in
      default (lhsCmds @ cmds)
	
    (* operations on xmm registers *)
    | Movdq (_, dst,_)  ->
      let floc = get_floc loc in
      let size = int_constant_expr dst#size in
      let (lhs, lhsCmds) = dst#to_lhs ~size:dst#size floc in
      let cmds = floc#get_assign_commands lhs ~size (XConst XRandom) in
      default (lhsCmds @ cmds)
	
    (* floating point operations that write to memory *)
    | Fbstp dst
    | FSaveState (_,dst)
    | FXSave dst
    | FStore (_,_,_,dst)   (* TBD: incorporate the width *)
    | FStoreState (_,_,_,dst) ->
      let floc = get_floc loc in
      let (lhs, lhsCmds) = dst#to_lhs floc in
      let cmds = floc#get_assign_commands lhs (XConst XRandom) in
      default (lhsCmds @ cmds)
	
    (* miscellaneous *)
    | ReadTimeStampCounter (* read time stamp counter into Edx:Eax *)
    | XGetBV -> (* read value of control register into Edx:Eax ; could assert Ecx = 0 here *)
      let eax = env#mk_cpu_register_variable Eax in
      let edx = env#mk_cpu_register_variable Edx in
      let cmds = [ ABSTRACT_VARS [ eax ; edx ] ] in 
      default cmds
	
    | RdRandomize op | Stmxcsr op ->
      let floc = get_floc loc in
      let size = int_constant_expr op#size in
      let (lhs, lhsCmds) = op#to_lhs floc in
      let cmds = floc#get_abstract_commands lhs ~size () in
      default (lhsCmds @ cmds)

    (* SIDT :  Stores the content the interrupt descriptor table 
       register (IDTR) in the destination operand. The destination 
       operand specifies a 6-byte memory location. *)
    | StoreIDTR op ->
       let floc = get_floc loc in
       let (lhs, lhsCmds) = op#to_lhs floc in
       let cmds = floc#get_abstract_commands lhs ~size:(int_constant_expr 6) () in
       default (lhsCmds @ cmds)
	
     (* the destination operation is an xmm register *)
    | AESDecrypt _ | AESDecryptLast _ | AESEncrypt _ | AESEncryptLast _ | AESInvMix _ 
    | AESKeyGenAssist _ 
    | VZeroAll -> default []
      
    (* the destination operand is always an FPU data register *)
    | FLoadConstant _ | FLoad _ | FStackOp _
    | Fadd _ | Fsub _ | Fsubr _ | Fmul _ | Fdiv _ | Fdivr _
    | Fcom _ | Fucom _ | Fcomi _
    | Finit _ | Fclex _
    | FRestoreState _
    | Fxch _  -> default []

    (* read memory only *)
    | FXRestore _ -> default []
    | Ldmxcsr _ -> default []

    (* the destination operand is always an xmm register *)
    | FXmmOp _ | FXmmOpEx _ -> default []

    (* these instructions have no effect on the state maintained *)
    | ClearInterruptFlag | ClearTaskSwitchedFlag | Prefetch _ | UndefinedInstruction
    | Test _ | Cmp _ -> default []
    | Halt | Pause | Wait -> default []

    (* binary coded decimal instructions; semantics to be added; abstracting for now *)
    | AAA | AAD _ | AAM _ | AAS | DAA | DAS ->
      let floc = get_floc loc in
      let (lhs, lhsCmds) = (eax_r RW)#to_lhs floc in
      let cmds = floc#get_abstract_commands lhs () in
      default (lhsCmds @ cmds)

    (* control-flow instructions are handled separately *)
    | DirectJmp _ | IndirectJmp _ | OpInvalid -> default []
    | _ ->
      begin
	add_unprocessed_instruction function_location instruction ;
	default []
      end

class assembly_function_translator_t (f:assembly_function_int) =
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
    let codePC = make_code_pc block in
    let blockLabel = make_code_label block#get_context_string in
    let rec aux commands =
      let (nodes,edges,newCommands) =
	try
	  translate_instruction
            ~function_location
            ~code_pc:codePC
            ~block_label:blockLabel 
	    ~exit_label
            ~commands
	with
	| Invocation_error s ->
	  begin
	    ch_error_log#add "translate instruction"
	      (LBLOCK [ STR s ; STR ": " ; function_location#toPretty ; STR " , " ;
			blockLabel#toPretty ]) ;
	    raise (BCH_failure (LBLOCK [ STR s ; STR ": " ; function_location#toPretty ]))
	  end
        | BCH_failure p ->
           begin
             ch_error_log#add "translate instruction"
               (LBLOCK [ p ; STR ": " ; function_location#toPretty ; STR " , " ;
                         blockLabel#toPretty ]) ;
             raise (BCH_failure (LBLOCK [ STR "Error in translating instruction: " ;
                                          function_location#toPretty ; STR ": " ; p ]))
           end in
      match nodes with
	[] -> 
	  if codePC#has_more_instructions then 
	    aux newCommands
	  else
	    let transaction = package_transaction finfo blockLabel newCommands in
	    let nodes = [ (blockLabel,  [transaction]) ] in
	    let edges = List.map 
	      (fun successor -> 
		let successorLabel = make_code_label successor in 
		(blockLabel, successorLabel)) codePC#get_block_successors in
	    (nodes, edges)
      | _ ->
	(nodes,edges) in
    let _ = finfo#env#start_transaction in
    let (nodes,edges) = aux [] in
    begin
      List.iter (fun (label,node) -> code_graph#add_node label node) nodes ;
      List.iter (fun (src,dst) -> code_graph#add_edge src dst) edges
    end

  method private get_entry_cmd =
    let env = finfo#env in
    let _ = env#start_transaction in
    let freeze_initial_register_value (reg:cpureg_t) =
      let regVar = env#mk_cpu_register_variable reg in
      let initVar = env#mk_initial_register_value (CPURegister reg) in
      ASSERT (EQ (regVar, initVar)) in
    let freeze_external_memory_values (v:variable_t) =
      let initVar = env#mk_initial_memory_value v in
      ASSERT (EQ (v, initVar)) in
    let rAsserts = List.map freeze_initial_register_value full_registers in
    let externalMemVars = env#get_external_memory_variables in
    let externalMemVars = List.filter env#has_constant_offset externalMemVars in
    let mAsserts = List.map freeze_external_memory_values externalMemVars in
    let esp0 = env#mk_initial_register_value (CPURegister Esp) in
    let _ = finfo#add_base_pointer esp0 in
    let unknown_scalar = env#mk_special_variable "unknown_scalar" in
    let initializeScalar =
      DOMAIN_OPERATION ( [ valueset_domain ], 
			 { op_name = new symbol_t "set_unknown_scalar" ;
			   op_args = [ ("unknown_scalar", unknown_scalar, WRITE) ] } ) in
    let initializeBasePointerOperations:cmd_t list =
      List.map (fun base ->
	DOMAIN_OPERATION ( [ valueset_domain ], 
			   { op_name = new symbol_t "initialize" ;
			     op_args = [ (base#getName#getBaseName, base, READ) ] } ))
	finfo#get_base_pointers in
    (* -------------------------------------------------------------------------
       The System V Intel386 ABI (chapter Registers and the Stack Frame) says that :
       The direction flag must be set to the "forward" (that is, zero) direction before 
       entry and upon exit from a function.
       ------------------------------------------------------------------------- *)
    let dfFlagCmd =
      let dfVar = finfo#env#mk_flag_variable (X86Flag DFlag) in
      ASSIGN_NUM (dfVar, NUM numerical_zero) in
    let constantAssigns = env#end_transaction in
    let cmds =
      constantAssigns
      @ rAsserts
      @ mAsserts
      @ [initializeScalar; dfFlagCmd]
      @ initializeBasePointerOperations  in
    TRANSACTION (new symbol_t "entry", LF.mkCode cmds, None)

  method initialize_types =
    let esp = finfo#env#mk_cpu_register_variable Esp in
    let espin = finfo#env#mk_initial_register_value (CPURegister Esp) in
    begin
      finfo#ftinv#add_function_var_fact esp t_voidptr ;
      finfo#ftinv#add_function_var_fact espin t_voidptr
    end      

  method translate =
    let faddr = f#get_address in
    let firstInstructionLabel = make_code_label function_location#ci in
    let entryLabel = make_code_label ~modifier:"entry" function_location#ci in
    let exitLabel  = make_code_label ~modifier:"exit"  function_location#ci in
    let procName = make_proc_name faddr in
    let _ = f#iter self#translate_block in
    let _ = self#initialize_types in
    let entry_cmd = self#get_entry_cmd in
    let scope = finfo#env#get_scope in
    let _ = code_graph#add_node entryLabel [ entry_cmd ] in
    let _ = code_graph#add_node exitLabel [ SKIP ] in
    let _ = code_graph#add_edge entryLabel firstInstructionLabel in
    let cfg = code_graph#to_cfg entryLabel exitLabel in
    let body = LF.mkCode [ CFG (procName, cfg) ] in
    let proc = LF.mkProcedure procName ~signature:[] ~bindings:[] ~scope ~body:body in
    (* let _ = pverbose [ proc#toPretty ; NL ] in *)
    chif_system#add_procedure proc

end

let rec translate_assembly_function (f:assembly_function_int) =
  let translator = new assembly_function_translator_t f in
  let faddr = f#get_address in
  try
    translator#translate
  with
  | CHFailure p
    | BCH_failure p -> 
     begin
       pr_debug [ STR "Failure in translation: " ; p ; NL ] ;
       raise (BCH_failure p)
     end
  | Request_function_retracing ->
    let _ = (get_function_info faddr)#env#end_transaction in
    let _ = chlog#add "retrace function" (LBLOCK [ faddr#toPretty ]) in
    let newF = trace_function faddr in
    begin
      (if newF#is_nonreturning then (get_function_info faddr)#set_nonreturning) ; 
      assembly_functions#replace_function newF ;
      translate_assembly_function newF 
    end
    

	
let rec translate_assembly_function_by_address (faddr:doubleword_int) =
  let f = assembly_functions#get_function_by_address faddr in
  try
    translate_assembly_function f
  with
    Request_function_retracing ->
      let _ = (get_function_info faddr)#env#end_transaction in
      let _ = chlog#add "retrace function" (LBLOCK [ faddr#toPretty ]) in
      let newF = trace_function faddr in
      begin
	(if newF#is_nonreturning then (get_function_info faddr)#set_nonreturning) ; 
	assembly_functions#replace_function newF ;
	translate_assembly_function_by_address faddr
      end
	
let translate_assembly_functions () =
  (* let msg = ref [] in *)
  let failedfunctions = ref [] in
  let functionfailure failuretype faddr p =
    begin
      ch_error_log#add "function failure"
	(LBLOCK [ STR failuretype ; STR ". " ; faddr#toPretty ; STR ": " ; p ]) ;
      failedfunctions := faddr :: !failedfunctions
    end in
  begin
    assembly_functions#itera (fun faddr f ->
      let _ = load_function_info faddr in
      try
	translate_assembly_function f
      with
      | Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
      | Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
      | Internal_error s -> functionfailure "Internal error" faddr (STR s)
      | Failure s -> functionfailure "Failure" faddr (STR s)
      | CHFailure p -> functionfailure "CHFailure" faddr p
      | BCH_failure p -> functionfailure "BCHFailure" faddr p) ;
    (match !failedfunctions with
    | [] -> ()
    | l -> chlog#add "failed functions"
      (LBLOCK (List.map (fun faddr -> LBLOCK [ faddr#toPretty ; NL ]) l)))
  end

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHPrettyUtil

(* bchlib *)
open BCHBasicTypes
open BCHFloc
open BCHLocation

(* bchlibmips32 *)
open BCHMIPSAssemblyInstruction
open BCHMIPSDictionary
open BCHMIPSDisassemblyUtils
open BCHMIPSOpcodeRecords
open BCHMIPSTypes


class mips_code_pc_t (block:mips_assembly_block_int):mips_code_pc_int =
object (self)

  val mutable instruction_list = block#get_instructions
  val mutable indelayslot = false
  val ctxtloc = block#get_location

  (* testloc, jumploc, then_successor_addr, else_successor_addr, testexpr *)
  val mutable conditional_successor_info = None


  method get_next_instruction =
    match instruction_list with
    | [] ->
       let msg =
         LBLOCK [
             block#get_first_address#toPretty;
             STR ": ";
	     STR "mips_code_pc#get_next_instruction"] in
       begin
	 ch_error_log#add "cfg error" msg;
	 raise (BCH_failure msg)
       end
    (* all conditional jump instructions have a delay slot *)
    | [h1; h2] when is_conditional_jump_instruction h1#get_opcode ->
       let jumpproxy =
         make_mips_assembly_instruction
           (h2#get_address#add_int 1) NoOperation "" in
       let jumploc = make_i_location ctxtloc (h2#get_address#add_int 1) in
       let testloc = make_i_location ctxtloc h1#get_address in
       let testfloc = get_floc testloc in
       let testexpr = get_conditional_jump_expr testfloc h1#get_opcode in
       let thenaddr = get_direct_jump_target_address h1#get_opcode in
       let elseaddr = h2#get_address#add_int 4 in
       let thenctxtaddr = (make_i_location ctxtloc thenaddr)#ci in
       let elsectxtaddr = (make_i_location ctxtloc elseaddr)#ci in
       begin
         conditional_successor_info <-
           Some (testloc,jumploc,thenctxtaddr,elsectxtaddr,testexpr) ;
         instruction_list <- [ h2 ; jumpproxy ] ;
         (testloc#ci,h1)
       end
    | h1::h2::tl when has_delay_slot h1#get_opcode && not indelayslot ->
       self#handle_delay_slot h1 h2 tl
    | h::tl ->
       let ctxtiaddr = (make_i_location ctxtloc h#get_address)#ci in
       begin
         indelayslot <- false ;
         instruction_list <- tl ;
         (ctxtiaddr,h)
       end

  method has_conditional_successor =
    match conditional_successor_info with Some _ -> true | _ -> false

  method get_conditional_successor_info =
    match conditional_successor_info with
    | Some i -> i
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "No conditional jump info found for block at address: ";
                 block#get_first_address#toPretty;
                 STR " in function ";
                 block#get_faddr#toPretty]))

  method private handle_delay_slot instr1 instr2 tl_instrs =
    let ctxtiaddr = (make_i_location ctxtloc instr2#get_address)#ci in
    let _ = indelayslot <-  true in
    let operands1 = get_operands_read instr1#get_opcode in
    let operands2 = get_operands_written instr2#get_opcode in
    let same_operand op1 op2 =
      (mips_dictionary#index_mips_opkind op1#get_kind) =
        (mips_dictionary#index_mips_opkind op2#get_kind) in
    let sharedoperands =
      List.filter (fun op1 ->
          List.exists (fun op2 -> same_operand op1 op2) operands2)
                  operands1 in
    match sharedoperands with
    | [] ->
       begin
         instruction_list <- instr1 :: tl_instrs;
         (ctxtiaddr,instr2)
       end
    | _ ->
       begin
         chlog#add
           "delay slot"
           (LBLOCK [
                instr1#get_address#toPretty;
                STR "  ";
                fixed_length_pretty
                  (STR (mips_opcode_to_string instr1#get_opcode)) 32;
                STR "; ";
                STR (mips_opcode_to_string instr2#get_opcode)]);
         indelayslot <- true;
         instruction_list <- instr1::tl_instrs;
         (ctxtiaddr, instr2)
       end


  method get_block_successors = block#get_successors

  method get_block_successor =
    match block#get_successors with
    | [successor] -> successor
    | []  ->
       let msg =
         LBLOCK [
             block#get_first_address#toPretty;
             STR ": ";
	     STR "get_block_successor has no successors"] in
      begin
	ch_error_log#add "cfg error" msg;
	raise (BCH_failure msg)
      end
    | _ ->
       let msg =
         LBLOCK [
             block#get_first_address#toPretty;
             STR ": ";
	     STR "block_successor has more than one successor"] in
      begin
	ch_error_log#add "cfg error" msg;
	raise (BCH_failure msg)
      end

  method get_false_branch_successor =
    match block#get_successors with
    | [false_branch; _] -> false_branch
    | _ ->
      let msg =
	LBLOCK [
            block#get_first_address#toPretty;
            NL;
            block#toPretty;
            NL;
	    INDENT (3, STR "get_false_branch_successor does not have two successors")] in
      begin
	ch_error_log#add "cfg error" msg;
	raise (BCH_failure msg)
      end

  method get_true_branch_successor =
    match block#get_successors with
    | [ _ ; true_branch ] -> true_branch
    | _ ->
      let msg =
	LBLOCK [
            block#get_first_address#toPretty;
            NL;
            block#toPretty;
            NL;
	    INDENT (3, STR "get_true_branch_successor does not have two successors")] in
      begin
	ch_error_log#add "cfg error" msg;
	raise (BCH_failure msg)
      end

  method has_more_instructions = match instruction_list with [] -> false | _ -> true
end


let make_mips_code_pc (block:mips_assembly_block_int) = new mips_code_pc_t block

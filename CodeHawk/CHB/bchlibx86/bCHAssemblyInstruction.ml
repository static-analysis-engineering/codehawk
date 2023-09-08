(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
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
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* xprlib *)
open Xprt
open XprTypes

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHLibTypes
open BCHSystemInfo

(* bchlibx86 *)
open BCHLibx86Types
open BCHX86Opcodes
open BCHX86OpcodeRecords


class assembly_instruction_t (virtual_address:doubleword_int) (opcode:opcode_t) 
  (instruction_bytes:string):assembly_instruction_int =
object (self)
  
  val mutable block_entry = false
  val mutable inlined_call = false
    
  method set_block_entry = 
    if not self#is_valid_instruction then
      let msg =
        LBLOCK [
            STR "Block entry not at instruction boundary: "; 
	    virtual_address#toPretty] in
      begin
	chlog#add "disassembly" msg;
	raise (BCH_failure msg)
      end
    else
      block_entry <- true

  method set_inlined_call = inlined_call <- true
	
  method is_block_entry = block_entry

  method is_inlined_call = inlined_call
    
  method get_address = virtual_address
    
  method get_opcode = opcode
    
  method get_instruction_bytes = instruction_bytes

  method get_bytes_ashexstring = byte_string_to_printed_string instruction_bytes
    
  method get_non_code_block = match opcode with (NotCode (Some b)) -> b | _ ->
    begin
      ch_error_log#add "invocation error" 
	(LBLOCK [ STR "No data block found at " ; virtual_address#toPretty ]) ;
      raise (Invocation_error "assembly_instruction#get_data_block")
    end
      
  method is_valid_instruction = match opcode with 
  | OpInvalid | NotCode _ | JumpTableEntry _ -> false 
  | _ -> true
    
  method is_direct_call = match opcode with DirectCall _ -> true | _ -> false
    
  method is_unknown = match opcode with Unknown | InconsistentInstr _ -> true | _ -> false
    
  method is_non_code_block = match opcode with (NotCode (Some _)) -> true | _ -> false
    
  method is_not_code = match opcode with NotCode _ -> true | _ -> false	

  method is_nop = is_nop_instruction opcode

  (* manipulation separate from the regular, modeled Esp operations *)
  method is_esp_manipulating floc =
    match opcode with
    | Pop _ | Push _ | PopFlags | PopRegisters | Enter _ | Leave -> false
    | Lea (dst,src) when                                     (* lea esp, (esp,,1) *)
	(dst#is_register && dst#get_cpureg = Esp) &&
	  (match src#get_kind with
	  | ScaledIndReg (Some Esp, None, 1,off) when off#equal numerical_zero -> true
	  | _ -> false) -> false
    | Mov (4,dst,src) when 
	(dst#is_register && dst#get_cpureg = Esp) &&
	  (src#is_register && src#get_cpureg = Ebp) -> false
    | _ ->
      let op_is_esp op = op#is_register && op#get_cpureg = Esp in
      let op_varies op = match (op#to_value floc) with
	| XConst (IntConst _) -> false | _ -> true in
      let ops = get_operands opcode in
      List.exists (fun op -> op_is_esp op && op#is_write) ops &&
	List.exists (fun op -> not (op_is_esp op) && op_varies op) ops
	
    
  method private is_locked = system_info#is_locked_instruction virtual_address	
    
  method toString = (if self#is_locked then "lock " else "") ^ (opcode_to_string opcode)
    
  method toPretty = LBLOCK [ STR self#toString ]

  method write_xml (node:xml_element_int) =
    let opc = self#get_opcode in
    let set = node#setAttribute in
    begin
      set "ia" self#get_address#to_hex_string ;
      set "opc" (opcode_to_string opc) ;
      set "bytes" (byte_string_to_spaced_string self#get_instruction_bytes)
    end
   
end
  
let make_assembly_instruction (va:doubleword_int) (opcode:opcode_t) (instructionBytes:string) =
  new assembly_instruction_t va opcode instructionBytes
    

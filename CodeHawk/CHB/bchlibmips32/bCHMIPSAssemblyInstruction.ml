(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* bchlibmips32 *)
open BCHMIPSTypes
open BCHMIPSOpcodeRecords

class mips_assembly_instruction_t (virtual_address:doubleword_int) (opcode:mips_opcode_t) 
  (instruction_bytes:string):mips_assembly_instruction_int =
object (self)
  
  val mutable block_entry = false
  val mutable delay_slot = false
  val mutable inlined_call = false
    
  method set_block_entry = block_entry <- true

  method set_inlined_call = inlined_call <- true

  method set_delay_slot = delay_slot <- true
	
  method is_block_entry = block_entry

  method is_delay_slot = delay_slot
    
  method get_address = virtual_address
    
  method get_opcode = opcode
    
  method get_instruction_bytes = instruction_bytes

  method get_bytes_ashexstring = byte_string_to_printed_string instruction_bytes
              
  method private is_locked = system_info#is_locked_instruction virtual_address

  method is_inlined_call = inlined_call
    
  method toString =
    (if self#is_locked then "lock " else "") ^ (mips_opcode_to_string opcode)
    
  method toPretty = LBLOCK [ STR self#toString ]

  method write_xml (node:xml_element_int) =
    let opc = self#get_opcode in
    let set = node#setAttribute in
    begin
      set "ia" self#get_address#to_hex_string ;
      set "opc" (mips_opcode_to_string opc) ;
      set "bytes" (byte_string_to_spaced_string self#get_instruction_bytes)
    end
   
end
  
let make_mips_assembly_instruction
      (va:doubleword_int)
      (opcode:mips_opcode_t)
      (instructionBytes:string) =
  new mips_assembly_instruction_t va opcode instructionBytes
    

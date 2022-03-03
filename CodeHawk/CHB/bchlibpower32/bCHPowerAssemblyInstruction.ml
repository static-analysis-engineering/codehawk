(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022 Aarno Labs LLC

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
open BCHFunctionData
open BCHLibTypes
open BCHSystemInfo

(* bchlibpower32 *)
open BCHPowerTypes


class power_assembly_instruction_t
        (vaddr: doubleword_int)
        (is_vle: bool)
        (opcode: power_opcode_t)
        (instruction_bytes: string): power_assembly_instruction_int =
object (self)
     
  val mutable block_entry = false
  val is_vle = is_vle

  method is_vle = is_vle

  method set_block_entry = block_entry <- true

  method is_block_entry = block_entry

  method get_opcode = opcode

  method get_address = vaddr

  method get_instruction_bytes = instruction_bytes

  method get_bytes_as_hexstring = byte_string_to_printed_string instruction_bytes

  method toString = "opcode"

  method toPretty = LBLOCK [STR self#toString]

  method write_xml (node: xml_element_int) = ()

end

                                               
let make_power_assembly_instruction
      (va: doubleword_int)
      (is_vle: bool)
      (opcode: power_opcode_t)
      (instructionbytes: string) =
  new power_assembly_instruction_t va is_vle opcode instructionbytes

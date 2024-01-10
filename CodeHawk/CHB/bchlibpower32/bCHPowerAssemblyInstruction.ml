(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2024  Aarno Labs LLC

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
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHLibTypes

(* bchlibpower32 *)
open BCHPowerTypes
open BCHPowerOpcodeRecords


class pwr_assembly_instruction_t
        (vaddr: doubleword_int)
        (is_vle: bool)
        (opcode: pwr_opcode_t)
        (instruction_bytes: string): pwr_assembly_instruction_int =
object (self)

  val mutable block_entry = false
  val mutable inlined_call = false
  val is_vle = is_vle

  method is_vle = is_vle

  method set_block_entry = block_entry <- true

  method set_inlined_call = inlined_call <- true

  method is_block_entry = block_entry

  method is_non_code_block =
    match opcode with
    | NotCode (Some _) -> true
    | _ -> false

  method is_valid_instruction: bool =
    match opcode with
    | OpInvalid -> false
    | NotCode _ -> false
    | _ -> true

  method is_not_code = match opcode with NotCode _ -> true | _ -> false

  method get_non_code_block =
    match opcode with
    | NotCode (Some b) -> b
    | _ ->
       let msg = (LBLOCK [STR "No data block found at "; vaddr#toPretty]) in
       begin
         ch_error_log#add "assembly instructions" msg;
         raise (BCH_failure msg)
       end

  method get_opcode = opcode

  method get_address = vaddr

  method get_instruction_bytes = instruction_bytes

  method get_bytes_as_hexstring = byte_string_to_printed_string instruction_bytes

  method toString = pwr_opcode_to_string opcode

  method toPretty = LBLOCK [STR self#toString]

  method write_xml (_node: xml_element_int) = ()

end


let make_pwr_assembly_instruction
      (va: doubleword_int)
      (is_vle: bool)
      (opcode: pwr_opcode_t)
      (instructionbytes: string) =
  new pwr_assembly_instruction_t va is_vle opcode instructionbytes

(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024  Aarno Labs LLC

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

(* chutil *)
open CHLogger
open CHPretty
open CHXmlDocument

(* bchlib *)
open BCHCPURegisters
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMOperand
open BCHARMTypes


module TR = CHTraceResult


class ldm_stm_sequence_t
        (ldmbase: arm_operand_int)
        (stmbase: arm_operand_int)
        (registers: arm_operand_int)
        (instrs: arm_assembly_instruction_int list)
        (anchor: doubleword_int): ldm_stm_sequence_int =
object (self)

  method srcreg = ldmbase

  method dstreg = stmbase

  method registers = registers

  method instrs = instrs

  method anchor = anchor

  method toCHIF = []

  method write_xml (node: xml_element_int) = ()

  method toString =
    "ldmstmcopy("
    ^ (armreg_to_string self#dstreg#get_register)
    ^ ", "
    ^ (armreg_to_string self#srcreg#get_register)
    ^ ", "
    ^ (string_of_int (4 * (List.length registers#get_register_list)))
    ^ ")"

  method toPretty = STR self#toString

end


let make_ldm_stm_sequence
      (ldmbase: arm_operand_int)
      (stmbase: arm_operand_int)
      (registers: arm_operand_int)
      (instrs: arm_assembly_instruction_int list)
      (anchor: doubleword_int): ldm_stm_sequence_int =
  new ldm_stm_sequence_t ldmbase stmbase registers instrs anchor



let create_ldm_stm_sequence
      (ch: pushback_stream_int)
      (stminstr: arm_assembly_instruction_int): ldm_stm_sequence_int option =
  let stmaddr = stminstr#get_address in
  match stminstr#get_opcode with
  | StoreMultipleIncrementAfter (_, _, stmbase, stmrl, _, _) ->
     let ldmaddr = stmaddr#add_int (-4) in
     (match TR.to_option (get_arm_assembly_instruction ldmaddr) with
      | Some ldminstr ->
         (match ldminstr#get_opcode with
          | LoadMultipleIncrementAfter (_, _, ldmbase, ldmrl, _) ->
             if equal_register_lists stmrl ldmrl then
               Some
                 (make_ldm_stm_sequence
                    ldmbase
                    stmbase
                    stmrl
                    [ldminstr; stminstr]
                    stmaddr)
             else
               None
          | _ -> None)
      | _ -> None)
  | _ -> None

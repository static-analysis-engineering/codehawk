(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026  Aarno Labs LLC

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
open CHPretty

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMTypes


module TR = CHTraceResult


class arm_wide_op_sequence_t
        (rdhi: arm_operand_int)
        (rdlo: arm_operand_int)
        (rnhi: arm_operand_int)
        (rnlo: arm_operand_int)
        (rmhi: arm_operand_int)
        (rmlo: arm_operand_int)
        (instrs: arm_assembly_instruction_int list)
        (anchor: doubleword_int): arm_wide_op_sequence_int =
  object (self)

    method rdhi = rdhi
    method rdlo = rdlo
    method rnhi = rnhi
    method rnlo = rnlo
    method rmhi = rmhi
    method rmlo = rmlo

    method instrs = instrs
    method anchor = anchor

    method toString =
      "wide op("
      ^ self#rdhi#toString ^ ", "
      ^ self#rdlo#toString ^ ", "
      ^ self#rnhi#toString ^ ", "
      ^ self#rnlo#toString ^ ", "
      ^ self#rmhi#toString ^ ", "
      ^ self#rmlo#toString ^ ")"

    method toPretty = STR self#toString

  end


let make_wide_op_sequence
      (rdhi: arm_operand_int)
      (rdlo: arm_operand_int)
      (rnhi: arm_operand_int)
      (rnlo: arm_operand_int)
      (rmhi: arm_operand_int)
      (rmlo: arm_operand_int)
      (instrs: arm_assembly_instruction_int list)
      (anchor: doubleword_int): arm_wide_op_sequence_int =
  new arm_wide_op_sequence_t rdhi rdlo rnhi rnlo rmhi rmlo instrs anchor


let create_arm_wide_op_sequence
      (_ch: pushback_stream_int)
      (carryinstr: arm_assembly_instruction_int): arm_wide_op_sequence_int option =
  let carryaddr = carryinstr#get_address in
  match carryinstr#get_opcode with
  | AddCarry (_, ACCAlways, rdhi, rnhi, rmhi, _) ->
     let addinstraddr = carryaddr#add_int (-4) in
     (match TR.to_option (get_arm_assembly_instruction addinstraddr) with
      | Some addinstr ->
         (match addinstr#get_opcode with
          | Add (true, ACCAlways, rdlo, rnlo, rmlo, _) ->
             let instrs = [addinstr; carryinstr] in
             Some (make_wide_op_sequence rdhi rdlo rnhi rnlo rmhi rmlo instrs carryaddr)
          | _ -> None)
      | _ -> None)
  | SubtractCarry (_, ACCAlways, rdhi, rnhi, rmhi, _) ->
     let subinstraddr = carryaddr#add_int (-4) in
     (match TR.to_option (get_arm_assembly_instruction subinstraddr) with
      | Some subinstr ->
         (match subinstr#get_opcode with
          | Subtract (true, ACCAlways, rdlo, rnlo, rmlo, _, _) ->
             let instrs = [subinstr; carryinstr] in
             Some (make_wide_op_sequence rdhi rdlo rnhi rnlo rmhi rmlo instrs carryaddr)
          | _ -> None)
      | _ -> None)
  | ReverseSubtractCarry (_, ACCAlways, rdhi, rnhi, rmhi) ->
     let revinstraddr = carryaddr#add_int (-4) in
     (match TR.to_option (get_arm_assembly_instruction revinstraddr) with
      | Some revinstr ->
         (match revinstr#get_opcode with
          | ReverseSubtract (true, ACCAlways, rdlo, rnlo, rmlo, _) ->
             let instrs = [revinstr; carryinstr] in
             Some (make_wide_op_sequence rdhi rdlo rnhi rnlo rmhi rmlo instrs carryaddr)
          | _ -> None)
      | _ -> None)
  | _ -> None

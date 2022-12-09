(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022      Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMTypes
open BCHDisassembleThumbInstruction


class thumb_it_sequence_t
        (kind: thumb_it_sequence_kind_t)
        (instrs: arm_assembly_instruction_int list)
        (anchor: doubleword_int): thumb_it_sequence_int =
object (self)

  method kind = kind

  method instrs = instrs

  method anchor = anchor

  method toCHIF = []

  method write_xml (node: xml_element_int) = ()

  method toPretty = STR "thumb-it-sequence"
end


let make_thumb_it_sequence
      (kind: thumb_it_sequence_kind_t)
      (instrs: arm_assembly_instruction_int list)
      (anchor: doubleword_int): thumb_it_sequence_int =
  new thumb_it_sequence_t kind instrs anchor


(*
   ITE  c                                   ITE  c
   MOV  Rx, #0x0   ->  Rx := !c     or      MOV  Rx, #0x1   ->  Rx := c
   MOV  Rx, #0x1                            MOV  Rx, #0x0
 *)
let is_ite_predicate_assignment
      (opcthen: arm_opcode_t) (opcelse: arm_opcode_t) =
  match (opcthen, opcelse) with
  | (Move (_, _, tr, thenop, _, _), Move (_, _, er, elseop, _, _))
     when
       (tr#is_register
        && er#is_register
        && tr#get_register = er#get_register
        && thenop#is_immediate
        && elseop#is_immediate
        && thenop#to_numerical#equal numerical_one
        && elseop#to_numerical#equal numerical_zero) ->
     Some tr
  | _ -> None


let disassemble_instruction (iaddr: doubleword_int) (ch: pushback_stream_int) =
  let instrpos = ch#pos in
  let bytes = ch#read_ui16 in
  let opcode =
    try
      disassemble_thumb_instruction ch iaddr bytes
    with
    | _ -> OpInvalid in
  let instrlen = ch#pos - instrpos in
  let instrbytes =
    fail_tvalue
      (trerror_record
         (STR "ThumbITSequence:disassemble_instruciton"))
      (ch#sub instrpos instrlen) in
  let instr = make_arm_assembly_instruction iaddr false opcode instrbytes in
  begin
    set_arm_assembly_instruction instr;
    (instr, instrlen)
  end


let create_thumb_it_sequence
      (ch: pushback_stream_int)
      (itinstr: arm_assembly_instruction_int): thumb_it_sequence_int option =
  let itiaddr0 = itinstr#get_address in
  match itinstr#get_opcode with
  | IfThen (c, xyz) when xyz = "E" ->
     let itiaddr1 = itiaddr0#add_int 2 in  (* There is only one IT encoding: T1: 2 bytes *)
     let (instr1, instrlen1) = disassemble_instruction itiaddr1 ch in
     let itiaddr2 = itiaddr1#add_int instrlen1 in
     let (instr2, instrlen2) = disassemble_instruction itiaddr2 ch in
     (match is_ite_predicate_assignment instr1#get_opcode instr2#get_opcode with
      | Some op ->
         Some
           (make_thumb_it_sequence
              (ITPredicateAssignment op) [itinstr; instr1; instr2] itiaddr0)
      | _ -> None)
  | _ -> None

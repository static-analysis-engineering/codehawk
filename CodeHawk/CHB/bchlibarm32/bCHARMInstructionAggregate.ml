(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2022-2024  Aarno Labs, LLC

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
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMJumptable
open BCHARMTypes
open BCHDisassembleARMInstruction
open BCHLoadStoreMultipleSequence
open BCHThumbITSequence


let arm_aggregate_kind_to_string (k: arm_aggregate_kind_t) =
  match k with
  | ARMJumptable jt ->
     "Jumptable at "
     ^ jt#start_address#to_hex_string
     ^ " with "
     ^ (string_of_int (List.length jt#target_addrs))
     ^ " target addresses"
  | ThumbITSequence it -> it#toString
  | LDMSTMSequence s -> s#toString


class arm_instruction_aggregate_t
        ~(kind: arm_aggregate_kind_t)
        ~(instrs: arm_assembly_instruction_int list)
        ~(entry: arm_assembly_instruction_int)
        ~(exitinstr: arm_assembly_instruction_int)
        ~(anchor: arm_assembly_instruction_int):
        arm_instruction_aggregate_int =
object (self)

  method kind = kind

  method instrs = instrs

  method addrs = List.map (fun i -> i#get_address) instrs

  method entry = entry

  method exitinstr = exitinstr

  method anchor = anchor

  method jumptable =
    match self#kind with
    | ARMJumptable jt -> jt
    | _ -> raise (BCH_failure (STR "Not a jumptable"))

  method it_sequence =
    match self#kind with
    | ThumbITSequence its -> its
    | _ -> raise (BCH_failure (STR "Not an it sequence"))

  method ldm_stm_sequence =
    match self#kind with
    | LDMSTMSequence s -> s
    | _ -> raise (BCH_failure (STR "Not an ldm-stm sequence"))

  method is_jumptable =
    match self#kind with
    | ARMJumptable _ -> true
    | _ -> false

  method is_it_sequence =
    match self#kind with
    | ThumbITSequence _ -> true
    | _ -> false

  method is_ldm_stm_sequence =
    match self#kind with
    | LDMSTMSequence _ -> true
    | _ -> false

  method write_xml (_node: xml_element_int) = ()

  method toCHIF (_faddr: doubleword_int) = []

  method toPretty =
    LBLOCK [
        STR "Aggregate of ";
        INT (List.length self#instrs);
        STR " instructions: ";
        STR (arm_aggregate_kind_to_string self#kind)]

end


let make_arm_instruction_aggregate
      ~(kind: arm_aggregate_kind_t)
      ~(instrs: arm_assembly_instruction_int list)
      ~(entry: arm_assembly_instruction_int)
      ~(exitinstr: arm_assembly_instruction_int)
      ~(anchor: arm_assembly_instruction_int ):
      arm_instruction_aggregate_int =
  let agg =
    new arm_instruction_aggregate_t ~kind ~instrs ~entry ~exitinstr ~anchor in
  begin
    chlog#add "aggregate instruction" agg#toPretty;
    agg
  end


let make_arm_jumptable_aggregate
      ~(jt: arm_jumptable_int)
      ~(instrs: arm_assembly_instruction_int list)
      ~(entry: arm_assembly_instruction_int)
      ~(exitinstr: arm_assembly_instruction_int)
      ~(anchor: arm_assembly_instruction_int):
      arm_instruction_aggregate_int =
  let kind = ARMJumptable jt in
  make_arm_instruction_aggregate ~kind ~instrs ~entry ~exitinstr ~anchor


let make_it_sequence_aggregate
      ~(its: thumb_it_sequence_int)
      ~(instrs: arm_assembly_instruction_int list)
      ~(entry: arm_assembly_instruction_int)
      ~(exitinstr: arm_assembly_instruction_int)
      ~(anchor: arm_assembly_instruction_int):
      arm_instruction_aggregate_int =
  let kind = ThumbITSequence its in
  make_arm_instruction_aggregate ~kind ~instrs ~entry ~exitinstr ~anchor


let make_ldm_stm_sequence_aggregate
      (ldmstmseq: ldm_stm_sequence_int): arm_instruction_aggregate_int =
  let kind = LDMSTMSequence ldmstmseq in
  make_arm_instruction_aggregate
    ~kind
    ~instrs:ldmstmseq#instrs
    ~entry:(List.hd ldmstmseq#instrs)
    ~exitinstr:(List.hd (List.tl ldmstmseq#instrs))
    ~anchor:(List.hd (List.tl ldmstmseq#instrs))


let disassemble_arm_instructions
      (ch: pushback_stream_int) (iaddr: doubleword_int) (n: int) =
  for _i = 1 to n do
    let instrbytes = ch#read_doubleword in
    let opcode = disassemble_arm_instruction ch iaddr instrbytes in
    let pos = ch#pos in
    let instrbytes = ch#sub (pos - 4) 4 in
    let instr = make_arm_assembly_instruction iaddr true opcode instrbytes in
    set_arm_assembly_instruction instr
  done


let identify_jumptable
      (ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int list * arm_jumptable_int) option =
  match instr#get_opcode with
  | TableBranchByte _ | TableBranchHalfword _ ->
     create_arm_table_branch ch instr
  | LoadRegister (ACCAlways, dst, _, _, _, true)
       when dst#is_register && dst#get_register = ARPC ->
       create_arm_ldr_jumptable ch instr
  | LoadRegister (ACCNotUnsignedHigher, dst, _, _, _, false)
       when dst#is_register && dst#get_register = ARPC ->
     let iaddr = instr#get_address in
     begin
       disassemble_arm_instructions ch (iaddr#add_int 4) 1;
       create_arm_ldrls_jumptable ch instr
     end
  | Add (_, ACCAlways, rd, rn, _, false)
       when rd#is_pc_register && rn#is_pc_register ->
     create_arm_add_pc_jumptable ch instr
  | BranchExchange (ACCAlways, regop) when regop#is_register ->
     create_arm_bx_jumptable ch instr
  | _ -> None


let identify_it_sequence
      (ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int): thumb_it_sequence_int option =
    match instr#get_opcode with
    | IfThen (_c, xyz) when (xyz = "E" || xyz = "") ->
       create_thumb_it_sequence ch instr
    | _ -> None


let identify_ldmstm_sequence
      (ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int): ldm_stm_sequence_int option =
  match instr#get_opcode with
  | StoreMultipleIncrementAfter (_, _, _, rl, _, _)
       when List.length rl#get_register_list > 1 ->
     create_ldm_stm_sequence ch instr
  | _ -> None
  

let identify_arm_aggregate
      (ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int):
      arm_instruction_aggregate_int option =
  match identify_jumptable ch instr with
  | Some (instrs, jt) ->
     let anchor = List.nth instrs ((List.length instrs) - 1) in
     let entry = List.hd instrs in
     let exitinstr = anchor in
     Some (make_arm_jumptable_aggregate ~jt ~instrs ~entry ~exitinstr ~anchor)
  | _ ->
     match identify_it_sequence ch instr with
     | Some its ->
        let instrs = its#instrs in
        let entry = List.hd instrs in
        let exitinstr = List.hd (List.rev instrs) in
        Some (make_it_sequence_aggregate
                ~its ~instrs ~entry ~exitinstr ~anchor:entry)
     | _ ->
        match identify_ldmstm_sequence ch instr with
        | Some ldmstmseq ->
           Some (make_ldm_stm_sequence_aggregate ldmstmseq)
        | _ -> None

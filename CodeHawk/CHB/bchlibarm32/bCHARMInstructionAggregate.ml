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
open BCHARMDisassemblyUtils
open BCHARMJumptable
open BCHARMTypes
open BCHDisassembleARMInstruction
open BCHLoadStoreMultipleSequence
open BCHThumbITSequence


module TR = CHTraceResult


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
  | PseudoLDRSB (i1, _, _) -> "Pseudo LDRSB at " ^ i1#get_address#to_hex_string
  | PseudoLDRSH (i1, _, _) -> "Pseudo LDRSH at " ^ i1#get_address#to_hex_string
  | ARMPredicateAssignment (inverse, op) ->
     let inv = if inverse then " (inverse)" else "" in
     "predicate assignment to " ^ op#toString ^ inv
  | BXCall (_, i2) -> "BXCall at " ^ i2#get_address#to_hex_string


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

  method is_bx_call =
    match self#kind with
    | BXCall _ -> true
    | _ -> false

  method is_pseudo_ldrsh =
    match self#kind with
    | PseudoLDRSH _ -> true
    | _ -> false

  method is_pseudo_ldrsb =
    match self#kind with
    | PseudoLDRSH _ -> true
    | _ -> false

  method is_predicate_assign =
    match self#kind with
    | ARMPredicateAssignment _ -> true
    | _ -> false

  method write_xml (_node: xml_element_int) = ()

  method toCHIF (_faddr: doubleword_int) = []

  method toPretty =
    LBLOCK [
        STR "Aggregate of ";
        INT (List.length self#instrs);
        STR " with anchor ";
        self#anchor#get_address#toPretty;
        STR " ";
        self#anchor#toPretty;
        STR ": ";
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


let make_bx_call_aggregate
      (movinstr: arm_assembly_instruction_int)
      (bxinstr: arm_assembly_instruction_int): arm_instruction_aggregate_int =
  let kind = BXCall (movinstr, bxinstr) in
  make_arm_instruction_aggregate
    ~kind
    ~instrs:[movinstr; bxinstr]
    ~entry:movinstr
    ~exitinstr:bxinstr
    ~anchor:bxinstr


let make_pseudo_ldrsh_aggregate
      (ldrhinstr: arm_assembly_instruction_int)
      (lslinstr: arm_assembly_instruction_int)
      (asrinstr: arm_assembly_instruction_int): arm_instruction_aggregate_int =
  let kind = PseudoLDRSH (ldrhinstr, lslinstr, asrinstr) in
  make_arm_instruction_aggregate
    ~kind
    ~instrs:[ldrhinstr; lslinstr; asrinstr]
    ~entry:ldrhinstr
    ~exitinstr:asrinstr
    ~anchor:asrinstr


let make_pseudo_ldrsb_aggregate
      (ldrbinstr: arm_assembly_instruction_int)
      (lslinstr: arm_assembly_instruction_int)
      (asrinstr: arm_assembly_instruction_int): arm_instruction_aggregate_int =
  let kind = PseudoLDRSB (ldrbinstr, lslinstr, asrinstr) in
  make_arm_instruction_aggregate
    ~kind
    ~instrs:[ldrbinstr; lslinstr; asrinstr]
    ~entry:ldrbinstr
    ~exitinstr:asrinstr
    ~anchor:asrinstr


let make_predassign_aggregate
      (inverse: bool)
      (mov1: arm_assembly_instruction_int)
      (mov2: arm_assembly_instruction_int)
      (dstop: arm_operand_int): arm_instruction_aggregate_int =
  let kind = ARMPredicateAssignment (inverse, dstop) in
  make_arm_instruction_aggregate
    ~kind
    ~instrs:[mov1; mov2]
    ~entry:mov1
    ~exitinstr:mov2
    ~anchor:mov2


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
  | Add (_, ACCNotUnsignedHigher, rd, rn, _, false)
       when rd#is_pc_register && rn#is_pc_register ->
     create_addls_pc_jumptable ch instr
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


(* format of BX-Call (in ARM)

   An indirect jump combined with a MOV of the PC into the LR converts
   into an indirect call (because PC holds the instruction-address + 8)

   MOV LR, PC
   BX Rx
 *)
let identify_bx_call
      (ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int * arm_assembly_instruction_int) option =
  let disassemble (iaddr: doubleword_int) =
    let instrpos = ch#pos in
    let bytes = ch#read_doubleword in
    let opcode =
      try
        disassemble_arm_instruction ch iaddr bytes
      with
      | _ ->
         let _ =
           chlog#add
             "bx-call disassemble-instruction"
             (LBLOCK [iaddr#toPretty]) in
         OpInvalid in
    let instrbytes = ch#sub instrpos 4 in
    let instr = make_arm_assembly_instruction iaddr true opcode instrbytes in
    begin
      set_arm_assembly_instruction instr;
      instr
    end in
  match instr#get_opcode with
  | Move (_, ACCAlways, dst, src, _, _)
       when src#is_register
            && dst#get_register = ARLR
            && src#get_register = ARPC ->
     begin
       let bxinstr = disassemble (instr#get_address#add_int 4) in
       match bxinstr#get_opcode with
       | BranchExchange (ACCAlways, op) when op#is_register ->
          Some (instr, bxinstr)
       | _ -> None
     end
  | _ -> None


(* format of pseudo LDRSH (in ARM)

   An LDRH combined with LSL 16, ASR 16 converts into (effectively) an
   LDRSH:

   LDRH Rx, mem
   LSL  Rx, Rx, #0x10
   ASR  Rx, Rx, #0x10
 *)
let identify_pseudo_ldrsh
      (_ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int
       * arm_assembly_instruction_int
       * arm_assembly_instruction_int) option =
  let sixteen = CHNumerical.mkNumerical 16 in
  match instr#get_opcode with
  | ArithmeticShiftRight (_, ACCAlways, rd, rs, imm, _)
       when imm#is_immediate
            && imm#to_numerical#equal sixteen
            && (rd#get_register = rs#get_register) ->
     let addr = instr#get_address in
     let lslinstr_r = get_arm_assembly_instruction (addr#add_int (-4)) in
     let ldrhinstr_r = get_arm_assembly_instruction (addr#add_int (-8)) in
     (match (TR.to_option lslinstr_r, TR.to_option ldrhinstr_r) with
      | (Some lslinstr, Some ldrhinstr) ->
         if
           (match lslinstr#get_opcode with
            | LogicalShiftLeft (_, ACCAlways, rd1, rs1, imm, _)
                 when imm#is_immediate
                      && imm#to_numerical#equal sixteen
                      && (rd1#get_register = rd#get_register)
                      && (rs1#get_register = rd#get_register) -> true
            | _ -> false)
           && (match ldrhinstr#get_opcode with
               | LoadRegisterHalfword (ACCAlways, rd2, _, _, _, _)
                    when rd2#get_register = rd#get_register -> true
               | _ -> false)
         then
           Some (TR.tget_ok ldrhinstr_r, TR.tget_ok lslinstr_r, instr)
         else
           None
      | _ -> None)
  | _ -> None


(* format of pseudo LDRSB (in ARM)

   An LDRH combined with LSL 16, ASR 16 converts into (effectively) an
   LDRSH:

   LDRB Rx, mem
   LSL  Rx, Rx, #0x18
   ASR  Rx, Rx, #0x18
 *)
let identify_pseudo_ldrsb
      (_ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int):
      (arm_assembly_instruction_int
       * arm_assembly_instruction_int
       * arm_assembly_instruction_int) option =
  let twentyfour = CHNumerical.mkNumerical 24 in
  match instr#get_opcode with
  | ArithmeticShiftRight (_, ACCAlways, rd, rs, imm, _)
       when imm#is_immediate
            && imm#to_numerical#equal twentyfour
            && (rd#get_register = rs#get_register) ->
     let addr = instr#get_address in
     let lslinstr_r = get_arm_assembly_instruction (addr#add_int (-4)) in
     let ldrbinstr_r = get_arm_assembly_instruction (addr#add_int (-8)) in
     (match (TR.to_option lslinstr_r, TR.to_option ldrbinstr_r) with
      | (Some lslinstr, Some ldrbinstr) ->
         if
           (match lslinstr#get_opcode with
            | LogicalShiftLeft (_, ACCAlways, rd1, rs1, imm, _)
                 when imm#is_immediate
                      && imm#to_numerical#equal twentyfour
                      && (rd1#get_register = rd#get_register)
                      && (rs1#get_register = rd#get_register) -> true
            | _ -> false)
           && (match ldrbinstr#get_opcode with
               | LoadRegisterByte (ACCAlways, rd2, _, _, _, _)
                    when rd2#get_register = rd#get_register -> true
               | _ -> false)
         then
           Some (ldrbinstr, lslinstr, instr)
         else
           None
      | _ -> None)
  | _ -> None


(* format of predicate assignment (in ARM): assigns the result of a test as a
   0/1 value to a register

   MOVNE  Rx, #0
   MOVEQ  Rx, #1
 *)
let identify_predicate_assignment
      (_ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int):
      (bool
       * arm_assembly_instruction_int
       * arm_assembly_instruction_int
       * arm_operand_int) option =
  let is_zero imm = imm#to_numerical#equal numerical_zero in
  let is_one imm = imm#to_numerical#equal numerical_one in
  let is_zero_or_one imm = (is_zero imm) || (is_one imm) in
  match instr#get_opcode with
  | Move (false, c2, rd, imm2, _, _)
       when imm2#is_immediate && (is_zero_or_one imm2) && (has_inverse_cc c2) ->
     let rdreg = rd#get_register in
     let addr = instr#get_address in
     let movinstr_r = get_arm_assembly_instruction (addr#add_int (-4)) in
     (match TR.to_option movinstr_r with
      | Some movinstr ->
         (match movinstr#get_opcode with
          | Move (false, c1, rd, imm1, _, _)
               when imm1#is_immediate
                  && (is_zero_or_one imm1)
                  && (rd#get_register = rdreg)
                  && (not (imm1#to_numerical#equal imm2#to_numerical))
                  && (has_inverse_cc c1)
                  && ((Option.get (get_inverse_cc c1)) = c2) ->
             let inverse = is_zero imm2 in
             Some (inverse, movinstr, instr, rd)
          | _ -> None)
      | _ -> None)
  | _ -> None


let identify_arm_aggregate
      (ch: pushback_stream_int)
      (instr: arm_assembly_instruction_int):
      arm_instruction_aggregate_int option =
  let result =
    match identify_jumptable ch instr with
    | Some (instrs, jt) ->
       let anchor = List.nth instrs ((List.length instrs) - 1) in
       let entry = List.hd instrs in
       let exitinstr = anchor in
       Some (make_arm_jumptable_aggregate ~jt ~instrs ~entry ~exitinstr ~anchor)
    | _ -> None in
  let result =
    match result with
    | Some _ -> result
    | _ ->
       match identify_it_sequence ch instr with
       | Some its ->
          let instrs = its#instrs in
          let entry = List.hd instrs in
          let exitinstr = List.hd (List.rev instrs) in
          Some (make_it_sequence_aggregate
                  ~its ~instrs ~entry ~exitinstr ~anchor:entry)
       | _ -> None in
  let result =
    match result with
    | Some _ -> result
    | _ ->
       match identify_ldmstm_sequence ch instr with
       | Some ldmstmseq ->
          Some (make_ldm_stm_sequence_aggregate ldmstmseq)
       | _ -> None in
  let result =
    match result with
    | Some _ -> result
    | _ ->
       match identify_bx_call ch instr with
       | Some (movinstr, bxinstr) ->
          Some (make_bx_call_aggregate movinstr bxinstr)
       | _ -> None in
  let result =
    match result with
    | Some _ -> result
    | _ ->
       match identify_pseudo_ldrsh ch instr with
       | Some (ldrhinstr, lslinstr, asrinstr) ->
          Some (make_pseudo_ldrsh_aggregate ldrhinstr lslinstr asrinstr)
       | _ -> None in
  let result =
    match result with
    | Some _ -> result
    | _ ->
       match identify_pseudo_ldrsb ch instr with
       | Some (ldrbinstr, lslinstr, asrinstr) ->
          Some (make_pseudo_ldrsb_aggregate ldrbinstr lslinstr asrinstr)
       | _ -> None in
  let result =
    match result with
    | Some _ -> result
    | _ ->
       match identify_predicate_assignment ch instr with
       | Some (inverse, mov1, mov2, dstop) ->
          Some (make_predassign_aggregate inverse mov1 mov2 dstop)
       | _ -> None in
  result

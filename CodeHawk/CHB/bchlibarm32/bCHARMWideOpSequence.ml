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
open BCHCPURegisters
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMTypes


module TR = CHTraceResult


let p2s = CHPrettyUtil.pretty_to_string


let operand_pair_to_string (p: arm_lo_hi_operand_pair_t) =
  "(" ^ (p2s (fst p)#toPretty) ^ ", " ^ (p2s (snd p)#toPretty) ^ ")"


let register_pair_to_string (p: arm_lo_hi_register_pair_t) =
  "(" ^ (armreg_to_string (fst p)) ^", " ^ (armreg_to_string (snd p)) ^ ")"


let arm_lo_hi_operand_pair_to_string = operand_pair_to_string
let arm_lo_hi_register_pair_to_string = register_pair_to_string


let operand_pair_to_register_pair
      (p: arm_lo_hi_operand_pair_t): arm_lo_hi_register_pair_t option =
  let (lo, hi) = p in
  if lo#is_register && hi#is_register then
    Some (lo#get_register, hi#get_register)
  else
    None


let is_wide_op_flagged (addr: doubleword_int) (tags: string list): bool =
  match BCHSystemInfo.system_info#get_aggregate addr with
  | Some [aggkind] -> List.mem aggkind tags
  | _ -> false


let get_wide_op_tag (addr: doubleword_int): string option =
  match BCHSystemInfo.system_info#get_aggregate addr with
  | Some [aggkind] -> Some aggkind
  | _ -> None


class arm_wide_op_sequence_t
        (lo_hi_operands_defined: arm_lo_hi_operand_pair_t list)
        (lo_hi_operands_used: arm_lo_hi_operand_pair_t list)
        (instrs: arm_assembly_instruction_int list)
        (anchor: doubleword_int): arm_wide_op_sequence_int =
  object (self)

    method lo_hi_operand_pairs_defined = lo_hi_operands_defined

    method lo_hi_operand_pairs_used = lo_hi_operands_used

    method lo_hi_register_pairs_defined =
      List.fold_left (fun acc op ->
          match operand_pair_to_register_pair op with
          | Some p -> p :: acc
          | _ -> acc) [] self#lo_hi_operand_pairs_defined

    method lo_hi_register_pairs_used =
      List.fold_left (fun acc op ->
          match operand_pair_to_register_pair op with
          | Some p -> p :: acc
          | _ -> acc) [] self#lo_hi_operand_pairs_used

    method instrs = instrs
    method anchor = anchor

    method toString =
      "wide-op with defs: "
      ^ (String.concat
           ", " (List.map operand_pair_to_string self#lo_hi_operand_pairs_defined))
      ^ "; used: "
      ^ (String.concat
           ", " (List.map operand_pair_to_string self#lo_hi_operand_pairs_used))

    method toPretty = STR self#toString

  end


let make_wide_op_sequence
      (lo_hi_operands_defined: arm_lo_hi_operand_pair_t list)
      (lo_hi_operands_used: arm_lo_hi_operand_pair_t list)
      (instrs: arm_assembly_instruction_int list)
      (anchor: doubleword_int): arm_wide_op_sequence_int =
  new arm_wide_op_sequence_t lo_hi_operands_defined lo_hi_operands_used instrs anchor


let create_arm_wide_op_sequence
      (_ch: pushback_stream_int)
      (anchorinstr: arm_assembly_instruction_int):
      (arm_wide_op_kind_t * arm_wide_op_sequence_int) option =
  let anchoraddr = anchorinstr#get_address in
  match anchorinstr#get_opcode with
  | AddCarry (_, ACCAlways, rdhi, rnhi, rmhi, _) ->
     let addinstraddr = anchoraddr#add_int (-4) in
     (match TR.to_option (get_arm_assembly_instruction addinstraddr) with
      | Some addinstr ->
         (match addinstr#get_opcode with
          | Add (true, ACCAlways, rdlo, rnlo, rmlo, _) ->
             let instrs = [addinstr; anchorinstr] in
             let opsdefined = [(rdlo, rdhi)] in
             let opsused = [(rnlo, rnhi); (rmlo, rmhi)] in
             let wop = make_wide_op_sequence opsdefined opsused instrs anchoraddr in
             Some (WideAdd, wop)
          | _ -> None)
      | _ -> None)
  | SubtractCarry (_, ACCAlways, rdhi, rnhi, rmhi, _) ->
     let subinstraddr = anchoraddr#add_int (-4) in
     (match TR.to_option (get_arm_assembly_instruction subinstraddr) with
      | Some subinstr ->
         (match subinstr#get_opcode with
          | Subtract (true, ACCAlways, rdlo, rnlo, rmlo, _, _) ->
             let instrs = [subinstr; anchorinstr] in
             let opsdefined = [(rdlo, rdhi)] in
             let opsused = [(rnlo, rnhi); (rmlo, rmhi)] in
             let wop = make_wide_op_sequence opsdefined opsused instrs anchoraddr in
             Some (WideSubtract, wop)
          | _ -> None)
      | _ -> None)
  | ReverseSubtractCarry (_, ACCAlways, rdhi, rnhi, rmhi) ->
     let revinstraddr = anchoraddr#add_int (-4) in
     (match TR.to_option (get_arm_assembly_instruction revinstraddr) with
      | Some revinstr ->
         (match revinstr#get_opcode with
          | ReverseSubtract (true, ACCAlways, rdlo, rnlo, rmlo, _) ->
             let instrs = [revinstr; anchorinstr] in
             let opsdefined = [(rdlo, rdhi)] in
             let opsused = [(rnlo, rnhi); (rmlo, rmhi)] in
             let wop = make_wide_op_sequence opsdefined opsused instrs anchoraddr in
             Some (WideReverseSubtract, wop)
          | _ -> None)
      | _ -> None)
  | Move (_, ACCAlways, rd2, rn2, _, _)
       when is_wide_op_flagged anchoraddr ["wide-move-lo-hi"; "wide-move-hi-lo"] ->
     let mov1addr = anchoraddr#add_int(-4) in
     let tag = Option.get (get_wide_op_tag anchoraddr) in
     (match TR.to_option (get_arm_assembly_instruction mov1addr) with
      | Some mov1instr ->
         (match mov1instr#get_opcode with
          | Move (_, ACCAlways, rd1, rn1, _ , _) ->
             let instrs = [mov1instr; anchorinstr] in
             let (opsdefined, opsused) =
               if tag = "wide-move-hi-lo" then
                 ([(rd2, rd1)], [(rn2, rn1)])
               else
                 ([(rd1, rd2)], [(rn1, rn2)]) in
             let wop = make_wide_op_sequence opsdefined opsused instrs anchoraddr in
             Some (WideMove, wop)
          | _ -> None)
      | _ -> None)
  | BitwiseNot (false, ACCAlways, rd2, rn2, _)
       when is_wide_op_flagged anchoraddr ["wide-move-not"] ->
     let mvn1addr = anchoraddr#add_int(-4) in
     (match TR.to_option (get_arm_assembly_instruction mvn1addr) with
      | Some mvn1instr ->
         (match mvn1instr#get_opcode with
          | BitwiseNot (false, ACCAlways, rd1, rn1, _ ) ->
             let instrs = [mvn1instr; anchorinstr] in
             let opsdefined = [(rd1, rd2)] in
             let opsused = [(rn1, rn2)] in
             let wop = make_wide_op_sequence opsdefined opsused instrs anchoraddr in
             Some (WideMoveNot, wop)
          | _ -> None)
      | _ -> None)
  | BitwiseAnd (_, ACCAlways, rd2, rn2, rm2, _)
       when is_wide_op_flagged anchoraddr ["wide-and"] ->
     let and1addr = anchoraddr#add_int(-4) in
     (match TR.to_option (get_arm_assembly_instruction and1addr) with
      | Some and1instr ->
         (match and1instr#get_opcode with
          | BitwiseAnd (_, ACCAlways, rd1, rn1, rm1, _) ->
             let instrs = [and1instr; anchorinstr] in
             let (opsdefined, opsused) =
               ([(rd1, rd2)], [(rn1, rn2); (rm1, rm2)]) in
             let wop = make_wide_op_sequence opsdefined opsused instrs anchoraddr in
             Some (WideAnd, wop)
          | _ -> None)
      | _ -> None)
  | BitwiseOr (_, ACCAlways, rd2, rn2, rm2, _)
       when is_wide_op_flagged anchoraddr ["wide-or"] ->
     let or1addr = anchoraddr#add_int(-4) in
     (match TR.to_option (get_arm_assembly_instruction or1addr) with
      | Some or1instr ->
         (match or1instr#get_opcode with
          | BitwiseOr (_, ACCAlways, rd1, rn1, rm1, _) ->
             let instrs = [or1instr; anchorinstr] in
             let (opsdefined, opsused) =
               ([(rd1, rd2)], [(rn1, rn2); (rm1, rm2)]) in
             let wop = make_wide_op_sequence opsdefined opsused instrs anchoraddr in
             Some (WideOr, wop)
          | _ -> None)
      | _ -> None)
  | BitwiseExclusiveOr (_, ACCAlways, rd2, rn2, rm2, _)
       when is_wide_op_flagged anchoraddr ["wide-xor"] ->
     let xor1addr = anchoraddr#add_int(-4) in
     (match TR.to_option (get_arm_assembly_instruction xor1addr) with
      | Some xor1instr ->
         (match xor1instr#get_opcode with
          | BitwiseExclusiveOr (_, ACCAlways, rd1, rn1, rm1, _) ->
             let instrs = [xor1instr; anchorinstr] in
             let (opsdefined, opsused) =
               ([(rd1, rd2)], [(rn1, rn2); (rm1, rm2)]) in
             let wop = make_wide_op_sequence opsdefined opsused instrs anchoraddr in
             Some (WideXOr, wop)
          | _ -> None)
      | _ -> None)

  | _ -> None

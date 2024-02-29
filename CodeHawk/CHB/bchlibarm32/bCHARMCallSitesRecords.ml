(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023-2024  Aarno Labs, LLC

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
open CHPrettyUtil

(* bchlib *)
open BCHDoubleword
open BCHFunctionData
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMOpcodeRecords
open BCHARMTypes


module H = Hashtbl
module TR = CHTraceResult


let is_r0 (op: arm_operand_int): bool =
  op#is_register && op#get_register = AR0


let is_r0_compare (instr: arm_assembly_instruction_int): bool =
  match instr#get_opcode with
  | Compare (_, rd, rm, _) -> is_r0 rd || is_r0 rm
  | CompareBranchZero (rn, _)
    | CompareBranchNonzero (rn, _) -> is_r0 rn
  | CompareNegative (_, rn, _) -> is_r0 rn
  | _ -> false


let is_r0_move (instr: arm_assembly_instruction_int): bool =
  match instr#get_opcode with
  | Move (_, _, _, rn, _, _) -> is_r0 rn
  | StoreRegister (_, rt, _, _, _, _) -> is_r0 rt
  | _ -> false


let is_r0_compute (instr: arm_assembly_instruction_int): bool =
  match instr#get_opcode with
  | Add (_, _, _, rn, rm, _) -> is_r0 rn || is_r0 rm
  | ArithmeticShiftRight (_, _, _, rn, rm, _) -> is_r0 rn || is_r0 rm
  | Subtract (_, _, _, rn, rm, _, _) -> is_r0 rn || is_r0 rm
  | _ -> false


let is_r0_clobber (instr: arm_assembly_instruction_int): bool =
  match instr#get_opcode with
  | ArithmeticShiftRight (_, _, rd, rn, rm, _) ->
     is_r0 rd && (not (is_r0 rn || is_r0 rm))
  | Move (_, _, rd, _, _, _) -> is_r0 rd
  | LoadRegister (_, rt, _, _, _, _) -> is_r0 rt
  | _ -> false

(*
let is_pop_lr (instr: arm_assembly_instruction_int): bool =
  match instr#get_opcode with
  | Pop (_, _, rl, _) -> rl#includes_lr
  | _ -> false
 *)

let is_pop_pc (instr: arm_assembly_instruction_int): bool =
  match instr#get_opcode with
  | Pop (_, _, rl, _) -> rl#includes_pc
  | _ -> false


class arm_callsite_record_t
        (callsite: doubleword_int)
        (pre_instrs: arm_assembly_instruction_int list)
        (post_instrs: arm_assembly_instruction_int list)
        (postblock_instr: arm_assembly_instruction_int):
        arm_callsite_record_int =
object (self)

  method callsite = callsite

  method pre_instrs = pre_instrs

  method post_instrs = post_instrs

  method postblock_instr = postblock_instr

  method private has_use (p: arm_assembly_instruction_int -> bool): bool =
    let optb =
      List.fold_left (fun acc instr ->
          match acc with
          | Some _ -> acc
          | _ ->
             if p instr then
               Some true
             else if is_r0_clobber instr then
               Some false
             else
               acc) None self#post_instrs in
    match optb with
    | Some true -> true
    | _ -> false

  method has_returnvalue_compare = self#has_use is_r0_compare

  method has_returnvalue_move = self#has_use is_r0_move

  method has_returnvalue_compute = self#has_use is_r0_compute

  method has_returnvalue_clobber =
    let optb =
      List.fold_left (fun acc instr ->
          match acc with
          | Some _ -> acc
          | _ ->
             if is_r0_clobber instr then
               Some true
             else if is_r0_move instr then
               Some false
             else if is_r0_compute instr then
               Some false
             else if is_r0_compare instr then
               Some false
             else
               acc) None self#post_instrs in
    match optb with
    | Some true -> true
    | _ -> false

  method private has_block_fallthrough =
    List.fold_left (fun acc instr ->
        (not acc)
        || (match instr#get_opcode with
            | Branch _ | BranchExchange _ -> false
            | Pop (_, _, rl, _) when rl#includes_pc -> false
            | _ -> acc)) true self#post_instrs

  method has_fnentry_successor =
    ((((List.length self#post_instrs) = 0)
      || ((List.length self#post_instrs) = 1 && self#has_nop_successor)
      || (self#has_block_fallthrough))
     && functions_data#is_function_entry_point self#postblock_instr#get_address)

  method has_nop_successor =
    (List.length self#post_instrs) > 0
    && (let instr1 = List.hd self#post_instrs in
        match instr1#get_opcode with
        | NoOperation _ -> true
        | _ -> false)

  method private is_returnvalue_passed_to_parent =
    let optb =
      List.fold_left (fun acc instr ->
          match acc with
          | Some _ -> acc
          | _ ->
             if is_pop_pc instr then
               Some true
             else if is_r0_clobber instr then
               Some false
             else
               acc) None self#post_instrs in
    match optb with
    | Some true -> true
    | _ -> false

  method toPretty =
    let ppre =
      LBLOCK
        (List.map
           (fun i ->
             LBLOCK [STR (arm_opcode_to_string i#get_opcode); NL])
           self#pre_instrs) in
    let ppost =
      LBLOCK
        (List.map
           (fun i ->
             LBLOCK [STR (arm_opcode_to_string i#get_opcode); NL])
           self#post_instrs) in
    let status =
      let pbool b = STR (if b then "T" else ".") in
      LBLOCK [
          STR "  compare: "; pbool self#has_returnvalue_compare; NL;
          STR "  move   : "; pbool self#has_returnvalue_move; NL;
          STR "  compute: "; pbool self#has_returnvalue_compute; NL;
          STR "  clobber: "; pbool self#has_returnvalue_clobber; NL;
          STR "  nopsucc: "; pbool self#has_nop_successor; NL;
          STR "  fnentry: "; pbool self#has_fnentry_successor; NL;
          STR "  passed-to-parent: "; pbool self#is_returnvalue_passed_to_parent; NL;
          (if (List.length self#post_instrs) = 0 then
             (LBLOCK [STR "   --- block-ending ---"; NL])
           else
             STR "")] in
    LBLOCK [
        STR "Call-site: ";
        callsite#toPretty;
        NL;
        status;
        NL;
        STR "Pre instructions";
        NL;
        ppre;
        NL;
        STR "Post instructions";
        NL;
        ppost;
        NL;
        STR "Post-block instruction: ";
        STR "  ";
        STR (arm_opcode_to_string self#postblock_instr#get_opcode)]


end


class arm_callsites_record_t (tgtaddr: doubleword_int): arm_callsites_record_int =
object (self)

  val table = H.create 3

  method add_callsite
           (callsite: doubleword_int)
           (pre_instrs: arm_assembly_instruction_int list)
           (post_instrs: arm_assembly_instruction_int list)
           (postblock_instr: arm_assembly_instruction_int) =
    let index = callsite#index in
    let csrec =
      new arm_callsite_record_t callsite pre_instrs post_instrs postblock_instr in
    H.replace table index csrec

  method target_address = tgtaddr

  method callsites = H.fold (fun _ v a -> v :: a) table []

  method is_returning =
    List.fold_left (fun (s, c, n) v ->
        if v#has_returnvalue_compare
           || v#has_returnvalue_move
           || v#has_returnvalue_compute then
          (s+3, c, n)
        else if (List.length v#post_instrs) = 0 then
          (s, c+1, n)
        else
          (s, c, n+1)) (0, 0, 0) self#callsites

  method is_returnvalue_used = self#is_returning

  method is_non_returning =
    List.fold_left (fun (s, c, n) v ->
        if v#has_fnentry_successor then
          (s+3, c, n)
        else if v#has_nop_successor then
          (s+1, c, n)
        else if (List.length v#post_instrs) = 0 then
          (s+1, c, n)
        else if v#has_returnvalue_compare
                || v#has_returnvalue_move
                || v#has_returnvalue_compute then
          (s, c+3, n)
        else
          (s, c, n+1)) (0, 0, 0) self#callsites

  method is_returnvalue_clobbered =
    List.fold_left (fun (s, c, n) v ->
        if v#has_returnvalue_clobber then
          (s+1, c, n)
        else
          (s, c, n+1)) (0, 0, 0) self#callsites

  method toPretty =
    LBLOCK
      (List.map (fun v -> LBLOCK [v#toPretty; NL])
      (H.fold (fun _ v a -> v :: a) table []))

end


class arm_callsites_records_t: arm_callsites_records_int =
object (self)

  val table = H.create 3

  method add_callsite
           (tgtaddr: doubleword_int)
           (callsite: doubleword_int)
           (pre_instrs: arm_assembly_instruction_int list)
           (post_instrs: arm_assembly_instruction_int list)
           (postblock_instr: arm_assembly_instruction_int) =
    let index = tgtaddr#index in
    let cssrec =
      if H.mem table index then
        H.find table index
      else
        let r = new arm_callsites_record_t tgtaddr in
        begin
          H.add table index r;
          r
        end in
    cssrec#add_callsite callsite pre_instrs post_instrs postblock_instr

  method is_returning (faddr: doubleword_int) =
    let index = faddr#index in
    if H.mem table index then
      (H.find table index)#is_returning
    else
      (0, 0, 0)

  method is_returnvalue_used (faddr: doubleword_int) =
    let index = faddr#index in
    if H.mem table index then
      (H.find table index)#is_returnvalue_used
    else
      (0, 0, 0)

  method is_non_returning (faddr: doubleword_int) =
    let index = faddr#index in
    if H.mem table index then
      (H.find table index)#is_non_returning
    else
      (0, 0, 0)

  method is_returnvalue_clobbered (faddr: doubleword_int) =
    let index = faddr#index in
    if H.mem table index then
      (H.find table index)#is_returnvalue_clobbered
    else
      (0, 0, 0)

  method get_non_returning_functions =
    H.fold (fun k _ a ->
        let dw = TR.tget_ok (int_to_doubleword k) in
        let (s, c, n) = self#is_non_returning dw in
        if (s - c) > 2 * (n + 2) then dw :: a else a) table []

  method summary_to_pretty =
    let header =
      LBLOCK [
          STR (fixed_length_string "faddr" 20);
          STR (fixed_length_string "R" 19);
          STR (fixed_length_string "U" 19);
          STR (fixed_length_string "NR" 19);
          STR (fixed_length_string "C" 19);
          NL;
          STR (string_repeat "-" 80);
          NL] in
    let fns =
      LBLOCK
        (List.map (fun (k, _) ->
             let faddr = TR.tget_ok (int_to_doubleword k) in
             let pbool (s, c, n) =
               LBLOCK [
                   fixed_length_pretty ~alignment:StrRight (INT s) 3;
                   STR ", ";
                   fixed_length_pretty ~alignment:StrRight (INT c) 3;
                   STR ", ";
                   fixed_length_pretty ~alignment:StrRight (INT n) 3;
                   STR "      "] in
             LBLOCK [
                 (fixed_length_pretty faddr#toPretty 14);
                 (pbool (self#is_returning faddr));
                 (pbool (self#is_returnvalue_used faddr));
                 (pbool (self#is_non_returning faddr));
                 (pbool (self#is_returnvalue_clobbered faddr));
                 NL])
           (List.sort
              (fun (k1, _) (k2, _) -> Stdlib.compare k1 k2)
              (H.fold (fun k v a -> (k, v) :: a) table []))) in
    let nrfns =
      LBLOCK [
          STR "Non-returning functions: "; NL;
          (LBLOCK
             (List.map (fun dw -> LBLOCK [STR "  "; dw#toPretty; NL])
                (List.sort
                   (fun dw1 dw2 -> dw1#compare dw2)
                   self#get_non_returning_functions)));
          NL] in
    LBLOCK [header; fns; NL; nrfns]

  method toPretty =
    LBLOCK
      (List.map (fun (k, v) ->
           let faddr = TR.tget_ok (int_to_doubleword k) in
           LBLOCK [
               NL;
               STR "--------------------------------------------";
               faddr#toPretty;
               NL;
               v#toPretty;
               NL;
               STR "==================================================";
               NL])
         (List.sort
            (fun (k1, _) (k2, _) -> Stdlib.compare k1 k2)
            (H.fold (fun k v a -> (k, v) :: a) table [])))

end


let arm_callsites_records: arm_callsites_records_int =
  new arm_callsites_records_t

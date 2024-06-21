(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs, LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHLocation

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMOpcodeRecords
open BCHARMTypes


module TR = CHTraceResult


class arm_assembly_block_t
        ?(ctxt=[])
        ?(conditionalreturns=[])
        (faddr:doubleword_int)                (* inner context function address *)
        (first_address:doubleword_int)        (* address of first instruction *)
        (last_address:doubleword_int)         (* address of last instruction *)
        (successors:ctxt_iaddress_t list):arm_assembly_block_int =
object (self)

  val loc = make_location ~ctxt { loc_faddr = faddr; loc_iaddr = first_address }
  val mutable rev_instrs = []
  val conditionalreturns = conditionalreturns

  method get_location = loc

  method get_faddr = faddr

  method get_first_address = first_address

  method get_last_address = last_address

  method get_context = ctxt

  method get_context_string = loc#ci

  method get_instructions_rev ?(high=last_address) () =
    let revinstrs =
      if (List.length rev_instrs) > 0 then
        rev_instrs
      else
        let addrs =
          !arm_assembly_instructions#get_code_addresses
            ~low:self#get_first_address ~high:self#get_last_address () in
        let instrs =
          TR.tfold_list
            ~ok:(fun acc v -> v::acc)
            []
            (List.map (fun a -> get_arm_assembly_instruction a) addrs) in
        begin
          rev_instrs <- instrs;
          instrs
        end in
    let high =
      if self#get_last_address#lt high then
        self#get_last_address
      else if high#lt self#get_first_address then
        self#get_first_address
      else
        high in
    List.filter (fun instr -> instr#get_address#le high) revinstrs

  method get_instructions = List.rev (self#get_instructions_rev ())

  method get_successors = successors

  method get_instruction (va:doubleword_int) =
    try
      List.find (fun instr ->
          va#equal instr#get_address) (self#get_instructions_rev ())
    with
    | Not_found ->
       raise
         (BCH_failure
            (LBLOCK [ STR "No instruction found at address "; va#toPretty ]))

  method get_instruction_count = List.length (self#get_instructions)

  method get_bytes_as_hexstring =
    let s = ref "" in
    let _ = self#itera (fun _ i -> s := !s ^ i#get_bytes_ashexstring) in
    !s

  method itera
           ?(low=first_address)
           ?(high=last_address)
           ?(reverse=false)
           (f:ctxt_iaddress_t -> arm_assembly_instruction_int -> unit) =
    let instrs = self#get_instructions in
    let instrs = if reverse then List.rev instrs else instrs in
    let instrs =
      if low#equal first_address then
        instrs
      else
        List.filter (fun instr -> low#le instr#get_address) instrs in
    let instrs =
      if high#equal last_address then
        instrs
      else
        List.filter (fun instr -> instr#get_address#le high) instrs in
    List.iter
      (fun instr -> f (make_i_location loc instr#get_address)#ci instr) instrs

  method includes_instruction_address (va:doubleword_int) =
    List.exists
      (fun instr -> va#equal instr#get_address) self#get_instructions

  method has_conditional_returns =
    (List.length conditionalreturns) > 0

  method exit_edges_indices = conditionalreturns

                                          (*
    match self#get_context with
    | [] ->
       List.exists
         (fun instr ->
           match instr#get_opcode with
           | Pop (_, _, rl, _) ->
              rl#includes_pc && is_opcode_conditional instr#get_opcode
           | _ -> false) self#get_instructions
    | _ -> false *)

  method is_returning =
    match successors with
    | [] -> true
    | _ -> false

  method toString =
    let instructionstrings = ref [] in
    let _ =
      self#itera (fun ctxtiaddr instr ->
          instructionstrings :=
            (ctxtiaddr ^ "  " ^ instr#toString) :: !instructionstrings) in
    String.concat "\n" (List.rev !instructionstrings)

  method toPretty = STR self#toString

end


let make_arm_assembly_block = new arm_assembly_block_t


let make_ctxt_arm_assembly_block
      (newctxt:context_t)
      (b:arm_assembly_block_int)
      (newsucc:ctxt_iaddress_t list): arm_assembly_block_int =
  make_arm_assembly_block
    ~ctxt:(newctxt :: b#get_context)
    b#get_faddr
    b#get_first_address
    b#get_last_address
    newsucc


let make_block_ctxt_arm_assembly_block
      (newctxt: context_t)
      (b: arm_assembly_block_int) =
  make_arm_assembly_block
    ~ctxt:(newctxt :: b#get_context)
    b#get_faddr
    b#get_first_address
    b#get_last_address
    b#get_successors


let update_arm_assembly_block_successors
      (b: arm_assembly_block_int)
      (s_old: ctxt_iaddress_t)
      (s_new: ctxt_iaddress_t list): arm_assembly_block_int =
  let newsucc =
    List.fold_left (fun acc s ->
        if s = s_old then acc @ s_new else acc @ [s]) [] b#get_successors in
  make_arm_assembly_block
    ~ctxt:b#get_context
    b#get_faddr
    b#get_first_address
    b#get_last_address
    newsucc

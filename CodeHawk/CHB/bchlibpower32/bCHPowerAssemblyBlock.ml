(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023  Aarno Labs, LLC

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
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHFloc
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation

       (* bchlibpower32 *)
open BCHPowerAssemblyInstructions
open BCHPowerOpcodeRecords
open BCHPowerTypes


module TR = CHTraceResult


class pwr_assembly_block_t
        ?(ctxt=[])                    
        (faddr: doubleword_int)       (* inner context function address *)
        (first_addr: doubleword_int)  (* address of first instruction *)
        (last_addr: doubleword_int)   (* address of last instruction *)
        (successors: ctxt_iaddress_t list): pwr_assembly_block_int =
object (self)

  val loc = make_location ~ctxt {loc_faddr = faddr; loc_iaddr = first_addr}

  method location = loc

  method faddr = faddr

  method first_address = first_addr

  method last_address = last_addr

  method context = ctxt

  method context_string = loc#ci

  method successors = successors                        

  method get_instructions_rev ?(high=last_addr) () =
    let high =
      if self#last_address#lt high then
        self#last_address
      else if high#lt self#first_address then
        self#first_address
      else high in
    let addrs_rev =
      !pwr_assembly_instructions#get_code_addresses_rev
        ~low:first_addr ~high () in
    TR.tfold_list
      ~ok:(fun acc v -> v::acc)
      []
      (List.map (fun a -> get_pwr_assembly_instruction a) (List.rev addrs_rev))

  method get_instructions = List.rev (self#get_instructions_rev ())

  method get_instruction (va: doubleword_int) =
    try
      List.find (fun instr ->
          va#equal instr#get_address) (self#get_instructions_rev ())
    with
    | Not_found ->
       raise
         (BCH_failure
            (LBLOCK [STR "No instruction found at address: "; va#toPretty]))

  method get_bytes_as_hexstring =
    let s = ref "" in
    let _ = self#itera (fun _ i -> s := !s ^ i#get_bytes_as_hexstring) in
    !s

  method get_instruction_count = List.length (self#get_instructions_rev ())

  method itera
           ?(low=first_addr)
           ?(high=last_addr)
           ?(reverse=false)
           (f: ctxt_iaddress_t -> pwr_assembly_instruction_int -> unit) =
    let instrs =
      if reverse then self#get_instructions_rev () else self#get_instructions in
    let instrs =
      if low#equal first_addr then
        instrs
      else
        List.filter (fun instr -> low#le instr#get_address) instrs in
    let instrs =
      if high#equal last_addr then
        instrs
      else
        List.filter (fun instr -> instr#get_address#le high) instrs in
    List.iter
      (fun instr -> f (make_i_location loc instr#get_address)#ci instr) instrs

  method includes_instruction_address (va: doubleword_int) =
    List.exists
      (fun instr -> va#equal instr#get_address) (self#get_instructions_rev ())

  method is_returning =
    match successors with
    | [] -> true
    | _ -> false

  method toString =
    let istrs = ref [] in
    let _ =
      self#itera (fun ctxtiaddr instr ->
          istrs := (ctxtiaddr ^ "  " ^ instr#toString) :: !istrs) in
    String.concat "\n" (List.rev !istrs)

  method toPretty = STR self#toString

end


let make_pwr_assembly_block = new pwr_assembly_block_t


let make_ctxt_pwr_assembly_block
      (newctxt: context_t)
      (b: pwr_assembly_block_int)
      (newsucc: ctxt_iaddress_t list): pwr_assembly_block_int =
  make_pwr_assembly_block
    ~ctxt:(newctxt :: b#context)
    b#faddr b#first_address b#last_address newsucc


let update_pwr_assembly_block_successors
      (b: pwr_assembly_block_int)
      (s_old: ctxt_iaddress_t)
      (s_new: ctxt_iaddress_t list): pwr_assembly_block_int =
  let newsucc =
    List.fold_left (fun acc s ->
        if s = s_old then acc @ s_new else acc @ [s]) [] b#successors in
  make_pwr_assembly_block
    ~ctxt:b#context b#faddr b#first_address b#last_address newsucc

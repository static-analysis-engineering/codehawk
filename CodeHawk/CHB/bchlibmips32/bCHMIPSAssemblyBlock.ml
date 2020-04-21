(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

(* bchlibmips32 *)
open BCHMIPSAssemblyInstructions
open BCHMIPSTypes

class mips_assembly_block_t
        ?(ctxt=[])
        (faddr:doubleword_int)
        (firstaddr:doubleword_int)
        (lastaddr:doubleword_int)
        (successors:ctxt_iaddress_t list):mips_assembly_block_int =
object (self)

  val loc = make_location ~ctxt { loc_faddr = faddr ; loc_iaddr = firstaddr }
  val mutable revinstrs = []

  method get_faddr = faddr

  method get_location = loc

  method get_context = ctxt

  method get_context_string = loc#ci

  method get_first_address = firstaddr
  method get_last_address = lastaddr

  method get_instructions_rev =
    match revinstrs with
    | [] ->
       let addrsrev =
         !mips_assembly_instructions#get_code_addresses_rev
          ~low:firstaddr ~high:lastaddr () in
       let instrsrev =
         List.map !mips_assembly_instructions#at_address addrsrev in
       begin revinstrs <- instrsrev ; instrsrev end
    | _ -> revinstrs

  method get_instruction_count = List.length self#get_instructions_rev

  method get_instructions = List.rev self#get_instructions_rev

  method get_successors = successors

  method get_instruction (va:doubleword_int) =
    try
      List.find (fun instr -> va#equal instr#get_address) self#get_instructions_rev
    with
    | Not_found ->
       raise (BCH_failure (LBLOCK [ STR "No instruction found at address ";
                                    va#toPretty ]))

  method get_bytes_as_hexstring =
    let s = ref "" in
    let _ = self#itera (fun _ i -> s := !s ^ i#get_bytes_ashexstring)  in
    !s

  method itera
           ?(low=firstaddr) ?(high=lastaddr) ?(reverse=false)
           (f:ctxt_iaddress_t -> mips_assembly_instruction_int -> unit) =
    let instrs = if reverse then  self#get_instructions_rev else self#get_instructions in
    let instrs = if low#equal firstaddr then instrs else
                   List.filter (fun instr -> low#le instr#get_address) instrs in
    let instrs = if high#equal lastaddr then  instrs else
                   List.filter (fun instr -> instr#get_address#le high) instrs in
    List.iter (fun instr -> f (make_i_location loc instr#get_address)#ci instr) instrs

  method private get_addresses =
    let l = ref [] in begin self#itera (fun a _ -> l := a :: !l) ; List.rev !l end

  method includes_instruction_address (va:doubleword_int) =
    List.exists (fun instr -> va#equal instr#get_address) self#get_instructions_rev

  method is_returning =
    match successors with
    | [] -> true
    | _ -> false

  method toString =
    let lines = ref [] in
    let _ =
      self#itera
        (fun ctxtiaddr instr ->
          lines := (ctxtiaddr ^ "  " ^ instr#toString) :: !lines) in
    String.concat "\n" (List.rev !lines)

  method toPretty =
    let pp = ref [] in
    let _ =
      self#itera
        (fun ctxtiaddr instr ->
          pp := (LBLOCK [ STR ctxtiaddr ; STR "  " ; instr#toPretty ; NL ]) :: !pp) in
    LBLOCK (List.rev !pp)

end

let make_mips_assembly_block = new mips_assembly_block_t
                
(* create an assembly block for an inlined function *)
let make_ctxt_mips_assembly_block
      (newctxt:context_t)            (* new context to be prepended *)
      (b:mips_assembly_block_int)         (* orginal assembly block *)
      (newsucc:ctxt_iaddress_t list)  (* new successors to be added *)
    :mips_assembly_block_int =
  let bsucc = b#get_successors in
  let faddr = b#get_faddr in
  let succ = List.map (fun s -> add_ctxt_to_ctxt_string faddr s newctxt) bsucc in
  make_mips_assembly_block
    ~ctxt:(newctxt :: b#get_context)
    b#get_faddr
    b#get_first_address
    b#get_last_address
    (succ @ newsucc)
  
let make_block_ctxt_mips_assembly_block
      (newctxt:context_t)
      (b:mips_assembly_block_int) =
  make_mips_assembly_block
    ~ctxt:(newctxt :: b#get_context)
    b#get_faddr
    b#get_first_address
    b#get_last_address
    b#get_successors
  
let update_mips_assembly_block_successors
      (b:mips_assembly_block_int)
      (s_old:ctxt_iaddress_t)
      (s_new:ctxt_iaddress_t):mips_assembly_block_int =
  let newsucc =
    List.map (fun s -> if s = s_old then s_new else s) b#get_successors in
  make_mips_assembly_block
    ~ctxt:b#get_context
    b#get_faddr
    b#get_first_address
    b#get_last_address
    newsucc

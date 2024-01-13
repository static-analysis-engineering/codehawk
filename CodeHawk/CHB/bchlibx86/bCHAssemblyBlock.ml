(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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
open BCHLibTypes
open BCHLocation

(* bchlibx86 *)
open BCHAssemblyInstructionAnnotations
open BCHAssemblyInstructions
open BCHLibx86Types


class assembly_block_t
        ?(ctxt=[])
        (faddr:doubleword_int)                (* inner context function address *)
        (first_address:doubleword_int)        (* address of first instruction *)
        (last_address:doubleword_int)         (* address of last instruction *)
        (successors:ctxt_iaddress_t list):assembly_block_int =
object (self)

  val loc = make_location ~ctxt {loc_faddr = faddr; loc_iaddr = first_address}
  val mutable rev_instrs = []

  method get_location = loc

  method get_faddr = faddr

  method get_first_address = first_address
  method get_last_address  = last_address

  method get_context = ctxt
  method get_context_string = loc#ci

  method get_instructions_rev =
    match rev_instrs with
    | [] ->
       let addrsRev =
         !assembly_instructions#get_code_addresses_rev
	   ~low:first_address ~high:last_address () in
      let instrsRev = List.map !assembly_instructions#at_address addrsRev in
      begin
        rev_instrs <- instrsRev;
        instrsRev
      end
    | l -> l

  method get_instructions = List.rev self#get_instructions_rev

  method get_successors = successors

  method get_instruction (va:doubleword_int) =
    try
      List.find (fun instr ->
          va#equal instr#get_address) self#get_instructions_rev
    with
    | Not_found ->
       raise
         (BCH_failure
            (LBLOCK [
                 STR "No instruction found at address "; va#toPretty]))

  method get_instruction_count = List.length self#get_instructions_rev

  method get_bytes_ashexstring =
    let s = ref "" in
    let _ = self#itera (fun _ i -> s := !s ^ i#get_bytes_ashexstring) in
    !s

  method itera
           ?(low=first_address)
           ?(high=last_address)
           ?(reverse=false)
           (f:ctxt_iaddress_t -> assembly_instruction_int -> unit) =
    let instrs =
      if reverse then self#get_instructions_rev else self#get_instructions in
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
    List.iter (fun instr ->
        f (make_i_location loc instr#get_address)#ci instr) instrs

  method private get_addresses =
    let l = ref [] in
    begin
      self#itera (fun a _ -> l := a :: !l);
      List.rev !l
    end

  method includes_instruction_address (va:doubleword_int) =
    List.exists (fun instr ->
        va#equal instr#get_address) self#get_instructions_rev

  method is_returning =
    match successors with
      [] ->
      let lastInstr = !assembly_instructions#at_address self#get_last_address in
      let iloc = make_i_location self#get_location last_address in
      let floc = get_floc iloc in
      begin
	match lastInstr#get_opcode with
	| DirectCall _ | IndirectCall _ -> false
	| IndirectJmp _ when
               floc#has_call_target && floc#get_call_target#is_nonreturning ->
	   false
	| _ -> true
      end
    | _ -> false


  method toString =
    let instructionStrings = ref [] in
    let _ =
      self#itera (fun ctxtiaddr instr ->
          instructionStrings :=
            (ctxtiaddr ^ "  " ^ instr#toString) :: !instructionStrings) in
    String.concat "\n" (List.rev !instructionStrings)

  method toPretty =
    let pp = ref [] in
    let _ = self#itera (fun ctxtiaddr instr ->
      pp := (LBLOCK [STR ctxtiaddr; STR "  "; instr#toPretty; NL]) :: !pp) in
    LBLOCK (List.rev !pp)

  method to_annotated_pretty =
    let pp = ref [] in
    let _ =
      self#itera (fun ctxtiaddr instr ->
          let iloc = ctxt_string_to_location faddr ctxtiaddr in
          let floc = get_floc iloc in
          let ann = create_annotation floc in
          pp :=
            (LBLOCK [
                 STR ctxtiaddr;
                 STR "  ";
		 fixed_length_pretty instr#toPretty 32;
                 ann#toPretty;
                 NL]) :: !pp) in
    LBLOCK (List.rev !pp)

  method write_xml (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun instr ->
           let iNode = xmlElement "instr" in
           let iloc = make_i_location self#get_location instr#get_address in
           let floc = get_floc iloc in
           begin
	     instr#write_xml iNode;
	     iNode#setPrettyAttribute "ann" (create_annotation floc)#toPretty;
	     iNode
           end) self#get_instructions)


  method to_xml (loops:cfg_loops_int) =
    let mkL a =
      let aNode = xmlElement "l" in
      begin aNode#setAttribute "a" a#to_hex_string; aNode end in
    let mkC c =
      let cNode = xmlElement "l" in
      begin
        cNode#setAttribute "a" c;
        cNode
      end in
    let node = xmlElement "block" in
    let lNode = xmlElement "locs" in
    let sNode = xmlElement "succ" in
    let nNode = xmlElement "nested-in"  in
    let nesting = loops#get_loop_levels self#get_first_address in
    begin
      node#setAttribute "a" self#get_first_address#to_hex_string;
      node#setAttribute "e" self#get_last_address#to_hex_string;
      lNode#appendChildren (List.map mkC self#get_addresses);
      sNode#appendChildren (List.map mkC self#get_successors);
      nNode#setIntAttribute "num" (List.length nesting);
      nNode#appendChildren (List.map mkL nesting);
      node#appendChildren [nNode; sNode; lNode];
      node
    end

end


let make_assembly_block = new assembly_block_t


(* create an assembly block for an inlined function *)
let make_ctxt_assembly_block
      (newctxt:context_t)            (* new context to be prepended *)
      (b:assembly_block_int)         (* orginal assembly block *)
      (newsucc:ctxt_iaddress_t list) (* new successors to be added *)
    :assembly_block_int =
  make_assembly_block
    ~ctxt:(newctxt :: b#get_context)
    b#get_faddr
    b#get_first_address
    b#get_last_address
    newsucc

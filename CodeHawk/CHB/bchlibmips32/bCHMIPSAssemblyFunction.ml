(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2025 Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHLibTypes
open BCHLocation

(* bchlibmips32 *)
open BCHMIPSAssemblyBlock
open BCHMIPSDisassemblyUtils
open BCHMIPSTypes

module H = Hashtbl


class mips_assembly_function_t
        (faddr:doubleword_int)
        (blocks:mips_assembly_block_int list)
        (successors: (ctxt_iaddress_t * ctxt_iaddress_t) list):mips_assembly_function_int =
object (self)

  val blocktable =
    let t = H.create 3 in
    let _ = List.iter (fun b -> H.add t b#get_context_string b) blocks in
    t
  val successortable =
    let t = H.create 3 in
    let _ = List.iter (fun (src,tgt) -> H.add t src tgt) successors in
    t

  method get_address = faddr

  method get_blocks = blocks

  method get_block (bctxt:ctxt_iaddress_t) =
    if H.mem blocktable bctxt then
      H.find blocktable bctxt
    else
      begin
	ch_error_log#add
          "invocation error"
	  (LBLOCK [
               STR "mips_assembly_function#get_block: "; STR bctxt ]);
	raise
          (BCH_failure
             (LBLOCK [
                  STR __FILE__; STR ":"; INT __LINE__; STR ": ";
                  STR "No assembly block found at ";
                  STR bctxt;
                  STR " in function ";
                  faddr#toPretty]))
      end

  method get_instruction (iaddr:doubleword_int) =
    try
      let block =
        List.find (fun b -> b#includes_instruction_address iaddr) blocks in
      block#get_instruction iaddr
    with
    | Not_found ->
       let msg =
         LBLOCK [
             STR __FILE__; STR ":"; INT __LINE__; STR ": ";
             STR "assembly_function#get_instruction: ";
             iaddr#toPretty;
             STR " in function ";
             faddr#toPretty]  in
       begin
         ch_error_log#add "invocation error" msg;
         raise (BCH_failure msg)
       end

  method get_bytes_as_hexstring =
    let s = ref "" in
    let _ = self#iter (fun b -> s := !s ^ b#get_bytes_as_hexstring) in
    !s

  method get_instruction_count = 
    List.fold_left (fun a b -> a + b#get_instruction_count) 0 blocks

  method get_block_count = List.length blocks

  method get_function_md5 =
    byte_string_to_printed_string (Digest.string self#get_bytes_as_hexstring)

  method populate_callgraph (callgraph:callgraph_int) =
    self#iteri (fun _ iaddr instr ->
        let opcode = instr#get_opcode in
        if is_direct_call_instruction opcode then
          let tgtaddr = get_direct_call_target_address opcode in
          callgraph#add_app_edge faddr tgtaddr iaddr []
        else if is_indirect_call_instruction opcode then
          callgraph#add_unresolved_edge faddr (-1) iaddr []
        else
          ())

  method iter (f:mips_assembly_block_int -> unit) =
    List.iter (fun block -> f block) self#get_blocks

  method itera (f:ctxt_iaddress_t -> mips_assembly_block_int -> unit) =
    List.iter (fun block -> f block#get_context_string block) self#get_blocks

  method iteri
           (f:doubleword_int
            -> ctxt_iaddress_t
            -> mips_assembly_instruction_int
            -> unit) =
    List.iter (fun (block:mips_assembly_block_int) ->
        block#itera (fun iaddr instr -> f faddr iaddr instr)) self#get_blocks

  method includes_instruction_address (va:doubleword_int) =
    List.exists (fun b -> b#includes_instruction_address va) blocks

  method toPretty =
    LBLOCK (List.map (fun block -> LBLOCK [block#toPretty; NL]) blocks)

end


let make_mips_assembly_function
      (va:doubleword_int)
      (blocks:mips_assembly_block_int list)
      (successors:(ctxt_iaddress_t * ctxt_iaddress_t) list) =
  let blocks =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_context_string b2#get_context_string)
      blocks in
  new mips_assembly_function_t va blocks successors


let inline_blocks
      (baddrs:doubleword_int list)
      (f:mips_assembly_function_int) =
  let newblocks = H.create f#get_block_count in    (* ctxt_iaddr -> assemblyblock *)
  let faddr = f#get_address in
  let is_to_be_inlined s = List.exists (fun b -> is_same_iaddress b s) baddrs in
  let rec process_block (baddr:ctxt_iaddress_t) =
    if H.mem newblocks baddr then
      ()
    else
      let block = f#get_block baddr in
      begin
        H.add newblocks baddr block;
        List.iter
          (fun s ->
            if is_to_be_inlined s then
              let succblock = f#get_block s in
              let ctxt = BlockContext block#get_first_address in
              let newctxtstr = add_ctxt_to_ctxt_string faddr s ctxt in
              let _ =
                if H.mem newblocks newctxtstr then
                  ()
                else
                  let newblock =
                    make_block_ctxt_mips_assembly_block ctxt succblock in
                  begin
                    chlog#add
                      "mips assembly block: add context"
                      (LBLOCK [faddr#toPretty; STR ": "; STR newctxtstr]);
                    H.add newblocks newctxtstr newblock
                  end in
              let thisnewblock =
                update_mips_assembly_block_successors block s newctxtstr in
              begin
                H.replace newblocks baddr thisnewblock;
                chlog#add
                  "mips assembly block: replace successor"
                  (LBLOCK [faddr#toPretty; STR ": "; STR baddr])
              end) block#get_successors;
        List.iter process_block block#get_successors
      end in
  let _ = process_block faddr#to_hex_string in
  let blocks = H.fold (fun _ v a -> v::a) newblocks [] in
  let succ =
    H.fold (fun k v a ->
        (List.map (fun s -> (k, s)) v#get_successors) @ a) newblocks [] in
  (blocks, succ)


let inline_blocks_mips_assembly_function
      (baddrs:doubleword_int list)
      (f:mips_assembly_function_int) =
  let (blocks, successors) = inline_blocks baddrs f in
  new mips_assembly_function_t f#get_address blocks successors

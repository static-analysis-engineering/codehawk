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

(* chutil *)
open CHLogger

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHLibTypes
open BCHLocation

(* bchlibarm32 *)
open BCHARMAssemblyBlock
open BCHARMAssemblyInstructions
open BCHARMTypes

module H = Hashtbl


class arm_assembly_function_t
        (faddr: doubleword_int)
        (blocks: arm_assembly_block_int list)
        (successors: (ctxt_iaddress_t * ctxt_iaddress_t) list)
      :arm_assembly_function_int =
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

  method get_cfg_edges = List.sort Stdlib.compare successors

  method get_block (bctxt:ctxt_iaddress_t) =
    if H.mem blocktable bctxt then
      H.find blocktable bctxt
    else
      begin
        ch_error_log#add
          "invocation error"
          (LBLOCK [ STR "arm_assembly_function#get_block: ";
                    STR bctxt ]);
        raise
          (BCH_failure
             (LBLOCK [ STR "No assembly block found at " ; STR bctxt;
                       STR " in function " ; faddr#toPretty ]))
      end

  method get_instruction (iaddr:doubleword_int) =
    try
      let block =
        List.find (fun b -> b#includes_instruction_address iaddr) blocks in
      block#get_instruction iaddr
    with
    | Not_found ->
       let msg = LBLOCK [ STR "arm_assembly_function#get_instruction: ";
                          iaddr#toPretty ] in
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

  method get_not_valid_instr_count =
    let c = ref 0 in
    let _ =
      self#iteri (fun _ _ instr ->
          match instr#get_opcode with
          | NotRecognized _
            | PermanentlyUndefined _
            | OpcodeUndefined _
            | OpcodeUnpredictable _ -> c := !c + 1
          | _ -> ()) in
    !c

  method get_function_md5 =
    byte_string_to_printed_string (Digest.string self#get_bytes_as_hexstring)

  method get_jumptables =
    let result = ref [] in
    let _ =
      self#iteri (fun _ _ instr ->
          if instr#is_aggregate_anchor then
            match instr#is_in_aggregate with
            | Some dw ->
               (match (get_aggregate dw)#kind with
                | ARMJumptable jt ->
                   result := (dw, jt) :: !result
                | _ -> ())
            | _ -> ()) in
    !result

  method iter (f:arm_assembly_block_int -> unit) =
    List.iter (fun b -> f b) self#get_blocks

  method itera (f:ctxt_iaddress_t -> arm_assembly_block_int -> unit) =
    List.iter (fun b -> f b#get_context_string b) self#get_blocks

  method iteri
           (f:doubleword_int
            -> ctxt_iaddress_t
            -> arm_assembly_instruction_int
            -> unit) =
    List.iter (fun (b:arm_assembly_block_int) ->
        b#itera (fun iaddr instr -> f faddr iaddr instr)) self#get_blocks

  method populate_callgraph (_callgraph: callgraph_int) =
    self#iteri (fun _ _iaddr _instr -> ())

  method includes_instruction_address (va:doubleword_int) =
    List.exists (fun b -> b#includes_instruction_address va) blocks

  method has_conditional_return =
    List.exists (fun b -> b#has_conditional_returns) blocks

  method get_true_conditional_return =
    try
      let tc =
        List.find (fun b ->
            b#get_instruction_count = 1
            && (has_true_condition_context b#get_context_string))
          blocks in
      Some tc
    with
    | _ -> None

  method toPretty =
    LBLOCK
      (List.map (fun b ->
           LBLOCK [
               b#toPretty;
               NL;
               STR " -> ";
               pretty_print_list b#get_successors (fun s -> STR s) "" ", " "";
               NL;
               NL]) blocks)

end


(* Duplicates basic blocks that contain a conditional return instruction
   (e.g., POPEQ or POPNE with PC included in the register list). Each such
   basic block should have only one instruction. Two versions are created:
   one with a true conditional context and one with a false conditional
   context. The one with true conditional context has no successor, the one
   with the false conditional context has the original successor. The
   semantics of the latter is equal to that of NOP.
let inline_conditional_blocks (fn: arm_assembly_function_int) =
  let blockreplacements = H.create (2 * fn#get_block_count) in
  let newblocks = H.create (2 * fn#get_block_count) in
  let faddr = fn#get_address in
  let update_successors (b: arm_assembly_block_int): arm_assembly_block_int =
    let newsucc =
      List.fold_left (fun acc s ->
          if H.mem blockreplacements s then
            let (fb, tb) = H.find blockreplacements s in
            acc @ [fb#get_context_string; tb#get_context_string]
          else
            acc @ [s]) [] b#get_successors in
    make_arm_assembly_block
      ~ctxt:b#get_context faddr b#get_first_address b#get_last_address newsucc in
  let _ =
    begin
      fn#iter (fun b ->
          if b#has_conditional_return_instr then
            let b1 =
              make_ctxt_arm_assembly_block
                (ConditionContext false) b b#get_successors in
            let b2 =
              make_ctxt_arm_assembly_block
                (ConditionContext true) b [] in
            H.add blockreplacements b#get_context_string (b1, b2));
      fn#iter (fun b ->
          if H.mem blockreplacements b#get_context_string then
            let (fblock, tblock) = H.find blockreplacements b#get_context_string in
            begin
              H.add newblocks tblock#get_context_string tblock;
              H.add newblocks fblock#get_context_string (update_successors fblock)
            end
          else
            H.add newblocks b#get_context_string (update_successors b))
    end in
  let blocks = H.fold (fun _ v a -> v::a) newblocks [] in
  let blocks =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_context_string b2#get_context_string) blocks in
  let succ =
    H.fold (fun k v a ->
        (List.map (fun s -> (k, s)) v#get_successors) @ a) newblocks [] in
  (blocks, succ)
 *)

let make_arm_assembly_function
      (va:doubleword_int)
      (blocks:arm_assembly_block_int list)
      (successors:(ctxt_iaddress_t * ctxt_iaddress_t) list) =
  let blocks =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_context_string b2#get_context_string) blocks in
  let fn = new arm_assembly_function_t va blocks successors in
  (* if fn#has_conditional_return then
    let (newblocks, newsucc) = inline_conditional_blocks fn in
    new arm_assembly_function_t va newblocks newsucc
  else *)
    fn


(* Note: this function must still be updated for the presence of conditional
   returns in assembly blocks *)
let inline_blocks
      (baddrs: doubleword_int list)
      (f: arm_assembly_function_int) =
  let newblocks = H.create f#get_block_count in  (* ctxt_iaddr -> assemblyblock *)
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
              let _ = chlog#add "to be inlined" (STR s) in
              let succblock = f#get_block s in
              let ctxt = BlockContext block#get_first_address in
              let newctxtstr = add_ctxt_to_ctxt_string faddr s ctxt in
              let _ =
                if H.mem newblocks newctxtstr then
                  ()
                else
                  let newblock =
                    make_block_ctxt_arm_assembly_block ctxt succblock in
                    H.add newblocks newctxtstr newblock in
              let thisnewblock =
                update_arm_assembly_block_successors block s [newctxtstr] in
              H.replace newblocks baddr thisnewblock) block#get_successors;
        List.iter process_block block#get_successors
      end in
  let _ = process_block faddr#to_hex_string in
  let blocks = H.fold (fun _ v a -> v::a) newblocks [] in
  let succ =
    H.fold (fun k v a ->
        (List.map (fun s -> (k, s)) v#get_successors) @ a) newblocks [] in
  (blocks, succ)


let inline_blocks_arm_assembly_function
      (baddrs: doubleword_int list)
      (f: arm_assembly_function_int) =
  let (blocks, successors) = inline_blocks baddrs f in
  new arm_assembly_function_t f#get_address blocks successors


let create_path_contexts
      (s: ctxt_iaddress_t)
      (sentinels: ctxt_iaddress_t list)
      (f: arm_assembly_function_int) =
  let faddr = f#get_address in
  let newblocks = H.create f#get_block_count in

  let rec create_path (p: string) (s: ctxt_iaddress_t) =
    let pblock = f#get_block s in
    let ctxt = PathContext p in
    let pctxtaddr = add_ctxt_to_ctxt_string faddr s ctxt in
    if H.mem newblocks pctxtaddr then
      pctxtaddr
    else
      (* add first to avoid infinite recursion for loop *)
      let _ = H.add newblocks pctxtaddr pblock in
      let psucc = pblock#get_successors in
      let new_succ = List.map (create_path p) psucc in
      let newblock = make_ctxt_arm_assembly_block ctxt pblock new_succ in
      begin
        H.replace newblocks pctxtaddr newblock;
        pctxtaddr
      end in

  let rec process_block (baddr: ctxt_iaddress_t) =
    if H.mem newblocks baddr then
      ()
    else
      let block = f#get_block baddr in
      let succs = block#get_successors in
      let new_succs = ref [] in
      if baddr = s then
        begin
          let cntr = ref 1 in
          List.iter (fun succ ->
              let new_succ =
                create_path ("path_" ^ (string_of_int !cntr)) succ in
              cntr := !cntr + 1;
              new_succs := new_succ :: !new_succs) succs;
          let newblock =
            make_arm_assembly_block
              ~ctxt:block#get_context
              block#get_faddr
              block#get_first_address
              block#get_last_address
              (List.rev !new_succs) in
          H.add newblocks baddr newblock
        end
      else
        begin
          H.add newblocks baddr block;
          List.iter process_block succs
        end in

  let _ = process_block faddr#to_hex_string in
  let blocks = H.fold (fun _ v a -> v::a) newblocks [] in
  let succ =
    H.fold (fun k v a ->
        (List.map (fun s -> (k, s)) v#get_successors) @ a) newblocks [] in
  new arm_assembly_function_t faddr blocks succ

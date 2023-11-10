(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023  Aarno Labs LLC

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

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHLibTypes
open BCHLocation
open BCHSystemInfo
open BCHSystemSettings

(* bchlibpower32 *)
open BCHPowerAssemblyBlock
open BCHPowerAssemblyFunction
open BCHPowerAssemblyFunctions
open BCHPowerAssemblyInstructions
open BCHPowerTypes


module TR = CHTraceResult


module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


let get_successors
      (faddr: doubleword_int) (iaddr: doubleword_int): ctxt_iaddress_t list =
  log_tfold_default
    (mk_tracelog_spec
       ~tag:"get_successors"
       ("faddr:" ^ faddr#to_hex_string ^ ", iaddr: " ^ iaddr#to_hex_string))
    (fun instr ->
      (* let get_next_iaddr = get_next_valid_instruction_address in *)
      let opcode = instr#get_opcode in
      let next () =
        log_tfold_default
          (mk_tracelog_spec
             ~tag:"get_successors:next"
             ("faddr:" ^ faddr#to_hex_string ^ ", iaddr:" ^ iaddr#to_hex_string))
          (fun a -> [a])
          []
          (get_next_valid_instruction_address iaddr) in

      (* let next_from (va: doubleword_int) =
        log_tfold_default
          (mk_tracelog_spec
             ~tag:"get_successors:next_from"
             ("faddr:" ^ faddr#to_hex_string ^ ", iaddr:" ^ iaddr#to_hex_string))
          (fun a -> [a])
          []
          (get_next_valid_instruction_address va) in *)

      let succ =
        match opcode with

        (* unconditionarl return instruction *)
        | BranchLinkRegister _ -> []

        (* unconditional branch *)
        | Branch (_, tgt) -> [tgt#get_absolute_address]

        (* conditional branch *)
        | BranchConditional (_, _, _, _, tgt)
          | BranchConditionalLink (_, _, _, _, tgt, _)
          | CBranchEqual (_, _, _, _, _, _, tgt)
          | CBranchGreaterThan (_, _, _, _, _, _, tgt)
          | CBranchLessEqual (_, _, _, _, _, _, tgt)
          | CBranchLessThan (_, _, _, _, _, _, tgt)
          | CBranchNotEqual (_, _, _, _, _, _, tgt) ->
           (* false branch first, true branch second *)
           (next ()) @ [tgt#get_absolute_address]

        | _ -> next () in

      List.map (fun va -> (make_location_by_address faddr va)#ci)
        (List.filter
           (fun va ->
             if !pwr_assembly_instructions#is_code_address va then
               true
             else
               (* let loc = make_location_by_address faddr va in *)
               false) succ))
    []
    (get_pwr_assembly_instruction iaddr)


(* Returns inlinedblocks, block constructed, and newly discovered function
   entry points *)
let construct_pwr_assembly_block
      (faddr: doubleword_int)
      (baddr: doubleword_int):
      (pwr_assembly_block_int list
       * pwr_assembly_block_int
       * doubleword_int list) =

  let newfnentries = new DoublewordCollections.set_t in

  (* let set_block_entry (a: doubleword_int) =
    TR.titer (fun instr ->
        instr#set_block_entry) (get_pwr_assembly_instruction a) in *)

  let get_instr = get_pwr_assembly_instruction in
  let has_next_instr =
    !pwr_assembly_instructions#has_next_valid_instruction in
  let get_next_instr_address =
    !pwr_assembly_instructions#get_next_valid_instruction_address in

  let is_tail_call (instr: pwr_assembly_instruction_int) =
    match instr#get_opcode with
    | BranchCountRegister _ ->
       let _ =
         chlog#add "assume tail call" (LBLOCK [instr#get_address#toPretty]) in
       true
    | _ -> false in

  let is_non_returning_call_instr (instr: pwr_assembly_instruction_int) =
    match instr#get_opcode with
    | BranchLink (_, tgt, _) when tgt#is_absolute_address ->
       let tgtaddr = tgt#get_absolute_address in
       ((functions_data#is_function_entry_point tgtaddr)
        && (functions_data#get_function tgtaddr)#is_non_returning)
    | _ -> false in

  let rec find_last_instruction (va: doubleword_int) (prev: doubleword_int) =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "find_last_instruction: "; va#toPretty]))
        (get_instr va) in

    (* continue tracing the block *)
    let nextva () =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "find_last_instruction: "; va#toPretty]))
        (get_next_instr_address va) in

    let floc = get_floc_by_address faddr va in
    let _ = floc#set_instruction_bytes instr#get_instruction_bytes in
    if va#equal wordzero then
      (* end of code reached? *)
      (Some [], prev, [])

    else if instr#is_block_entry then
      (* we went beyond the end of the block, return previous *)
      (None, prev, [])

    else if is_non_returning_call_instr instr then
      (* end of function, no successors *)
      (Some [], va, [])

    else if is_tail_call instr then
      (* call instruction that is not returning *)
      (Some [], va,  [])

    else if system_info#is_nonreturning_call faddr va then
      (* user-declared non-returning call, no successors *)
      (Some [], va, [])

    else if floc#has_call_target && floc#get_call_target#is_nonreturning then
      (* end of the function, no successors *)
      (Some [], va, [])

    else if has_next_instr va then
      (* continue tracing the block *)
      find_last_instruction (nextva ()) va

    else
      (* dead end, no more instructions *)
      (None, va, []) in

  let binstr =
    fail_tvalue
      (trerror_record
         (LBLOCK [STR "get_successors: "; baddr#toPretty]))
      (get_instr baddr) in

  let (succ, lastaddr, inlinedblocks) =
    if system_info#is_nonreturning_call faddr baddr then
      (* user-declared non-returning call, no successors *)
      (Some [], baddr, [])

    else if is_non_returning_call_instr binstr then
      (* end of function, no successors *)
      (Some [], baddr, [])

    else if has_next_instr baddr then
      (* construct the block *)
      let nextva =
        fail_tvalue
          (trerror_record
             (LBLOCK [STR "get_successors: "; baddr#toPretty]))
          (get_next_instr_address baddr) in
      find_last_instruction nextva baddr

    else
      (* give up *)
      (None, baddr, []) in

  let succ =
    match succ with
    | Some s -> s
    | _ ->
       match system_info#get_successors lastaddr with
       | [] -> get_successors faddr lastaddr
       | l ->
          (* user-provided successors to the last instruction *)
          List.map
            (fun loc -> loc#ci)
            (List.map (make_location_by_address faddr) l) in

  (inlinedblocks,
   make_pwr_assembly_block faddr baddr lastaddr succ,
   newfnentries#toList)


let construct_pwr_assembly_function
      (faddr: doubleword_int): (doubleword_int list * pwr_assembly_function_int) =
  let newfnentries = new DoublewordCollections.set_t in
  let workset = new DoublewordCollections.set_t in
  let doneset = new DoublewordCollections.set_t in
  let get_iaddr s = (ctxt_string_to_location faddr s)#i in
  let add_to_workset l =
    List.iter (fun a -> if doneset#has a then () else workset#add a) l in
  let set_block_entry (baddr: doubleword_int) =
    TR.titer
      (fun instr -> instr#set_block_entry)
      (get_pwr_assembly_instruction baddr) in
  let blocks = ref [] in
  let rec add_block (baddr: doubleword_int) =
    let (inlinedblocks, block, newfes) =
      construct_pwr_assembly_block faddr baddr in
    let blocksucc =
      match inlinedblocks with
      | [] -> block#successors
      | _ -> [] in
    let inlinedblocksucc =
      List.fold_left
        (fun acc b ->
          match b#successors with
          | [h] when is_iaddress h -> h::acc
          | _ -> acc) [] inlinedblocks in
    begin
      set_block_entry baddr;
      newfnentries#addList newfes;
      workset#remove baddr;
      doneset#add baddr;
      blocks := (block :: inlinedblocks) @ !blocks;
      add_to_workset
        (List.map get_iaddr (blocksucc @ inlinedblocksucc));
      match workset#choose with Some a -> add_block a  | _ -> ()
    end in
  let _ = add_block faddr in
  let blocklist =
    List.sort (fun (b1: pwr_assembly_block_int) (b2: pwr_assembly_block_int) ->
        Stdlib.compare b1#context_string b2#context_string) !blocks in
  let succ =
    List.fold_left
      (fun acc (b: pwr_assembly_block_int) ->
        let src = b#context_string in
        (List.map (fun tgt -> (src, tgt)) b#successors) @ acc) [] blocklist in
  (newfnentries#toList, make_pwr_assembly_function faddr blocklist succ)

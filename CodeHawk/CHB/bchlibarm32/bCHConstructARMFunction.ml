(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2022-2024  Aarno Labs LLC

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
open BCHSystemInfo

(* bchlibelf *)
open BCHELFHeader

(* bchlibarm32 *)
open BCHARMAssemblyBlock
open BCHARMAssemblyFunction
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstructions
open BCHARMTypes
open BCHLocation


module TR = CHTraceResult


module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


let get_successors
      (faddr: doubleword_int) (iaddr: doubleword_int):ctxt_iaddress_t list =
  log_tfold_default
    (mk_tracelog_spec
       ~tag:"get_successors"
       ("faddr:" ^ faddr#to_hex_string ^ ", " ^ "iaddr:" ^ iaddr#to_hex_string))
    (fun instr ->
      let get_next_iaddr = get_next_valid_instruction_address in
      let opcode = instr#get_opcode in
      let next () =
        log_tfold_default
          (mk_tracelog_spec
             ~tag:"get_successors:next"
             ("faddr:" ^ faddr#to_hex_string ^ ", " ^ "iaddr:" ^ iaddr#to_hex_string))
          (fun a -> [a])
          []
          (get_next_valid_instruction_address iaddr) in

      let is_maybe_non_returning_call_instr =
        match instr#get_opcode with
        | BranchLink (ACCAlways, tgt)
          | BranchLinkExchange (ACCAlways, tgt) when tgt#is_absolute_address ->
           let tgtaddr = tgt#get_absolute_address in
           ((functions_data#is_function_entry_point tgtaddr)
            && (functions_data#get_function tgtaddr)#is_maybe_non_returning)
        | _ -> false in

      let next_from (va: doubleword_int) =
        log_tfold_default
          (mk_tracelog_spec
             ~tag:"get_successors:next_from"
             ("faddr:" ^ faddr#to_hex_string ^ ", " ^ "iaddr:" ^ iaddr#to_hex_string))
          (fun a -> [a])
          []
          (get_next_valid_instruction_address va) in

      (* Return (follow-instr-addr, conditional-instructions-addresses) or None
         if a next address cannot be found.*)
      let get_iftxf (iaddr: doubleword_int) (ninstr: int):
            (doubleword_int * doubleword_int list) option =
        (* if then x follow *)
        let rec aux
                  (n: int)
                  (iva: doubleword_int)
                  (result: doubleword_int list option) =
          if n = 0 then
            result
          else
            match result with
            | None -> None
            | Some instrs ->
               (match TR.to_option (get_next_iaddr iva) with
                | None -> None
                | Some va ->
                   aux (n - 1) va (Some (va :: instrs))) in
        match (aux ninstr iaddr (Some [])) with
        | Some l when (List.length l) = ninstr ->
           Some (List.hd l, List.rev (List.tl l))
        | _ -> None in

      let succ =
        match opcode with
        (* error situation *)
        | PermanentlyUndefined _ -> []

        (* unconditional return instruction *)
        | Pop (ACCAlways, _, rl, _) when rl#includes_pc -> []

        (* conditional return instruction *)
        | Pop (_, _, rl, _) when rl#includes_pc ->
           (next ()) @ [wordmax]

        (* maybe non-returning call instruction *)
        | BranchLink _ | BranchLinkExchange _
             when is_maybe_non_returning_call_instr ->
           let _ = chlog#add "maybe non returning" (iaddr#toPretty) in
           (next ()) @ [wordmax]

        (* return via LDM/LDMDB/LDMDA/LDMIB *)
        | LoadMultipleDecrementBefore (_, ACCAlways, _, rl, _)
          | LoadMultipleDecrementAfter (_, ACCAlways, _, rl, _)
          | LoadMultipleIncrementBefore (_, ACCAlways, _, rl, _)
          | LoadMultipleIncrementAfter (_, ACCAlways, _, rl, _)
             when rl#includes_pc -> []

        (* return via indirect jump on LR *)
        | Branch (ACCAlways, op, _)
          | BranchExchange (ACCAlways, op)
             when op#is_register && op#get_register = ARLR -> []

        (* conditional return in guarded basic block *)
        | Branch (_, op, _)
          | BranchExchange (_, op)
             when op#is_register
                  && op#get_register = ARLR
                  && instr#is_condition_covered -> []

        (* conditional return not guarded; TBD: duplicate block *)
        | Branch (_, op, _)
          | BranchExchange (_, op)
             when op#is_register && op#get_register = ARLR ->
           (next ())

        (* return via Move *)
        | Move (_, ACCAlways, dst, src, _, _)
             when dst#is_register
                  && dst#get_register = ARPC
                  && src#is_register
                  && src#get_register = ARLR -> []

        (* LDRLS jumptable (ARM) *)
        | Branch _ when instr#is_aggregate_anchor
                        && (get_aggregate iaddr)#is_jumptable ->
           let jt = (get_aggregate iaddr)#jumptable in
           jt#default_target :: jt#target_addrs

        (* Unconditional direct jump *)
        | Branch (ACCAlways, op, _)
          | BranchExchange (ACCAlways, op) when op#is_absolute_address ->
           [op#get_absolute_address]

        (* Conditional direct jump *)
        | Branch (_, op, _)
          | BranchExchange (_, op)
          | CompareBranchZero (_, op)
          | CompareBranchNonzero (_, op) when op#is_absolute_address ->
           (* false branch first, true branch second *)
           (next ()) @ [op#get_absolute_address]

        (* Thumb-2 IfThen construct:
           va0: ITT c
           va1: if c .. .
           va2: if c ...
           va3: next instruction (fall-through)
         *)
        | IfThen (_, xyz) when (xyz = "T") || (xyz = "TT") ->
           let n_instrs = (String.length xyz) + 2 in
           (match get_iftxf iaddr n_instrs with
            | Some (followva, conditional_vas) ->
               [followva; (List.hd conditional_vas)]
            | _->
               begin
                 ch_error_log#add
                   "construct_function: IfThen"
                   (LBLOCK [iaddr#toPretty; STR ": Error with ITT, ITTT"]);
                 []
               end)

        | IfThen _ when instr#is_aggregate_anchor ->
           let exitinstr = (get_aggregate iaddr)#exitinstr in
           next_from exitinstr#get_address

        | IfThen (_, xyz) ->
           let _ =
             chlog#add
               "function construction:IfThen"
               (LBLOCK [
                    STR "Not handled: "; STR xyz; STR " at "; iaddr#toPretty]) in
           next ()

        | TableBranchByte _
          | TableBranchHalfword _
          | LoadRegister _
          | BranchExchange _
          | Add _
             when instr#is_aggregate_anchor
                  && (get_aggregate iaddr)#is_jumptable ->
           let jt = (get_aggregate iaddr)#jumptable in
           jt#default_target :: jt#target_addrs

        (* may or may not be a return *)
        | LoadRegister (_, dst, _, _, mem, _)
             when dst#is_register && dst#get_register = ARPC ->
           if mem#is_literal_address then
             let addr = mem#get_literal_address in
             if elf_header#is_program_address addr then
               [elf_header#get_program_value addr]
             else
               []
           else
             []

        | Branch (ACCAlways, op, _)
          | BranchExchange (ACCAlways, op) when op#is_pc_register ->
           [iaddr#add_int 4]

        | Branch (ACCAlways, op, _)
          | BranchExchange (ACCAlways, op) when op#is_register ->
           let floc = get_floc_by_address faddr instr#get_address in
           let opxpr = op#to_expr floc in
           let opxpr = floc#inv#rewrite_expr opxpr in
           (match opxpr with
            | XConst (IntConst n) ->
               let tgt =
                 if (n#modulo (mkNumerical 2))#equal numerical_one then
                   n#sub numerical_one
                 else
                   n in
               log_tfold_default
                 (mk_tracelog_spec
                    ~tag:"construct-function"
                    (floc#cia ^ ": constant: " ^ n#toString))
                 (fun addr ->
                   if !arm_assembly_instructions#is_code_address addr then
                     [addr]
                   else
                     [])
                 []
                 (numerical_to_doubleword tgt)
            | _ -> [])

        (* no information available, give up *)
        | Branch _ | BranchExchange _ -> []

        | _ -> next () in

      List.map (fun va -> (make_location_by_address faddr va)#ci)
        (List.filter
           (fun va ->
             (* wordmax is used to indicate that the successor of a basic
                block is another basic block in addition to returning from
                the function (i.e., a conditional return)
                The value will be filtered out when creating the assembly
                block *)
             if !arm_assembly_instructions#is_code_address va
                || va = wordmax then
               true
             else
               let loc = make_location_by_address faddr va in
               begin
                 ch_error_log#add
                   "disassembly"
                   (LBLOCK [
                        STR "Successor of ";
                        loc#toPretty;
                        STR " is not a valid code address"]);
                 false
               end) succ))
    []
    (get_arm_assembly_instruction iaddr)


let construct_arm_assembly_block
      (faddr: doubleword_int)
      (baddr: doubleword_int):
      (arm_assembly_block_int list * arm_assembly_block_int * doubleword_int list) =

  let newfnentries = new DoublewordCollections.set_t in

  let set_block_entry (a: doubleword_int) =
    TR.titer (fun instr ->
        instr#set_block_entry) (get_arm_assembly_instruction a) in

  let get_instr = get_arm_assembly_instruction in
  let has_next_instr =
    !arm_assembly_instructions#has_next_valid_instruction in
  let get_next_instr_address =
    !arm_assembly_instructions#get_next_valid_instruction_address in

  let is_permanently_undefined (instr: arm_assembly_instruction_int) =
    match instr#get_opcode with
    | PermanentlyUndefined _ -> true
    | _ -> false in

  let is_tail_call (instr: arm_assembly_instruction_int) =
    match instr#get_opcode with
    | Branch (ACCAlways, tgt, _)
      | BranchExchange (ACCAlways, tgt) when tgt#is_absolute_address ->
       let tgtaddr = tgt#get_absolute_address in
       functions_data#is_function_entry_point tgtaddr
    | _ -> false in

  let is_non_returning_call_instr (instr: arm_assembly_instruction_int) =
    match instr#get_opcode with
    | BranchLink (ACCAlways, tgt)
      | BranchLinkExchange (ACCAlways, tgt) when tgt#is_absolute_address ->
       let tgtaddr = tgt#get_absolute_address in
       ((functions_data#is_function_entry_point tgtaddr)
        && (functions_data#get_function tgtaddr)#is_non_returning)
    | _ -> false in

  let get_inlined_function (instr: arm_assembly_instruction_int) =
    let tgtaddr =
      match instr#get_opcode with
      | BranchLink (_, op)
        | BranchLinkExchange (_, op) when op#is_absolute_address ->
         op#get_absolute_address
      | _ ->
         raise
           (BCH_failure
              (LBLOCK [
                   STR "Internal error in construct_arm_assembly_block: ";
                   instr#toPretty])) in
    get_arm_assembly_function tgtaddr in

  let get_inlined_call_blocks
        (va: doubleword_int)
        (instr: arm_assembly_instruction_int):
        (ctxt_iaddress_t * arm_assembly_block_int list) =
    let inlinedfn = get_inlined_function instr in
    let returnsite =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "construct_arm_assembly_block: "; va#toPretty]))
        (get_next_instr_address va) in
    let _ = set_block_entry returnsite in
    let functioncontext =
      mk_function_context ~faddr:faddr ~callsite:va ~returnsite:returnsite in
    let callsucc =
      make_function_context_location
        ~faddr:faddr
        ~callsite:va
        ~returnsite:returnsite
        ~calltgt:inlinedfn#get_address in

    let inlinedblocks =
      let inline_exit = (make_location_by_address faddr returnsite)#ci in
      List.map (fun (b: arm_assembly_block_int) ->
          let succ =
            match b#get_successors with
            | [] -> [inline_exit]
            | l ->
               (* exit edges must be replaced by inline_exits *)
               if b#has_conditional_returns then
                 let exitixs = b#exit_edges_indices in
                 let (_, xix, succ) =
                   List.fold_left (fun (ix, xix, acc) s ->
                       match xix with
                       | [] ->
                          (ix + 1,
                           [],
                           (add_ctxt_to_ctxt_string faddr s functioncontext)
                           :: acc)
                       | h :: tl when ix = h ->
                          (ix + 1,
                           tl,
                           inline_exit
                           :: (add_ctxt_to_ctxt_string faddr s functioncontext)
                           :: acc)
                       | _  ->
                          (ix + 1,
                           xix,
                           (add_ctxt_to_ctxt_string faddr s functioncontext)
                           :: acc))
                     (1, exitixs, []) l in
                 (* add exits for remaining exit indices *)
                 succ @ (List.map (fun _ -> inline_exit) xix)
               else
                 List.map (fun s ->
                     add_ctxt_to_ctxt_string faddr s functioncontext) l in
          make_ctxt_arm_assembly_block functioncontext b succ)
      inlinedfn#get_blocks in

    (callsucc#ci, inlinedblocks) in

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
      (* went beyond the end of the block, return previous *)
      (None, prev, [])

    else if system_info#is_nonreturning_call faddr va then
      (* user-declared non-returning call, no successors *)
      (Some [], va, [])

    else if is_non_returning_call_instr instr then
      (* the end of the function, no successors *)
      (Some [], va, [])

    else if is_tail_call instr then
      (* the end of the function, no successors *)
      (Some [], va, [])

    else if is_permanently_undefined instr then
      (* dead end, no successors *)
      (Some [], va, [])

    else if floc#has_call_target && floc#get_call_target#is_nonreturning then
      (* end of the function, no successors *)
      (Some [], va, [])

    else if instr#is_inlined_call then
      (* insert all basic blocks of the function that is inlined *)
      let (callsucc, inlinedblocks) = get_inlined_call_blocks va instr in
      (Some [callsucc], va, inlinedblocks)

    else if Option.is_some instr#is_in_aggregate
            && not instr#is_aggregate_exit then
      (* aggregate is linear unit *)
      find_last_instruction (nextva ()) va

    else if Option.is_some instr#is_in_aggregate
            && instr#is_aggregate_exit
            && (match instr#get_opcode with
                | Add (_, ACCNotUnsignedHigher, _, _, _, _) -> true
                | _ -> false) then
      (* the ADDLS aggregate must be forced to appear at the end of a block
         to ensure successors are connected.*)
      (None, va, [])

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

    else if is_tail_call binstr then
      (* the end of the function, no successors *)
      (Some [], baddr, [])

    else if is_permanently_undefined binstr then
      (* dead end, no successors *)
      (Some [], baddr, [])

    else if binstr#is_inlined_call then
      (* insert all basic blocks of the function that is inlined *)
      let (callsucc, inlinedblocks) = get_inlined_call_blocks baddr binstr in
      (Some [callsucc], baddr, inlinedblocks)

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
  (* There may be multiple successors that are returns; their indices are
     collected, while the successors themselves are filtered out.*)
  let (conditionalreturns, _index, succ) =
    List.fold_left (fun (cr, ix, sl) s ->
        if s = wordmax#to_hex_string then
          (ix::cr, ix + 1, sl)
        else
          (cr, ix + 1, s::sl)) ([], 1, []) succ in
  let succ = List.rev succ in
  (inlinedblocks,
   make_arm_assembly_block ~conditionalreturns faddr baddr lastaddr succ,
   newfnentries#toList)


(* Constructs an assembly function. In the process it may discover a
   tail-call, which is reported back as a new function entry point. *)
let construct_arm_assembly_function
      (faddr: doubleword_int):(doubleword_int list * arm_assembly_function_int) =
  let newfnentries = new DoublewordCollections.set_t in
  let workset = new DoublewordCollections.set_t in
  let doneset = new DoublewordCollections.set_t in
  let get_iaddr s = (ctxt_string_to_location faddr s)#i in
  let add_to_workset l =
    List.iter (fun a -> if doneset#has a then () else workset#add a) l in
  let set_block_entry (baddr: doubleword_int) =
    TR.titer
      (fun instr -> instr#set_block_entry)
      (get_arm_assembly_instruction baddr) in
  let blocks = ref [] in
  let rec add_block (baddr: doubleword_int) =
    let (inlinedblocks, block, newfes) =
      construct_arm_assembly_block faddr baddr in
    let blocksucc =
      match inlinedblocks with
      | [] -> block#get_successors
      | _ -> [] in
    let inlinedblocksucc =
      List.fold_left
        (fun acc b ->
          match b#get_successors with
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
      match workset#choose with Some a -> add_block a | _ -> ()
    end in
  let _ = add_block faddr in
  let blocklist =
    List.sort (fun (b1: arm_assembly_block_int) (b2: arm_assembly_block_int) ->
        Stdlib.compare b1#get_context_string b2#get_context_string) !blocks in
  let succ =
    List.fold_left
      (fun acc (b: arm_assembly_block_int) ->
        let src = b#get_context_string in
        (List.map (fun tgt -> (src, tgt)) b#get_successors) @ acc) [] blocklist in
  (newfnentries#toList, make_arm_assembly_function faddr blocklist succ)

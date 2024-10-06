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
open CHTiming

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHFloc
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHLocation
open BCHMakeCallTargetInfo
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities

(* bchlibelf *)
open BCHELFHeader
open BCHELFTypes

(* bchlibarm32 *)
open BCHARMAssemblyFunctions
open BCHARMAssemblyInstruction
open BCHARMAssemblyInstructions
open BCHARMCallSitesRecords
open BCHARMInstructionAggregate
open BCHARMPseudocode
open BCHARMOpcodeRecords
open BCHARMTypes
open BCHConstructARMFunction
open BCHDisassembleARMInstruction
open BCHDisassembleThumbInstruction

module H = Hashtbl
module TR = CHTraceResult


let log_error (tag: string) (msg: string): tracelogspec_t =
  mk_tracelog_spec ~tag:("disassemble-arm:" ^ tag) msg


module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


let disassemble_arm_section
      (sectionbase: doubleword_int) (sectionbytes: string) =
  let sectionsize = String.length sectionbytes in
  let mode = ref "arm" in

  let add_instruction
        (iaddr: doubleword_int) (opcode: arm_opcode_t) (bytes: string) =
    let instr =
      make_arm_assembly_instruction iaddr (!mode="arm") opcode bytes in
    begin
      set_arm_assembly_instruction instr;
      instr
    end in
  let ch = make_pushback_stream sectionbytes in

  let not_code_length nc =
    match nc with
    | JumpTable jt -> jt#get_length
    | DataBlock db -> db#get_length in

  let not_code_set_string nc s =
    match nc with
    | DataBlock db -> db#set_data_string s
    | _ -> () in

  let is_data_block (iaddr: doubleword_int) =
    TR.to_bool
      (fun instr -> instr#is_non_code_block)
      (get_arm_assembly_instruction iaddr) in

  let skip_data_block (pos: int) ch =
    let iaddr = sectionbase#add_int pos in
    log_titer
      (mk_tracelog_spec
         ~tag:"disassembly" ("skip_data_block:" ^ iaddr#to_hex_string))
      (fun instr ->
        let nonCodeBlock = instr#get_non_code_block in
        let dblen = not_code_length nonCodeBlock in
        if pos + dblen <= sectionsize then
          let blockbytes =
            try
              ch#sub pos dblen
            with
            | BCH_failure p ->
               begin
                 ch_error_log#add
                   "disassembly:skip data_block"
                   (LBLOCK [
                        STR "pos: ";
                        INT pos;
                        STR "; dblen: ";
                        INT dblen;
                        STR ": ";
                        p]);
                 ""
               end in
          begin
            (if collect_diagnostics () then
               ch_diagnostics_log#add
                 "skip data block"
                 (LBLOCK [STR "pos: "; INT pos; STR "; length: "; INT dblen]));
            ch#skip_bytes dblen;
            not_code_set_string nonCodeBlock blockbytes
          end
        else
          ch_error_log#add
            "data block problem"
            (LBLOCK [
                 STR "Data block at ";
                 (sectionbase#add_int pos)#toPretty;
                 STR " extends beyond end of section. Ignore"]))
      (get_arm_assembly_instruction iaddr) in

  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [
           STR "sectionbase: ";
           sectionbase#toPretty ;
           STR "; size: ";
           INT sectionsize]) in
  try
    begin
      while ch#pos + 2 < sectionsize do   (* <= causes problems at section end *)
        let prevPos = ch#pos in
        let iaddr = sectionbase#add_int ch#pos in
        let _ =
          if system_settings#has_thumb then
            match system_info#get_arm_thumb_switch iaddr with
            | Some "A" ->
               begin
                 mode := "arm";
                 chlog#add
                   "arm-thumb switch"
                   (LBLOCK [iaddr#toPretty; STR ": arm"])
               end
            | Some "T" ->
               begin
                 mode := "thumb";
                 chlog#add
                   "arm-thumb switch"
                   (LBLOCK [iaddr#toPretty; STR ": thumb"])
               end
            | _ ->
               () in
        try
          if is_data_block iaddr then
            skip_data_block prevPos ch
          else
            if system_settings#has_thumb && !mode = "thumb" then
              (* Thumb mode *)
              let instrbytes = ch#read_ui16 in
              let opcode =
                try
                  disassemble_thumb_instruction ch iaddr instrbytes
                with
                | _ -> OpInvalid in
              let currentPos = ch#pos in
              let instrlen = currentPos - prevPos in
              let instrbytes = ch#sub prevPos instrlen in
              let instr = add_instruction iaddr opcode instrbytes in
              let optagg = identify_arm_aggregate ch instr in
              match optagg with
              | Some agg -> set_aggregate iaddr agg
              | _ -> ()

            else
              (* ARM mode *)
              let instrbytes = ch#read_doubleword in
              let opcode =
                  try
                    disassemble_arm_instruction ch iaddr instrbytes
                  with
                  | BCH_failure p ->
                     begin
                       ch_error_log#add
                         "instruction disassembly error"
                         (LBLOCK [iaddr#toPretty; STR ": "; p]);
                       NotRecognized ("error", instrbytes)
                     end
                  | _ -> OpInvalid in
              let currentPos = ch#pos in
              let instrlen = currentPos - prevPos in
              let instrbytes = ch#sub prevPos instrlen in
              let instr = add_instruction iaddr opcode instrbytes in
              let optagg = identify_arm_aggregate ch instr in
              match optagg with
              | Some agg -> set_aggregate agg#anchor#get_address agg
              | _ -> ()
        with
        | BCH_failure p ->
           begin
             ch_error_log#add
               "disassembly"
               (LBLOCK [
                    STR "failure in disassembling instruction at ";
                    iaddr#toPretty;
                    STR " in mode ";
                    STR !mode]);
             raise (BCH_failure p)
           end
      done
    end
  with
  | BCH_failure p ->
     begin
       pr_debug [STR "Error in disassembly: "; p; NL];
       raise (BCH_failure p)
     end
  | IO.No_more_input ->
     begin
       pr_debug [STR "Error in disassembly: No more input"; NL];
       raise IO.No_more_input
     end


let sanitize_datablocks
      (headers: elf_section_header_int list) (datablocks: data_block_int list) =
  List.iter (fun db ->
      let dbstart = db#get_start_address in
      let dbend = db#get_end_address in
      List.iter (fun h ->
          let sa = h#get_addr in
          let s_end = h#get_addr#add_int h#get_size#value in
          if dbstart#lt sa && sa#lt dbend then
            begin
              chlog#add
                "truncate datablock"
                (LBLOCK [
                     dbstart#toPretty;
                     STR ": original end: ";
                     dbend#toPretty;
                     STR "; new end: ";
                     sa#toPretty]);
              db#truncate sa
            end
          else if sa#le dbstart && dbstart#lt s_end && s_end#lt dbend then
            begin
              chlog#add
                "truncate datablock"
                (LBLOCK [
                     dbstart#toPretty;
                     STR ": original end: ";
                     dbend#toPretty;
                     STR "; new end: ";
                     s_end#toPretty]);
              db#truncate s_end
            end
        ) headers) datablocks


let disassemble_arm_sections () =
  let _ = set_starttime (Unix.gettimeofday ()) in
  let xSections = elf_header#get_executable_sections in
  let headers =
    List.sort (fun (h1, _) (h2, _) ->
        h1#get_addr#compare h2#get_addr) xSections in
  let sectionsizes =
    List.map (fun (h, _) ->
        (h#get_section_name, h#get_addr, h#get_size)) headers in
  let is_in_executable_section (db: data_block_int) =
    List.fold_left (fun found (_, ha, hsize) ->
        found
        || (ha#le db#get_start_address
            && db#get_start_address#lt (ha#add_int hsize#value)))
      false sectionsizes in
  let programentrypoint = elf_header#get_program_entry_point in
  let datablocks =
    List.filter is_in_executable_section system_info#get_data_blocks in
  begin
    initialize_arm_instructions sectionsizes;
    pr_timing [
        STR "instructions initialized";
        pretty_print_list
          sectionsizes
          (fun (name, addr, size) ->
            LBLOCK [
                STR "(";
                STR name;
                STR ", ";
                addr#toPretty;
                STR ", ";
                size#toPretty;
                STR ")"]) " [" ", " "]"];
    let (dw, r) = programentrypoint#to_aligned 4 in
    (if (r = 1) then system_info#set_arm_thumb_switch dw "T");
    ignore (functions_data#add_function dw);
    sanitize_datablocks (List.map fst headers) datablocks;
    pr_timing [STR "data blocks sanitized ("; INT (List.length datablocks); STR ")"];
    initialize_arm_assembly_instructions sectionsizes datablocks;
    pr_timing [STR "assembly instructions initialized"];
    List.iter
      (fun (h, x) ->
        begin
          disassemble_arm_section h#get_addr x;
          pr_timing [
              STR "section disassembled at ";
              h#get_addr#toPretty;
              STR " of length ";
              INT (String.length x);
              STR " bytes"]
        end) xSections
  end


(* recognizes patterns of library function calls

     F B 0x99bc  00 c6 8f e2       ADR      R12, 0x99c4
         0x99c0  3a ca 8c e2       ADD      R12, R12, #237568
         0x99c4  bc f8 bc e5       LDR      PC, [R12], #2236

     F B 0x89b0  00 c6 8f e2       ADR      R12, 0x89b8
         0x89b4  0a ca 8c e2       ADD      R12, R12, #40960
         0x89b8  a4 fb bc e5       LDR      PC, [R12], #2980

     F B 0x2d8a8  00 c6 8f e2       ADR      R12, 0x2d8b0
         0x2d8ac  e3 ca 8c e2       ADD      R12, R12, #0xe3000
         0x2d8b0  68 f7 bc e5       LDR      PC, [R12], #1896

     F B 0x1f2ec  05 c6 8f e2       ADR      R12, 0x51f2f4
         0x1f2f0  42 ca 8c e2       ADD      R12, R12, #0x42000
         0x1f2f4  18 fd bc e5       LDR      PC, [R12], #3352

     F B 0x38f1c  02 c6 8f e2       ADR      R12, 0x238f24
         0x38f20  0b ca 8c e2       ADD      R12, R12, #0xb000
         0x38f24  e8 f0 bc e5       LDR      PC, [R12], #232

     F B 0x674    00 c6 8f e2       ADR      R12, 0x67c
         0x678    11 ca 8c e2       ADD      R12, R12, #0x11000
         0x67c    98 f9 bc e5       LDR      PC, [R12, #2456]!

     F B 0x6f9b8  01 c6 8f e2       ADR      R12, 0x16f9b8
         0x6f9bc  1f ca 8c e2       ADD      R12, R12, #0x1f000
         0x6f9c0  b4 fd bc e5       LDR      PC, [R12,#0xdb4]!


 *)
let is_library_stub faddr =
  if elf_header#is_program_address faddr
     && elf_header#has_xsubstring faddr 12 then
    let bytestring =
      byte_string_to_printed_string (elf_header#get_xsubstring faddr 12) in
    let instrsegs = [
        "\\(..\\)c68fe2\\(..\\)ca8ce2\\(....\\)bce5"
      ] in
    List.exists (fun s ->
        let regex = Str.regexp s in
        Str.string_match regex bytestring 0) instrsegs
  else
    false


let set_library_stub_name faddr =
  if elf_header#is_program_address faddr then
    let to_int h = Int64.to_int (Int64.of_string h) in
    let bytestring =
      byte_string_to_printed_string (elf_header#get_xsubstring faddr 12) in
    let regex = Str.regexp "\\(..\\)c68fe2\\(..\\)ca8ce2\\(..\\)f\\(.\\)bce5" in
    if Str.string_match regex bytestring 0 then
      let imm8_1h = "0x" ^ (Str.matched_group 1 bytestring) in
      let imm8_1 = to_int imm8_1h in
      let offset1 = faddr#add_int ((arm_expand_imm 6 imm8_1) + 8) in
      let imm8_2h = "0x" ^ (Str.matched_group 2 bytestring) in
      let imm8_2 = to_int imm8_2h in
      let offset2 = arm_expand_imm 10 imm8_2 in
      let imm8_3h = Str.matched_group 3 bytestring in
      let imm4_4h = "0x" ^ (Str.matched_group 4 bytestring) in
      let imm12_4h = imm4_4h ^ imm8_3h in
      let imm12_4 = to_int imm12_4h in
      let addr = offset1#add_int (offset2 + imm12_4) in
      if functions_data#has_function_name addr then
        let fndata = functions_data#add_function faddr in
        begin
          fndata#add_name (functions_data#get_function addr)#get_function_name;
          fndata#set_library_stub;
          chlog#add
            "ELF library stub relocated"
            (LBLOCK [faddr#toPretty; STR ": "; STR fndata#get_function_name])
        end
      else
        chlog#add
          "no stub name found"
          (LBLOCK [
               faddr#toPretty;
               STR " -> ";
               addr#toPretty;
               STR " (imm8_1h: ";
               STR imm8_1h;
               STR "; offset1: ";
               offset1#toPretty;
               STR "; offset2: ";
               INT offset2;
               STR "; imm12_4h: ";
               STR imm12_4h;
               STR ")"])
    else
      chlog#add "no string match for stub" faddr#toPretty
  else
    chlog#add "presumed library stub not a program address" faddr#toPretty


let get_so_target (tgtaddr:doubleword_int) (_instr:arm_assembly_instruction_int) =
  if functions_data#has_function_name tgtaddr then
    let fndata = functions_data#get_function tgtaddr in
    if fndata#is_library_stub then
      Some fndata#get_function_name
    else if function_summary_library#has_so_function fndata#get_function_name then
      Some fndata#get_function_name
    else
      None
  else
    None


(* can be used before functions have been constructed *)
let is_nr_call_instruction (instr:arm_assembly_instruction_int) =
  match instr#get_opcode with
  | BranchLink (ACCAlways, tgt)
    | BranchLinkExchange (ACCAlways, tgt) when tgt#is_absolute_address ->
     let tgtaddr = tgt#get_absolute_address in
     ((functions_data#is_function_entry_point tgtaddr)
      && (functions_data#get_function tgtaddr)#is_non_returning)
  | _ -> false


let is_maybe_nr_call_instruction (instr: arm_assembly_instruction_int) =
  match instr#get_opcode with
  | BranchLink (ACCAlways, tgt)
    | BranchLinkExchange (ACCAlways, tgt) when tgt#is_absolute_address ->
     let tgtaddr = tgt#get_absolute_address in
     ((functions_data#is_function_entry_point tgtaddr)
      && (functions_data#get_function tgtaddr)#is_maybe_non_returning)
  | _ -> false



let collect_function_entry_points () =
  let addresses = new DoublewordCollections.set_t in
  begin
    !arm_assembly_instructions#itera
      (fun _va instr ->
        match instr#get_opcode with
        | BranchLink (_,op)
          | BranchLinkExchange (_,op) when op#is_absolute_address ->
           (match get_so_target op#get_absolute_address instr with
            | Some sym ->
               (functions_data#add_function op#get_absolute_address)#add_name sym
            | _ -> addresses#add op#get_absolute_address)
        | _ -> ()) ;
    addresses#toList
  end


let collect_call_targets () =
  !arm_assembly_instructions#itera
    (fun _va instr ->
      match instr#get_opcode with
      | BranchLink (_, op)
        | BranchLinkExchange (_, op) when op#is_absolute_address ->
         let tgtaddr = op#get_absolute_address in
         if functions_data#is_function_entry_point tgtaddr then
           let fndata = functions_data#get_function tgtaddr in
           fndata#add_callsite
      | _ -> ())


let set_block_boundaries () =
  let set_inlined_call (a: doubleword_int) =
    log_titer
      (mk_tracelog_spec
         ~tag:"set_block_boundaries"
         ("set_inlined_call:" ^ a#to_hex_string))
      (fun instr -> instr#set_inlined_call)
      (get_arm_assembly_instruction a) in
  let set_block_entry a =
    let instr =
      fail_tvalue
        (trerror_record
           (LBLOCK [STR "set_block_boundaries:set_block_entry: "; a#toPretty]))
        (get_arm_assembly_instruction a) in
    instr#set_block_entry in

  (* Return (follow-instr-addr, conditional-instructions-addresses) or None
     if a next address cannot be found.*)
  let get_iftxf (iaddr: doubleword_int) (ninstr: int):
        (doubleword_int * doubleword_int list) option =
    let get_next_iaddr = get_next_valid_instruction_address in
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

  let feps = functions_data#get_function_entry_points in
  let datablocks = system_info#get_data_blocks in
  begin
    (* -------------------------------- record function entry points -- *)
    List.iter
      (fun fe ->
        try
          set_block_entry fe
        with
        | BCH_failure _ ->
           chlog#add
             "disassembly"
             (LBLOCK [
                  STR "function entry point incorrect: ";
                  fe#toPretty])) feps;

    (* -------------------------------- record end of data blocks -- *)
    List.iter
      (fun db ->
        try
          set_block_entry db#get_end_address
        with
        | BCH_failure _ ->
           chlog#add
             "disassembly"
             (LBLOCK [
                  STR "data block end address incorrect: ";
                  db#get_end_address#toPretty])) datablocks;

    (* --------------------------------------- record jumptables -- *)
    List.iter
      (fun jt ->
        try
          List.iter set_block_entry jt#get_all_targets
        with
        | BCH_failure _ ->
           ch_error_log#add
             "disassembly"
             (LBLOCK [
                  STR "jump table target address incorrect: ";
                  jt#toPretty
                    ~is_function_entry_point:(fun _ -> false)
                    ~get_opt_function_name:(fun _ -> None)]))
      system_info#get_jumptables;

    (* ------------------- record targets of unconditional jumps -- *)
    !arm_assembly_instructions#itera
      (fun va instr ->
        try
          (match instr#get_opcode with
           | Branch (_, op, _)
             | BranchExchange (_,op)
             | CompareBranchNonzero (_, op)
             | CompareBranchZero (_, op) ->
              if op#is_absolute_address then
                let jmpaddr = op#get_absolute_address in
                set_block_entry jmpaddr;
              else
                ()

           (* Thumb-2 IfThen construct:
              va0: ITT c
              va1: if c .. .
              va2: if   c ...
              va3: next instruction (fall-through)
            *)
           | IfThen (_c, xyz) when (xyz = "T") || (xyz = "TT") ->
              let n_instrs = (String.length xyz) + 2 in
              (match get_iftxf va n_instrs with
               | Some (followva, conditional_vas)
                    when (List.length conditional_vas) = (n_instrs - 1) ->
                  let c_instrs =
                    List.fold_left (fun optresult va ->
                        match optresult with
                        | None -> None
                        | Some instrs ->
                           log_tfold
                             (log_error
                                "set_block_boundaries:ifthen"
                                "invalid instruction")
                             ~ok:(fun instr -> Some (instr :: instrs))
                             ~error:(fun _ -> None)
                             (get_arm_assembly_instruction va))
                      (Some []) conditional_vas in
                  (match c_instrs with
                   | Some instrs ->
                      begin
                        set_block_entry (List.hd conditional_vas);
                        set_block_entry followva;
                        instr#set_block_condition;
                        List.iter (fun c_instr ->
                            c_instr#set_condition_covered_by va) instrs;
                        chlog#add
                          "IfThen conditional block"
                          (LBLOCK [
                               va#toPretty;
                               STR ": ";
                               STR xyz;
                               STR "; true block entry: ";
                               (List.hd conditional_vas)#toPretty;
                               STR "; false block entry: ";
                               followva#toPretty])
                      end
                   | _ ->
                      ch_error_log#add
                        "set_block_boundaries:IfThen"
                        (LBLOCK [
                             va#toPretty; STR ": Error in getting instructions"]))
               | _ ->
                  ch_error_log#add
                    "set_block_boundaries:IfThen"
                    (LBLOCK [
                         va#toPretty;
                         STR ": Error in getting instruction addresses"]))
(*
           | IfThen (c, xyz)
                when (xyz = "")
                     && (let nextva_r = get_next_valid_instruction_address va in
                         match TR.to_option nextva_r with
                         | Some nextva ->
                            (log_tfold
                               (log_error
                                  "set_block_boundaries:ifthen"
                                  "invalid instruction")
                               ~ok:(fun instr ->
                                 match instr#get_opcode with
                                 | Pop (_, _, rl, _) -> rl#includes_pc
                                 | _ -> false)
                               ~error:(fun _ -> false)
                               (get_arm_assembly_instruction nextva))
                         | _ -> false) ->
              instr#set_block_condition *)

           (* make a conditional return a separate block, so that it can be
              contextualized with a ConditionContext

              The problem  with this approach is that the condition now is
              in a different block and thus not connected. It is better to
              treat a conditional return in the same way as a conditional
              branch.
           | Pop (_, _, rl, _)
                when rl#includes_pc && is_opcode_conditional instr#get_opcode ->
              set_block_entry va
            *)

           | BranchLink _ | BranchLinkExchange _
                when is_nr_call_instruction instr
                     || is_maybe_nr_call_instruction instr ->
              set_block_entry (va#add_int 4)

           | _ -> ())
        with
        | BCH_failure p ->
           chlog#add
             "disassembly"
             (LBLOCK [
                  STR "assembly instruction creates incorrect block entry: ";
                  instr#toPretty;
                  STR ": ";
                  p]));

    (* -------------------------- incorporate jump successors -- *)
    !arm_assembly_instructions#itera
      (fun va _ ->
        match system_info#get_successors va with
        | [] -> ()
        | l ->
           begin
             List.iter set_block_entry l;
             set_block_entry (va#add_int 4)
           end);

    (* --------------- add block entries due to previous block-ending -- *)
    !arm_assembly_instructions#itera
      (fun va instr ->
        let opcode = instr#get_opcode in
        let is_block_ending =
          match opcode with
          | Pop (_, _, rl, _) -> rl#includes_pc
          | Move (_, _, dst, _, _, _) ->
             dst#is_register && dst#get_register = ARPC
          | Branch _ | BranchExchange _ ->
             (* Don't break up TBB/TBH and other jumptable sequences *)
             (match instr#is_in_aggregate with
              | Some dw -> not (get_aggregate dw)#is_jumptable
              | _ -> true)
          | CompareBranchZero _ | CompareBranchNonzero _ -> true
          | LoadRegister (_, dst, _, _, _, _)
               when dst#is_register
                    && dst#get_register = ARPC
                    && Option.is_none instr#is_in_aggregate -> true
          | LoadMultipleDecrementBefore (_, _, _, rl, _)
            | LoadMultipleDecrementAfter (_, _, _, rl, _)
            | LoadMultipleIncrementBefore (_, _, _, rl, _)
            | LoadMultipleIncrementAfter (_, _, _, rl, _) when rl#includes_pc ->
             true
          | BranchLink (_, op) | BranchLinkExchange (_, op)
               when op#is_absolute_address
                    && (system_info#is_inlined_function op#get_absolute_address
                        || system_info#is_trampoline_payload op#get_absolute_address) ->
             begin
               chlog#add "add inlined call" va#toPretty;
               set_inlined_call va;
               true
             end
          | PermanentlyUndefined _ -> true
          | _ -> false in
        if is_block_ending && has_next_valid_instruction va then
          let nextva =
            fail_tvalue
              (trerror_record
                 (LBLOCK [STR "Internal error in set_block_boundaries"]))
              (get_next_valid_instruction_address va) in
          set_block_entry nextva
        else
          ())
  end


let check_function_validity (fn: arm_assembly_function_int): bool =
  let result = ref true in
  begin
    fn#iteri (fun _ _ instr ->
        if !result then
          match instr#get_opcode with
          | NotRecognized _ -> result := false
          | PermanentlyUndefined _ -> result := false
          | _ -> ());
    !result
  end


(* Returns a list of newly discovered function entry points (obtained from
   tail calls) *)
let construct_assembly_function
      ?(check=false) (_count:int) (faddr:doubleword_int): doubleword_int list =
      try
        let newfns =
          if !arm_assembly_instructions#is_code_address faddr then
            let (newfns, fn) = construct_arm_assembly_function faddr in
            if (check && check_function_validity fn) || not check then
              begin
                arm_assembly_functions#add_function fn;
                newfns
              end
            else
              begin
                chlog#add "abandon function" fn#get_address#toPretty;
                []
              end
          else
            [] in
        newfns
      with
      | BCH_failure p ->
         begin
           ch_error_log#add
             "construct assembly function"
             (LBLOCK [faddr#toPretty; STR ": "; p]);
           raise
             (BCH_failure
                (LBLOCK [
                     STR "Error in constructing function ";
                     faddr#toPretty;
                     STR ": ";
                     p]))
         end


let record_call_targets_arm () =
  arm_assembly_functions#itera
    (fun faddr f ->
      let finfo = get_function_info faddr in
      try
        begin
          f#iteri
            (fun _ ctxtiaddr instr ->
              match instr#get_opcode with
              | BranchLink (_, op)
                | BranchLinkExchange (_, op) ->
                 if finfo#has_call_target ctxtiaddr
                    && not (finfo#get_call_target ctxtiaddr)#is_unknown then
                   let loc = ctxt_string_to_location faddr ctxtiaddr in
                   let floc = get_floc loc in
                   floc#update_call_target
                 else if op#is_absolute_address then
                   begin
                     match get_so_target op#get_absolute_address instr with
                     | Some tgt ->
                        finfo#set_call_target ctxtiaddr (mk_so_target tgt)
                     | _ ->
                        finfo#set_call_target
                          ctxtiaddr (mk_app_target op#get_absolute_address)
                   end
                 else
                   let iaddr = instr#get_address in
                   if system_info#has_call_target faddr iaddr then
                     let calltgt = system_info#get_call_target faddr iaddr in
                     let ctinfo = mk_call_target_info calltgt in
                     finfo#set_call_target ctxtiaddr ctinfo
                   else
                     finfo#set_call_target ctxtiaddr (mk_unknown_target ())
              | Branch (_, tgt, _) when
                     tgt#is_absolute_address
                     && functions_data#is_function_entry_point
                          tgt#get_absolute_address ->
                 if finfo#has_call_target ctxtiaddr
                    && not (finfo#get_call_target ctxtiaddr)#is_unknown then
                   let loc = ctxt_string_to_location faddr ctxtiaddr in
                   let floc = get_floc loc in
                   floc#update_call_target
                 else
                   begin
                     match get_so_target tgt#get_absolute_address instr with
                     | Some tgt ->
                        finfo#set_call_target ctxtiaddr (mk_so_target tgt)
                     | _ ->
                        finfo#set_call_target
                          ctxtiaddr (mk_app_target tgt#get_absolute_address)
                   end
              | Branch _
                | BranchExchange _
                   when system_info#has_call_target faddr instr#get_address ->
                 let calltgt = system_info#get_call_target faddr instr#get_address in
                 let ctinfo = mk_call_target_info calltgt in
                 let _ =
                   chlog#add
                     "call-back table target"
                     (LBLOCK [
                          STR "(";
                          faddr#toPretty;
                          STR ", ";
                          STR ctxtiaddr;
                          STR "): ";
                          ctinfo#toPretty
                        ]) in
                 finfo#set_call_target ctxtiaddr ctinfo

              | _ -> ())
        end
      with
      | BCH_failure p ->
         ch_error_log#add
           "record-call-targets-arm"
           (LBLOCK [STR "Function: "; faddr#toPretty; STR ": "; p]))

(* ---------------------------------------------------------------------
   associate conditional jump instructions with the closest instruction
   (within the same basic block) that sets the flags
   ---------------------------------------------------------------------- *)
let associate_condition_code_users () =
  let set_condition
        (flags_used: arm_cc_flag_t list)
        (faddr: doubleword_int)
        (ctxtiaddr:ctxt_iaddress_t)
        (block: arm_assembly_block_int) =
    let finfo = get_function_info faddr in
    let loc = ctxt_string_to_location faddr ctxtiaddr in
    let revInstrs: arm_assembly_instruction_int list =
      block#get_instructions_rev ~high:loc#i () in

    (* remove the conditional instruction itself *)
    let revInstrs: arm_assembly_instruction_int list =
      match revInstrs with
      | _::tl -> tl
      | [] -> [] in
    let rec set l =
      match l with
      | [] ->
         log_titer
           (mk_tracelog_spec
              ~tag:"associate_condition_code_users"
              ("set:" ^ loc#i#to_hex_string))
           (fun instr ->
	     chlog#add
               "cc user without setter"
	       (LBLOCK [loc#toPretty; STR ": " ; instr#toPretty]))
	   (get_arm_assembly_instruction loc#i)
      | instr :: tl ->
	match get_arm_flags_set instr#get_opcode with
	| [] -> set tl
	| flags_set ->
	  if List.for_all (fun fUsed -> List.mem fUsed flags_set) flags_used then
             let iloc = ctxt_string_to_location faddr ctxtiaddr in
             let instrctxt = (make_i_location iloc instr#get_address)#ci in
	    finfo#connect_cc_user ctxtiaddr instrctxt in
    set revInstrs in
  let count = ref 0 in
  arm_assembly_functions#itera
    (fun faddr f ->
      begin
        f#iter
	  (fun block ->
	    block#itera
	      (fun iaddr instr ->
	        match get_arm_flags_used instr#get_opcode with
	        | [] -> ()
	        | flags -> set_condition flags faddr iaddr block));
        count := !count + 1;
        pr_interval_timing [STR "  associate condition codes: "; INT !count] 60.0
      end)


let construct_functions_arm ?(construct_all_functions=false) () =
  let _ =
    system_info#initialize_function_entry_points collect_function_entry_points in
  let fns_included = included_functions () in
  let _ =
    List.iter
      (fun dw -> ignore (functions_data#add_function dw))
      (List.map (fun s -> TR.tget_ok (string_to_doubleword s)) fns_included) in
  let _ = collect_call_targets () in
  let _ = set_block_boundaries () in
  let _ = pr_timing [STR "block boundaries set"] in
  let _ = !arm_assembly_instructions#collect_callsites in
  let _ = pr_timing [STR "callsites collected"] in
  let _ =
    let nonrfns = arm_callsites_records#get_non_returning_functions in
    List.iter (fun faddr ->
        if functions_data#is_function_entry_point faddr then
          let fndata = functions_data#get_function faddr in
          fndata#set_non_returning) nonrfns in
  let _ = pr_timing [STR "non-returning functions set"] in
  let fnentrypoints =
    if ((List.length fns_included) = 0) || construct_all_functions then
      functions_data#get_function_entry_points
    else
      (* Add inlined functions to have these functions constructed before the
         functions that inline these functions are constructed, so the cfgs are
         available for the inlined calls *)
      functions_data#get_inlined_function_entry_points
      @ (List.map
           (fun faddr -> TR.tget_ok (string_to_doubleword faddr)) fns_included) in
  let newfns = ref fnentrypoints in
  let count = ref 0 in
  let addedfns = new DoublewordCollections.set_t in
  begin
    while (List.length !newfns) > 0 do
      begin
        List.iter
          (fun faddr ->
            let default () =
              try
                let _ = count := !count + 1 in
                let newfunctions = construct_assembly_function !count faddr in
                let _ =
                  pr_interval_timing [
                      STR "functions constructed: "; INT !count] 60.0 in
                addedfns#addList newfunctions
              with
              | BCH_failure p ->
                 ch_error_log#add
                   "construct functions"
                   (LBLOCK [STR "Function "; faddr#toPretty; STR ": "; p]) in
            if functions_data#is_function_entry_point faddr then
              let fndata = functions_data#get_function faddr in
              if fndata#is_library_stub then
                ()
              else if fndata#has_name then
                if is_library_stub faddr then
                  begin
                    fndata#set_library_stub;
                    chlog#add
                      "ELF library stub"
                      (LBLOCK [
                           faddr#toPretty; STR ": "; STR fndata#get_function_name])
                  end
                else
                  default ()
              else if is_library_stub faddr then
                begin
                  fndata#set_library_stub;
                  set_library_stub_name faddr
                end
              else
                default ()
            else
              ch_error_log#add
                "no function found"
                (LBLOCK [STR "construct functions: "; faddr#toPretty])
          ) !newfns;
        newfns := addedfns#toList;
        addedfns#removeList addedfns#toList
      end
    done;

    pr_timing [STR "functions constructed ("; INT !count; STR ") -- first pass"];
    arm_assembly_functions#identify_dataref_datablocks;
    pr_timing [STR "datablocks identified -- first pass"];

    (if (List.length fns_included) = 0 || construct_all_functions then
      begin
        List.iter (fun faddr ->
            begin
              count := !count + 1;
              ignore (construct_assembly_function ~check:true !count faddr);
              pr_interval_timing [STR "functions constructed: "; INT !count] 60.0
            end) arm_assembly_functions#add_functions_by_preamble;

        pr_timing [
            STR "functions constructed ("; INT !count; STR ") -- second pass"];
        arm_assembly_functions#identify_dataref_datablocks;
        pr_timing [STR "dataref blocks identified"];
      end);

    arm_assembly_functions#apply_path_contexts;

    record_call_targets_arm ();
    pr_timing [STR "call targets recorded"];
    associate_condition_code_users ();
    pr_timing [STR "condition-codes associated"];
    if (List.length fns_included) = 0 then
      begin
        arm_assembly_functions#identify_datablocks;
        pr_timing [STR "datablocks identified"]
      end
  end

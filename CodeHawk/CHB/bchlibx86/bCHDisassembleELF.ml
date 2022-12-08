(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHUtil

(* xprlib *)
open Xprt
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHFloc
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionInfo
open BCHJumpTable
open BCHLibTypes
open BCHLocation
open BCHMakeCallTargetInfo
open BCHStreamWrapper
open BCHSystemInfo
open BCHUtilities

(* bchlibelf *)
open BCHELFHeader
open BCHELFTypes

(* bchlibx86 *)
open BCHAssemblyBlock
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHAssemblyInstruction
open BCHAssemblyInstructions
open BCHDisassembleInstruction
open BCHDisassemblyUtils
open BCHLibx86Types
open BCHOperand
open BCHPredefinedCallSemantics
open BCHX86OpcodeRecords

module TR = CHTraceResult

module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)


let pr_expr = xpr_formatter#pr_expr
let x2p = xpr_formatter#pr_expr


let disassemble (base:doubleword_int) (displacement:int) (x:string) =
  let add_instruction position opcode bytes =
    let index = position + displacement in
    let addr = base#add_int position in
    let instruction = make_assembly_instruction addr opcode bytes in
    !assembly_instructions#set index instruction in
  let ch = make_pushback_stream x in
  let size = String.length x in
  try
    while ch#pos < size do
      let prevPos = ch#pos in
      let firstByte = ch#read_byte in
      let opcode = disassemble_instruction ch base firstByte in
      let currentPos = ch#pos in
      let instrLen = currentPos - prevPos in
      let instrBytes = Bytes.make instrLen ' ' in
      let _ = Bytes.blit (Bytes.of_string x) prevPos instrBytes 0 instrLen in
      let _ = add_instruction prevPos opcode (Bytes.to_string instrBytes) in
      ()
    done
  with
  | BCH_failure p ->
    ch_error_log#add "disassembly"
      (LBLOCK [ STR "failure in disassembly: " ; p ])

let disassemble_elf_sections () =
  let xSections = elf_header#get_executable_sections in
  let headers =
    List.sort (fun (h1,_) (h2,_) ->
        h1#get_addr#compare h2#get_addr) xSections in
  let (lowest,_) = List.hd headers in
  let (highest,_) = List.hd (List.rev headers) in
  let startOfCode = lowest#get_addr in
  let endOfCode = highest#get_addr#add highest#get_size in
  let sizeOfCode = TR.tget_ok (endOfCode#subtract startOfCode) in
  let _ = initialize_instructions sizeOfCode#to_int in
  let _ =
    chlog#add
      "initialization"
      (LBLOCK [
           STR "Create space for ";
           sizeOfCode#toPretty;
           STR " (";
	   INT sizeOfCode#to_int;
           STR ")";
           STR "instructions"]) in
  let _ =
    initialize_assembly_instructions
      0 sizeOfCode#to_int sizeOfCode#to_int startOfCode [] [] in
  let _ =
    List.iter
      (fun (h,x) ->
        let displacement =
          TR.tget_ok (h#get_addr#subtract_to_int startOfCode) in
        disassemble h#get_addr displacement x) xSections in
  sizeOfCode


let get_indirect_jump_targets (op:operand_int) =
  if op#is_jump_table_target then
    let (jumpbase,reg) = op#get_jump_table_target in
    try
      let jumpbase = TR.tget_ok (numerical_to_doubleword jumpbase) in
      match system_info#is_in_jumptable jumpbase with
      | Some jt -> Some (jumpbase, jt, reg)
      | _ -> 
         begin
	   chlog#add
             "jump table"
	     (LBLOCK [STR "not found for offset "; jumpbase#toPretty]);
	   match elf_header#get_containing_section jumpbase with
           | Some s ->
              begin
                chlog#add "jumpbase section" (s#toPretty) ;
                match create_jumptable
                        ~base:jumpbase
                        ~section_base:s#get_vaddr
                        ~is_code_address:system_info#is_code_address
                        ~section_string:s#get_xstring  with
                | Some jt ->
                  begin
                    chlog#add
                      "add jumptable"
                      (LBLOCK [
                           jt#get_start_address#toPretty;
                           STR "; length: ";
                           INT jt#get_length]);
                    Some (jumpbase,jt,reg)
                  end
                | _ ->
                   begin
                     chlog#add "add jumptable" (STR  "not created");
                     None
                   end
              end
           | _ ->
              begin
                chlog#add "jumpbase section" (STR "not found");
                None
              end
         end
    with
    | Invalid_argument s ->
      begin
	ch_error_log#add
          "invalid argument"
	  (LBLOCK [
               STR "get_indirect_jump_targets: ";
               STR s;
               STR ": ";
	       op#toPretty]);
	None
      end
  else
    None


let get_so_target (instr:assembly_instruction_int) =
  (*
     I:  ...: call a      text section
          a : jump *b
         ------------------
          b : c           relocation table mapping to symbol

     II: ...: call a
          a : jump* ebx[offset]
         -------------------
          ebx+offset: c    relocatiob table mapping to symbol
   *)
  let check_case_I tgtaddr =
    if !assembly_instructions#is_code_address tgtaddr then
      let tgtopc = (!assembly_instructions#at_address tgtaddr)#get_opcode in
      match tgtopc with
      | IndirectJmp jmptgt ->
         if jmptgt#is_absolute_address then
           elf_header#get_relocation jmptgt#get_absolute_address
         else
           None
      | _ -> None
    else
      None in
  match instr#get_opcode with
  | DirectCall op when op#is_absolute_address -> check_case_I op#get_absolute_address
  | _ -> None


let is_so_target (instr:assembly_instruction_int) =
  match get_so_target instr with Some _ -> true | _ -> false

(* ------------------------------------------- position-independent code (pic) *)

let get_pic_so_target (refebx:numerical_t) (instr:assembly_instruction_int) =
  (*
       II: ...: call a
          a : jump* ebx[offset]
         -------------------
          ebx+offset: c    relocatiob table mapping to symbol
   *)
  let check_case_II tgtaddr =
    if !assembly_instructions#is_code_address tgtaddr then
      let tgtopc = (!assembly_instructions#at_address tgtaddr)#get_opcode in
      match tgtopc with
      | IndirectJmp jmptgt ->
         if jmptgt#is_indirect_register && (jmptgt#get_indirect_register = Ebx) then
           let symboloffset = refebx#add jmptgt#get_indirect_register_offset in
           elf_header#get_relocation
             (TR.tget_ok (numerical_to_doubleword symboloffset))
         else
           None
      | _ -> None
    else
      None  in
  match instr#get_opcode with
  | DirectCall op -> check_case_II op#get_absolute_address
  | _ -> None


let is_pic_so_target (instr:assembly_instruction_int) =
  let check_case_II tgtaddr =
    if !assembly_instructions#is_code_address tgtaddr then
      let tgtopc = (!assembly_instructions#at_address tgtaddr)#get_opcode in
      match tgtopc with
      | IndirectJmp jmptgt ->
         jmptgt#is_indirect_register && (jmptgt#get_indirect_register = Ebx) 
      | _ -> false
    else
      false  in
  match instr#get_opcode with
  | DirectCall op -> check_case_II op#get_absolute_address
  | _ -> false


let resolve_pic_target floc instr =
  if is_pic_so_target instr then
    let ebxvar = floc#f#env#mk_cpu_register_variable Ebx in
    if floc#is_constant ebxvar then
      let ebxvalue = floc#get_constant ebxvar in
      match get_pic_so_target ebxvalue instr with
      | Some tgt ->
         begin
           chlog#add "pic target" (LBLOCK [ STR floc#cia ; STR ": " ; STR tgt ]) ;
           floc#set_call_target (mk_so_target tgt) ;
           (*  check_non_returning floc *)
         end
      | _ -> ()
    else
      ()
  else
    ()


let resolve_pic_targets faddr f =
  f#iteri
    (fun _ ctxtiaddr instr ->
      let loc = ctxt_string_to_location faddr ctxtiaddr in
      let floc = get_floc loc in
      resolve_pic_target floc instr)

(* -------------------------------------------------------------------------- *)
  
let collect_function_entry_points () =
  let addresses = new DoublewordCollections.set_t in
  begin
    !assembly_instructions#itera
     (fun va instr ->
       match instr#get_opcode with
       | DirectCall op when op#is_absolute_address ->
          (match get_so_target instr with
           | Some sym ->
              (functions_data#add_function op#get_absolute_address)#add_name sym
           | _ -> addresses#add op#get_absolute_address)
       | _ -> ()) ;
    addresses#toList
  end


let is_nr_call_instruction (instr:assembly_instruction_int) =
  match instr#get_opcode with
  | DirectCall op when op#is_absolute_address ->
     let faddr = op#get_absolute_address in
     (functions_data#is_function_entry_point faddr)
     && (functions_data#get_function faddr)#is_non_returning
  | _ -> false


let set_block_boundaries () =
  let set_block_entry a = (!assembly_instructions#at_address a)#set_block_entry in
  let is_in_range = !assembly_instructions#is_in_code_range in
  let feps = functions_data#get_function_entry_points in
  begin
    (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ record function entry points *)
    List.iter
      (fun fe ->
        try
          set_block_entry fe
        with
	| BCH_failure _ ->
	   chlog#add
             "disassembly"
	     (LBLOCK [STR "function entry point incorrect: "; fe#toPretty])
	| Invalid_argument s ->
	   ch_error_log#add
             "disassembly"
	     (LBLOCK [
                  STR "function entry point problem: ";
                  fe#toPretty;
		  STR ": ";
                  STR s])
      ) feps;

    (* ~~~~~~~~~~~~~~~~ record targets of unconditional and conditional jumps *)
    !assembly_instructions#itera
     (fun _ instr ->
       try
         let opcode = instr#get_opcode in
         if is_direct_jump_instruction instr#get_opcode then
	   let targetOp =
	     match get_operands opcode with
             | [op] | [op; _] -> op
             | _ ->
	        raise
                  (BCH_failure
		     (LBLOCK [
                          STR "Internal error in set_block_boundaries "])) in
           if targetOp#is_absolute_address then
             let targetAddress = targetOp#get_absolute_address in
             if is_in_range targetAddress then
               set_block_entry targetAddress
             else
               ()
           else
             ()
         else
           ()
       with
       | BCH_failure p ->
	  chlog#add
            "disassembly" 
	    (LBLOCK [
                 STR "assembly instruction creates incorrect block entry: ";
		 instr#toPretty;
                 STR ": ";
                 p])
     );
    
    (* ~~~~~~~~~~~ add block entries due to previous block-ending instruction *)
    !assembly_instructions#itera
      (fun va instr ->
	let opcode = instr#get_opcode in
	let isBlockEnding = 
	  is_jump_instruction opcode || 
	    (match opcode with 
	     | Ret _ | BndRet _ | RepzRet | InterruptReturn _ | Halt -> true
	     | IndirectCall _ | DirectCall _ -> is_nr_call_instruction instr
	     |	_ -> false) in
	if isBlockEnding
           && !assembly_instructions#has_next_valid_instruction va then
	  set_block_entry
            (!assembly_instructions#get_next_valid_instruction_address va)
	else
	  ())
  end


let get_return_successors (floc:floc_int) =
  if system_info#is_goto_return floc#ia then
    [system_info#get_goto_return floc#ia]
  else
    let (level,espoffset) = floc#get_stackpointer_offset "x86" in
    match espoffset#singleton with
    | Some num when num#equal numerical_zero -> []
    | Some num ->
      begin
	let stackRhs = (esp_deref RD)#to_variable floc in
	let dst = 
	  floc#inv#rewrite_expr (XVar stackRhs) floc#env#get_variable_comparator in
	match dst with
	| XConst (IntConst n) ->
	  let addr = TR.tget_ok (numerical_to_doubleword n) in
	  if system_info#is_code_address addr then
	    begin
	      system_info#add_goto_return floc#ia addr;
	      [addr]
	    end
	  else
	    begin
	      ch_error_log#add
                "invalid goto return address"
		(LBLOCK [
                     floc#l#toPretty;
                     STR ": ";
                     addr#toPretty;
		     STR "(offset: ";
                     num#toPretty;
                     STR ")"]);
	      []
	    end
	| _ ->
	  begin
	    ch_error_log#add
              "indeterminate goto return address"
	      (LBLOCK [
                   floc#l#toPretty;
                   STR ": ";
                   pr_expr dst;
		   STR " with offset ";
                   num#toPretty]);
	    []
	  end
      end
    | _ -> []


let is_so_jump_target (target_address:doubleword_int) =
  match elf_header#get_relocation target_address with
  | Some _ -> true
  | _ -> false


(* it is assumed that these are successors to a toplevel block;
   blocks of inlined functions are incorporated all at once *)
let get_successors (faddr:doubleword_int) (iaddr:doubleword_int) =
  if system_info#is_nonreturning_call faddr iaddr then
    []
  else
    let loc = make_location {loc_faddr = faddr; loc_iaddr = iaddr} in
    let floc = get_floc loc in
    let ctxtiaddr = loc#ci in
    let instr = !assembly_instructions#at_address iaddr in
    let finfo = get_function_info faddr in
    let opcode = instr#get_opcode in
    let next () =
      if !assembly_instructions#has_next_valid_instruction iaddr then
        [!assembly_instructions#get_next_valid_instruction_address iaddr]
      else
        begin
          chlog#add
            "disassembly"
            (LBLOCK [
                 STR "Next instruction for ";
                 iaddr#toPretty;
                 STR " ";
                 instr#toPretty;
                 STR " was not found"]);
          []
        end in
    let is_so_jump_target_op op =
      (op#is_absolute_address && is_so_jump_target op#get_absolute_address) in
    let get_so_jump_target_op op =
      let dw =
        if op#is_absolute_address then
          op#get_absolute_address
        else
          raise
            (BCH_failure (STR "Unexpected operand in get_so_jump_target_op")) in
      match elf_header#get_relocation dw  with
      | Some fname -> fname
      | _ -> raise
               (BCH_failure
                  (LBLOCK [
                       STR "Unable to find relocation object for ";
                            dw#toPretty])) in
    let successors = match opcode with
      | RepzRet | Ret None | BndRet None -> get_return_successors (get_floc loc)
      | Ret _ | BndRet _ | Halt -> []
      | DirectJmp op
        | CfJmp (op,_,_) when op#is_absolute_address -> [op#get_absolute_address]
      | Jcc (_,op)
           when system_info#is_fixed_true_branch iaddr && op#is_absolute_address ->
         [op#get_absolute_address]
      | IndirectJmp _ when system_info#has_jump_target iaddr ->
         let (base,jt,db) = system_info#get_jump_target iaddr in
         begin
           finfo#set_offsettable_target ctxtiaddr base jt db;
           (get_floc loc)#get_jump_successors
         end
      | IndirectJmp _ when finfo#has_jump_target ctxtiaddr ->
         (get_floc loc)#get_jump_successors
      | IndirectJmp op when finfo#is_dll_jumptarget ctxtiaddr -> []
      | IndirectJmp op when is_so_jump_target_op op ->
         let fname = get_so_jump_target_op op in
         let ctinfo = mk_so_target fname in
         begin
           finfo#set_so_jumptarget ctxtiaddr fname ctinfo;
           chlog#add
             "so library call:get_successors:get_indirect_jump_target"
             (LBLOCK [
                  faddr#toPretty;
                  STR ",";
                  iaddr#toPretty;
                  STR ": ";
                  STR fname]);
           []
         end
      | IndirectJmp op when op#is_jump_table_target ->
         let floc = get_floc loc in
         (match get_indirect_jump_targets op with
          | Some  (jumpbase,table,reg) ->
             begin
               finfo#set_jumptable_target ctxtiaddr jumpbase table reg;
               floc#get_jump_successors
             end
          | _ ->
             let tgtexpr = op#to_expr floc in
             begin
               chlog#add
                 "indirect jump"
                 (LBLOCK [floc#l#toPretty; STR ": "; x2p tgtexpr]);
               []
             end)
      | IndirectJmp op ->
         let floc = get_floc loc in
         begin
           finfo#set_unknown_jumptarget ctxtiaddr ;
           chlog#add
             "unknown jump target"
             (LBLOCK [floc#l#toPretty; STR ": "; op#toPretty]);
           []
         end
      | IndirectCall _ | DirectCall _
           when floc#has_call_target && floc#get_call_target#is_nonreturning ->
         (* when finfo#is_nonreturning_call ctxtiaddr -> *)
         []
      | DirectCall op when
             op#is_absolute_address
             && (functions_data#get_function
                   op#get_absolute_address)#is_non_returning ->
         []
      | DirectLoop op ->
         if op#is_absolute_address then
           (next ()) @ [op#get_absolute_address]
         else
           begin
             chlog#add
               "disassembly:DirectLoop"
               (LBLOCK [
                    STR "Target operand of loop instruction is not ";
                    STR "an absolute address: ";
                    iaddr#toPretty;
                    STR " ";
                    op#toPretty]);
             (next ())
           end
      | _ ->
         if is_conditional_jump_instruction opcode then
           let targetOp = get_jump_operand opcode in
           if targetOp#is_absolute_address then
             (next ()) @ [targetOp#get_absolute_address]
           else
             begin
               chlog#add
                 "disassembly:conditional jump"
                 (LBLOCK [
                      STR "Target operand of conditional jump is not ";
                      STR "an absolute address: ";
                      iaddr#toPretty;
                      STR "  ";
                      targetOp#toPretty]);
               (next ())
             end
         else
           (next ()) in
    List.map
      (fun va -> (make_location {loc_faddr = faddr; loc_iaddr = va})#ci)
      (List.filter
         (fun va ->
           if !assembly_instructions#is_code_address va then true else
             begin 
	       chlog#add
                 "disassembly"
	         (LBLOCK [
                      STR "Successor of ";
                      va#toPretty;
		      STR " is not a valid code address"]);
	       false
             end) successors)


let trace_block (faddr:doubleword_int) (baddr:doubleword_int) =
  let set_block_entry a = (!assembly_instructions#at_address a)#set_block_entry in    
  let get_instr = !assembly_instructions#at_address in
  let get_next_instr_address = 
    !assembly_instructions#get_next_valid_instruction_address in

  let rec find_last_instruction (va:doubleword_int) (prev:doubleword_int) =
    let instr = get_instr va in
    let floc = get_floc (make_location {loc_faddr = faddr; loc_iaddr = va}) in
    let _ = floc#set_instruction_bytes instr#get_instruction_bytes in
    if va#equal wordzero then
      (Some [], prev, [])
    else if instr#is_block_entry then 
      (None, prev, [])
    else if floc#has_call_target && floc#get_call_target#is_nonreturning then
      let _ = chlog#add "non-returning" floc#l#toPretty in
      (Some [], va, [])
    else if instr#is_inlined_call then
      let a = match instr#get_opcode with
        | DirectCall op -> op#get_absolute_address
        | _ ->
           raise (BCH_failure (LBLOCK [STR "Internal error in trace block"])) in
      let fn = assembly_functions#get_function_by_address a in
      let returnsite = get_next_instr_address va in
      let _ = set_block_entry returnsite in
      let ctxt =
        FunctionContext
          {ctxt_faddr = faddr;
           ctxt_callsite = a;
           ctxt_returnsite = returnsite} in
      let callloc = make_location {loc_faddr = a; loc_iaddr = a} in
      let ctxtcallloc = make_c_location callloc ctxt in
      let callsucc = ctxtcallloc#ci in 
      let inlinedblocks =
        List.map
          (fun b ->
            let succ =
              match b#get_successors with
              | [] ->
                 [(make_location {loc_faddr = faddr; loc_iaddr = returnsite})#ci]
              | l ->
                 List.map (fun s -> add_ctxt_to_ctxt_string faddr s ctxt) l in
            make_ctxt_assembly_block ctxt b succ) fn#get_blocks in
      (Some [callsucc], va, inlinedblocks)
    else if !assembly_instructions#has_next_valid_instruction va then
      find_last_instruction (get_next_instr_address va) va
    else (None, va, []) in

  let (succ,lastAddress,inlinedblocks) = 
    if !assembly_instructions#has_next_valid_instruction baddr then
      let floc = get_floc (make_location {loc_faddr = faddr; loc_iaddr = baddr}) in
      let _ = floc#set_instruction_bytes (get_instr baddr)#get_instruction_bytes in
      find_last_instruction (get_next_instr_address baddr) baddr
    else (None, baddr, []) in

  let successors = match succ with
    | Some s -> s
    | _ -> get_successors faddr lastAddress in
  (inlinedblocks, make_assembly_block faddr baddr lastAddress successors)
  

let trace_function (faddr:doubleword_int) =
  let workSet = new DoublewordCollections.set_t in
  let doneSet = new DoublewordCollections.set_t in
  let set_block_entry a = (!assembly_instructions#at_address a)#set_block_entry in
  let get_iaddr s = (ctxt_string_to_location faddr s)#i in
  let add_to_workset l = 
    List.iter (fun a -> if doneSet#has a then () else workSet#add a) l in
  let blocks = ref [] in
  let rec add_block (blockEntry:doubleword_int) =
    let (inlinedblocks,block) = trace_block faddr blockEntry in
    let blockSuccessors = block#get_successors in
    begin
      set_block_entry blockEntry;
      workSet#remove blockEntry;
      doneSet#add blockEntry;
      blocks := (block :: inlinedblocks) @ !blocks;
      add_to_workset (List.map get_iaddr blockSuccessors);
      match workSet#choose with Some a -> add_block a | _ -> ()
    end in
  let _ = add_block faddr in
  let blockList =
    List.sort (fun b1 b2 ->
        Stdlib.compare b1#get_context_string b2#get_context_string) !blocks in
  let successors =
    List.fold_left (fun acc b ->
        let src = b#get_context_string in
        (List.map (fun tgt -> (src,tgt)) b#get_successors) @ acc) [] blockList in
  make_assembly_function faddr blockList successors 
  

let construct_assembly_function (count:int) (faddr:doubleword_int) =
  try
    if !assembly_instructions#is_code_address faddr then
      let fn = trace_function faddr in
      assembly_functions#add_function fn
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


let construct_functions () =
  let _ =
    system_info#initialize_function_entry_points collect_function_entry_points in
  let _ = set_block_boundaries () in
  let functionEntryPoints = functions_data#get_function_entry_points in
  let count = ref 0 in
  List.iter (fun faddr ->
      try
        begin
          count := !count + 1;
          construct_assembly_function !count faddr
        end
      with
      | BCH_failure p ->
         ch_error_log#add
           "construct functions"
           (LBLOCK [STR "Function "; faddr#toPretty; STR ": "; p])
    ) functionEntryPoints


let record_call_targets () =
  assembly_functions#itera
    (fun faddr f ->
      try
        let _ = resolve_pic_targets faddr f in
        let finfo = get_function_info faddr in
        begin
          f#iteri
            (fun _  ctxtiaddr instr ->
              let loc = ctxt_string_to_location faddr ctxtiaddr in
              let floc = get_floc loc in
              match instr#get_opcode with
              | DirectCall op when
                     op#is_absolute_address
                     && (get_function_info
                           op#get_absolute_address)#is_dynlib_stub -> ()
              | DirectCall op | IndirectCall op ->
                 if floc#has_call_target
                    && floc#get_call_target#is_app_call then
                   let appaddr = floc#get_call_target#get_app_address in
                   let ctinfo = get_callsemantics_target appaddr in
                   if ctinfo#is_inlined_call then
                     begin
                       floc#set_call_target ctinfo;
                       finfo#schedule_invariant_reset;
                       chlog#add
                         "reset invariants"
                         (LBLOCK [
                              finfo#a#toPretty;
                              STR  ":";
                              STR ctxtiaddr])
                          end
                   else ()
                 else
                   begin
                     match get_so_target instr with
                     | Some tgt -> floc#set_call_target (mk_so_target tgt)
                     | _ ->
                        if is_pic_so_target instr then
                          ()
                        else if op#is_absolute_address then
                          floc#set_call_target
                            (mk_app_target op#get_absolute_address)
                        else
                          floc#set_call_target (mk_unknown_target ())
                   end
              | _ -> ())
        end
      with
      | BCH_failure p ->
         ch_error_log#add
           "record call targets"
           (LBLOCK [STR "function "; faddr#toPretty; STR ": "; p]))


(* ---------------------------------------------------------------------
   associate conditional jump instructions with the closest instruction
   (within the same basic block) that sets the flags                     
   ---------------------------------------------------------------------- *)
let associate_condition_code_users () =
  let set_condition flags_used faddr (ctxtiaddr:ctxt_iaddress_t) block =
    let finfo = get_function_info faddr in
    let revInstrs = block#get_instructions_rev in
    let rec set l =
      match l with
      | [] ->
	  let loc = ctxt_string_to_location faddr ctxtiaddr in
	  disassembly_log#add
            "cc user without setter"
	    (LBLOCK [
                 loc#toPretty;
                 STR ": ";
		 (!assembly_instructions#at_address loc#i)#toPretty])
      | instr :: tl ->
	match get_flags_set instr#get_opcode with
	| [] -> set tl
	| flags_set -> 
	  if List.for_all (fun fUsed -> List.mem fUsed flags_set) flags_used then
             let iloc = ctxt_string_to_location faddr ctxtiaddr in
             let instrctxt = (make_i_location iloc instr#get_address)#ci in
	    finfo#connect_cc_user ctxtiaddr instrctxt in
    set revInstrs in
  assembly_functions#itera
    (fun faddr assemblyFunction ->
      assemblyFunction#iter
	(fun block ->
	  block#itera
	    (fun iaddr instr ->
	      match get_flags_used instr#get_opcode with
	      | [] -> ()
	      | flags -> set_condition flags faddr iaddr block)))


(* -----------------------------------------------------------------------------
   associate values that get pushed onto the stack immediately before a call
   instruction with the call
   ----------------------------------------------------------------------------- *)
let associate_function_arguments_push () =

  let identify_known_arguments
        ~(callAddress:ctxt_iaddress_t)
        ~(numParams:int)
        ~(block:assembly_block_int)
        faddr =
    let argNr = ref 0 in
    let active = ref true in
    let first = ref true in
    let compensateForPop = ref 0 in
    let valid = ref true in
    let callloc = ctxt_string_to_location faddr callAddress  in
    block#itera
      ~high:callloc#i ~reverse:true
      (fun ctxtiaddr instr ->
        if !first then
          first := false   (* skip the call itself *)
        else
          let loc = ctxt_string_to_location faddr ctxtiaddr in          
          if !valid && !active && !argNr < numParams then
            match instr#get_opcode with
            | Pop _ -> compensateForPop := !compensateForPop + 1
            | Push _ when !compensateForPop > 0 ->
               compensateForPop := !compensateForPop - 1
            | Push (_,op) ->
               begin
                 argNr := !argNr + 1 ;
                 op#set_function_argument callAddress !argNr ;
               end
            | DirectCall _ | IndirectCall _ ->
               let floc = get_floc loc in
               if floc#has_call_target
                  && floc#get_call_target#is_signature_valid then
                 match floc#get_call_target#get_stack_adjustment with
                 | Some adj -> compensateForPop := !compensateForPop + (adj / 4)
                 | _ -> valid := false
               else ()
            | Sub (dst,_)
              | Add (dst,_) when dst#is_register && dst#get_cpureg = Esp -> valid := false
            | Mov (4,dst,_)  when dst#is_memory_access ->
               (match dst#get_kind with
                | IndReg (Esp, offset)
                  | ScaledIndReg (None, Some Esp, 1, offset)
                  | ScaledIndReg (Some Esp, None, 1, offset) ->
                   if offset#equal numerical_zero then valid := false
                | _ -> ())
            | _ -> ()) in

  let identify_arguments
        ~(callAddress:ctxt_iaddress_t)
        ~(block:assembly_block_int) =
    let argNr = ref 0 in
    let active = ref true in
    let first = ref true in
    let compensateForPop = ref false in
    let valid = ref true in
    let faddr = block#get_faddr in
    let callloc = ctxt_string_to_location faddr callAddress in
    block#itera
      ~high:callloc#i ~reverse:true
      (fun ctxtiaddr instr ->
        if !first then
          first := false  (* skip the call itself *)
        else  
          if !valid && !active then
            match instr#get_opcode with
            | Pop _ -> compensateForPop := true
            | Push _ when !compensateForPop -> compensateForPop := false
            | Push (_,op) ->
               begin
                 argNr := !argNr + 1 ;
                 op#set_function_argument callAddress !argNr ;
               end
            | Sub (dst,_)
              | Add (dst,_) when dst#is_register && dst#get_cpureg = Esp ->
               valid := false
            | Mov (4,dst,_) when dst#is_memory_access ->
               (match dst#get_kind with
                | IndReg (Esp,offset)
                  | ScaledIndReg (None, Some Esp, 1, offset)
                  | ScaledIndReg (Some Esp, None, 1, offset) ->
                   if offset#equal numerical_zero then valid := false
                | _ -> ())
            | DirectCall _ | IndirectCall _ -> active := false
            | _ -> ()) in

  assembly_functions#itera
    (fun faddr fn ->
      try
        fn#iter
          (fun block ->
            block#itera
              (fun ctxtiaddr instr ->
                let loc = ctxt_string_to_location faddr ctxtiaddr in
                let floc = get_floc loc in
                match instr#get_opcode with
                | DirectCall op when
                       op#is_absolute_address && has_callsemantics op#get_absolute_address ->
                   let semantics = get_callsemantics op#get_absolute_address in
                   let numParams = semantics#get_parametercount in
                   identify_known_arguments ~callAddress:ctxtiaddr ~numParams ~block faddr
                | DirectCall _ | IndirectCall _ ->
                   if floc#has_call_target
                      && floc#get_call_target#is_signature_valid then
                     let fintf = floc#get_call_target#get_function_interface in
                     let numParams = List.length (get_stack_parameter_names fintf) in
                     identify_known_arguments
                       ~callAddress:ctxtiaddr ~numParams ~block faddr
                   else
                     identify_arguments ~callAddress:ctxtiaddr ~block
                | _ -> ()))
      with
      | BCH_failure p ->
         ch_error_log#add
           "associate function arguments (push)"
           (LBLOCK [STR "Function "; faddr#toPretty; STR ": "; p]))


(* -----------------------------------------------------------------------------
   associate values that get moved onto the stack immediately before a call
   instruction with the call
   ----------------------------------------------------------------------------- *)
let associate_function_arguments_mov () =
  let identify_known_arguments
        ~(callAddress:ctxt_iaddress_t)
        ~(numParams:int) 
        ~(block:assembly_block_int) =
    let active = ref true in
    let first = ref true in
    let argumentsFound = ref [] in
    let maxIndex = ref 0 in
    let faddr = block#get_faddr in
    let callloc = ctxt_string_to_location faddr callAddress in
    begin
      block#itera ~high:callloc#i ~reverse:true
	(fun va instr ->
	  if !first then first := false       (* skip the call itself *)
	  else
	    if !active then
	      match instr#get_opcode with
	      | Mov (4, dst, src) when dst#is_esp_offset ->
		 let offset = dst#get_esp_offset#toInt in
		 let argNr = (offset / 4) + 1 in
		 if argNr <= numParams then
		   begin
		     src#set_function_argument callAddress argNr ;
		     argumentsFound := argNr :: !argumentsFound ;
		     if argNr > !maxIndex then maxIndex := argNr 
		   end
		 else
		   ()
	      | DirectCall _ | IndirectCall _ -> 
		 let argumentsNotFound = 
		   list_difference 
		     (List.init numParams (fun i->i)) !argumentsFound (fun x y -> x=y) in
		 begin
		   (match argumentsNotFound with
		    | [] -> ()
		    | _ ->
		       ch_error_log#add
                         "function arguments"
		         (LBLOCK [ STR "Unable to collect all arguments for " ; 
				   STR callAddress ; 
				   STR ". Arguments " ;
				   pretty_print_list argumentsNotFound 
				                     (fun n -> INT n) "[" ";" "]" ;
				   STR " are missing" ]));
		   active := false
		 end
	      | _ -> ()) 
    end in

  let identify_arguments ~(callAddress:ctxt_iaddress_t) ~(block:assembly_block_int) =
    let active = ref true in
    let first = ref true in
    let argumentsFound = ref [] in
    let faddr = block#get_faddr in
    let callloc = ctxt_string_to_location faddr callAddress in
    begin
      block#itera ~high:callloc#i ~reverse:true
	(fun va instr ->
	  if !first then
            first := false          (* skip the call itself *)
	  else
	    if !active then
	      match instr#get_opcode with
	      | Mov (4, dst, src) when dst#is_esp_offset ->
		let offset = dst#get_esp_offset#toInt in
		let argNr = (offset/4) + 1 in
		begin
		  src#set_function_argument callAddress argNr ;
		  argumentsFound := src :: !argumentsFound
		end
	      | DirectCall _ | IndirectCall _ -> active := false
	      | _ -> ()) ;
      !argumentsFound
    end in

  let sanitize_arguments (arguments:operand_int list) =
    let arguments = List.sort
      (fun op1 op2 ->
	let (_,nr1) = op1#get_function_argument in
	let (_,nr2) = op2#get_function_argument in
	Stdlib.compare nr1 nr2) arguments in
    let (arguments, notArguments,_) =
      List.fold_left
	(fun (args,notArgs,seqNr) op ->
	  let (_,nr) = op#get_function_argument in
	  if nr = seqNr + 1 then 
	    (op::args, notArgs, nr) 
	  else 
	    (args, op::notArgs,nr)) ([],[],0) arguments in
    List.iter (fun op -> op#reset_function_argument) notArguments in

  assembly_functions#itera
    (fun faddr assemblyFunction ->
      try
	assemblyFunction#iter
	  (fun block ->
	    block#itera
	      (fun ctxtiaddr instr ->
                let loc = ctxt_string_to_location faddr ctxtiaddr in
		let floc = get_floc loc in
		match instr#get_opcode with
		| DirectCall op when 
		    op#is_absolute_address && has_callsemantics op#get_absolute_address ->
		  let semantics = get_callsemantics op#get_absolute_address in
		  let numParams = semantics#get_parametercount in
		  identify_known_arguments ~callAddress:ctxtiaddr ~numParams ~block
		| DirectCall _	| IndirectCall _ ->  
		   if floc#has_call_target
                      && floc#get_call_target#is_signature_valid then
		      let fintf = floc#get_call_target#get_function_interface in
		      let numParams = 
			List.length (get_stack_parameter_names fintf) in
		      identify_known_arguments
                        ~callAddress:ctxtiaddr ~numParams ~block
		    else
		      let functionArgs =
                        identify_arguments ~callAddress:ctxtiaddr ~block in
		      sanitize_arguments functionArgs
		| _ -> ())
	  )
      with
      | BCH_failure p ->
	 ch_error_log#add
           "associate function arguments (gcc)"
	   (LBLOCK [
                STR "Function ";
                assemblyFunction#get_address#toPretty;
                STR ": ";
                p])
    )


let associate_function_arguments () =
  let pushcount = ref 0 in
  let callcount = ref 0 in
  begin
    !assembly_instructions#iteri
     (fun _ instr ->
       match instr#get_opcode with
       | Push _ -> pushcount := !pushcount + 1
       | DirectCall _ | IndirectCall _ -> callcount := !callcount + 1
       | _ -> ()) ;
    if !pushcount > !callcount then
      associate_function_arguments_push ()
    else
      associate_function_arguments_mov ()
  end


let decorate_functions () =
  begin
    record_call_targets ();
    associate_condition_code_users ();
    associate_function_arguments ()
  end


let construct_functions_elf () =
  try
    begin
      construct_functions ();
      decorate_functions ();
      (true, LBLOCK [STR "Construct functions successful"; NL])
    end
  with
  | Invocation_error s
  | Invalid_argument s
  | Failure s ->
    (false, LBLOCK [STR "Failure in constructing functions: "; STR s; NL])
  | BCH_failure p ->
    (false, LBLOCK [STR "Failure in constructing functions: "; p; NL])

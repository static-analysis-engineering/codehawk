(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

(* xprlib *)
open Xprt
open XprToPretty
open XprTypes
open Xsimplify

(* bchlib *)
open BCHBasicTypes
open BCHDataBlock
open BCHDoubleword
open BCHFloc
open BCHFunctionApi
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummaryLibrary
open BCHJumpTable
open BCHLibTypes
open BCHLocation
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities

(* bchlibelf *)
open BCHELFHeader
open BCHELFTypes

(* bchlibmips32 *)
open BCHMIPSAssemblyBlock
open BCHMIPSAssemblyFunction
open BCHMIPSAssemblyFunctions
open BCHMIPSAssemblyInstruction
open BCHMIPSAssemblyInstructions

open BCHDisassembleMIPSInstruction
open BCHMIPSOperand
open BCHMIPSTypes
open BCHMIPSDisassemblyUtils

module P = Pervasives

(* ------------------------------------------------------------------------------
 * Constants used:
 * datablock_threshold: the minimum number of bad instructions to trigger creation 
 *                      of a data block (5)
 * ------------------------------------------------------------------------------ *)

let datablock_threshold = 5

module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)

let x2p = xpr_formatter#pr_expr

class opcode_monitor_t (base:doubleword_int) (size:int) =
object (self)

  val mutable datablocks = []
  val mutable statusvalid = true
  val mutable refaddress = wordzero

  method check_instruction (instr:mips_assembly_instruction_int) =
    match instr#get_opcode with
    | OpInvalid when statusvalid ->
       begin
         statusvalid <- false ;
         refaddress <- instr#get_address
       end
    | _ when (not statusvalid) ->
       let addr = instr#get_address in
       let badinstrcount = (addr#subtract refaddress)#to_int /  4  in
       let _ =
         if badinstrcount > datablock_threshold then self#add_data_block addr in
       statusvalid <- true
    | _ -> ()

  method private add_data_block addr =
    let db = make_data_block refaddress addr "" in
    begin
      chlog#add
        "datablock"
        (LBLOCK [ refaddress#toPretty ; STR " - " ; addr#toPretty ]) ; 
      system_info#add_data_block db ;
      datablocks <- db :: datablocks
    end
    
  method get_data_blocks =
    let _ =
      if not statusvalid then
        self#add_data_block (base#add_int size) in
    datablocks

end

let disassemble (base:doubleword_int) (displacement:int) (x:string) =
  let size = String.length x in  
  let opcode_monitor = new opcode_monitor_t base size in
  let add_instruction position opcode bytes =
    let index = (position + displacement) / 4 in  (* assume 4-byte aligned *)
    let addr = base#add_int position in
    let instr = make_mips_assembly_instruction addr opcode bytes in
    begin
      !mips_assembly_instructions#set index instr ;
      opcode_monitor#check_instruction instr
    end in
  let ch = system_info#get_string_stream x in
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [ STR "base: " ; base#toPretty ;
                STR "; displacement: " ; INT displacement ;
                STR "; size: " ; INT size  ]) in
  try
    begin
      while ch#pos < size do
        let prevPos = ch#pos in
        let instrbytes = ch#read_doubleword in
        let opcode = disassemble_mips_instruction ch base instrbytes in
        let currentPos = ch#pos in
        let instrLen = currentPos - prevPos in
        let instrBytes = Bytes.make instrLen ' ' in
        let _ = Bytes.blit (Bytes.of_string x) prevPos instrBytes 0  instrLen in
        let _ = add_instruction prevPos opcode (Bytes.to_string  instrBytes) in
      ()
      done ;
      !mips_assembly_instructions#set_not_code opcode_monitor#get_data_blocks
    end
  with
  | BCH_failure p ->
     begin
       pr_debug [ STR "Error in disassembly: " ; p ] ;
       raise (BCH_failure p)
     end
  

let disassemble_mips_sections () =
  let xSections = elf_header#get_executable_sections in
  let headers = List.sort (fun (h1,_) (h2,_) -> h1#get_addr#compare h2#get_addr) xSections in
  let (lowest,_) = List.hd headers in
  let (highest,_) = List.hd (List.rev headers) in
  let _ =
    chlog#add
      "disassembly"
      (LBLOCK [ pretty_print_list
                  headers
                  (fun (s,_) ->
                    LBLOCK [ STR s#get_section_name ; STR ":" ; s#get_addr#toPretty ;
                             STR " (" ; s#get_size#toPretty ; STR ")" ])
                  "[" " ; " "]" ]) in                                                     
  let startOfCode = lowest#get_addr in
  let endOfCode = highest#get_addr#add highest#get_size in
  let sizeOfCode = endOfCode#subtract startOfCode in
  let _ = initialize_mips_instructions (sizeOfCode#to_int / 4) in   (* only 4-byte aligned *)
  let _ = pverbose 
            [ STR "Create space for " ; sizeOfCode#toPretty ; STR " (" ;
	      INT sizeOfCode#to_int ; STR ")" ; STR "instructions" ] in
  let _ = initialize_mips_assembly_instructions sizeOfCode#to_int startOfCode in
  let _ = List.iter
            (fun (h,x) ->
              let displacement = (h#get_addr#subtract startOfCode)#to_int in
              disassemble h#get_addr displacement x) xSections in
  sizeOfCode

  (* returns the address of the location holding the relocation symbol
     if the instructions exhibit the following pattern:
     a   : lui    $t7,...
           lw     $t9,xxx($t7)
           jr     $t9
           addiu  $t8, $t7, xxx    (not included in the check)

     None otherwise
   *)
let extract_so_symbol (opcodes:mips_opcode_t list) =
  match opcodes with
  | [ LoadUpperImmediate (tmp,imm16) ;
      LoadWord (dst,src) ;
      JumpRegister tgt ] ->
     (match (tmp#get_kind, src#get_kind) with
      | (MIPSReg r1, MIPSIndReg (r2,offset)) when r1 = r2 ->
         (match dst#get_kind with
          | MIPSReg MRt9 ->            (* specified in the ABI *)
             let addr = (imm16#to_numerical#toInt lsl 16) + offset#toInt in
             Some (int_to_doubleword addr)
          | _ -> None)
      | _ -> None)
  | _ -> None

let get_so_target (instr:mips_assembly_instruction_int) =
  let check_so_target tgtaddr =
    let get_tgtopc a = (!mips_assembly_instructions#at_address a)#get_opcode in
    let tgtopc1 = get_tgtopc tgtaddr in
    let tgtopc2 = get_tgtopc (tgtaddr#add_int 4) in
    let tgtopc3 = get_tgtopc (tgtaddr#add_int 8) in
    extract_so_symbol [ tgtopc1; tgtopc2; tgtopc3 ] in
  match instr#get_opcode with
  | JumpLink op
  | BranchLink op when op#is_absolute_address ->
     let opaddr = op#get_absolute_address in
     (match check_so_target opaddr with
      | Some addr -> elf_header#get_relocation addr
      | _ -> None)
  | _ -> None

let is_nr_call_instruction (instr:mips_assembly_instruction_int) =
  match get_so_target instr with
  | Some sym ->
     (function_summary_library#has_so_function sym)
     && (function_summary_library#get_so_function sym)#is_nonreturning
  | _ ->
     match instr#get_opcode with
     | JumpLink tgt
       | BranchLTZeroLink (_,tgt)
       | BranchGEZeroLink (_,tgt)
       | BranchLink tgt when tgt#is_absolute_address ->
        let tgtaddr = tgt#get_absolute_address in
        ((functions_data#is_function_entry_point tgtaddr)
         && (functions_data#get_function tgtaddr)#is_non_returning)
     | _ -> false

let collect_function_entry_points () =
  let addresses = new DoublewordCollections.set_t in
  begin
    !mips_assembly_instructions#itera
     (fun va instr ->
       match instr#get_opcode with
       | BranchLTZeroLink (_,tgt)
         | BranchGEZeroLink (_,tgt)
         | BranchLink tgt
         | JumpLink tgt when tgt#is_absolute_address ->
          (match get_so_target instr with
           | Some sym ->
              (functions_data#add_function tgt#get_absolute_address)#add_name sym
           | _ ->
              addresses#add tgt#get_absolute_address)
       | _ -> ()) ;
    addresses#toList
  end

let set_block_boundaries () =
  let set_block_entry a =
    (!mips_assembly_instructions#at_address a)#set_block_entry in
  let set_delay_slot a =
    (!mips_assembly_instructions#at_address a)#set_delay_slot in
  let feps = functions_data#get_function_entry_points in
  begin
    (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ record function entry points *)
    List.iter
      (fun fe ->
        try
          set_block_entry fe
        with
	| BCH_failure _ ->
	  chlog#add "disassembly" 
	    (LBLOCK [ STR "function entry point incorrect: " ; fe#toPretty ])
	| Invalid_argument s ->
	  ch_error_log#add "disassembly"
	    (LBLOCK [ STR "function entry point problem: " ; fe#toPretty ; 
		      STR ": " ; STR s ])
      ) feps ;
    (* ~~~~~~~~~~~~~~~~~~~~ record targets of unconditional and conditional jumps *)
    !mips_assembly_instructions#itera
     (fun _ instr ->
       try
         let opcode = instr#get_opcode in
         if is_direct_jump_instruction opcode then
           let tgtaddr = get_direct_jump_target_address opcode in
           set_block_entry tgtaddr
         else
           ()
       with
       | BCH_failure p ->
          ch_error_log#add
            "disassembly"
            (LBLOCK [ STR "assembly instruction creates incorrect block entry: (" ;
                      instr#get_address#toPretty ; STR "): " ;
                      instr#toPretty ; STR ": " ; p ])) ;
    (* ~~~~~~~~~~~~~~~~~~ add block entries due to previous block-ending instruction *)
    !mips_assembly_instructions#itera
     (fun va instr ->
       let opcode = instr#get_opcode in
       if is_jump_instruction opcode || is_halt_instruction opcode then
         begin
           set_delay_slot (va#add_int 4) ;
           set_block_entry (va#add_int 8)
         end
       else if is_nr_call_instruction instr then
         begin
           set_delay_slot (va#add_int 4) ;
           set_block_entry (va#add_int 8)
         end
       else
         ())
  end

let is_so_jump_target (target_address:doubleword_int) =
  match elf_header#get_relocation target_address with
  | Some _ -> true
  | _ -> false

let get_successors (faddr:doubleword_int) (iaddr:doubleword_int)  =
  if system_info#is_nonreturning_call faddr iaddr then
    []
  else
    let instr = !mips_assembly_instructions#at_address iaddr in
    let opcode = instr#get_opcode in
    let next () = [ iaddr#add_int 4 ] in
    let delaynext () = [ iaddr#add_int 8 ] in
    let successors =
      if is_conditional_jump_instruction opcode then
        (delaynext ()) @ [ get_direct_jump_target_address opcode ]
      else if is_direct_jump_instruction opcode then
        [ get_direct_jump_target_address opcode ]
      else
        next () in
    List.map
      (fun va -> (make_location { loc_faddr = faddr ; loc_iaddr = va })#ci)
      successors
    

let trace_block (faddr:doubleword_int) (baddr:doubleword_int) =
  let set_block_entry a = (!mips_assembly_instructions#at_address a)#set_block_entry in    
  let get_instr iaddr =
    try
      !mips_assembly_instructions#at_address iaddr
    with
    | BCH_failure p ->
       begin
         pr_debug [ STR "  Error: trace block: get_instr: " ; iaddr#toPretty ; NL ] ;
         raise (BCH_failure p)
       end in
  let get_next_instr_addr a = a#add_int 4 in
  let mk_ci_succ l =
    List.map
      (fun va -> (make_location { loc_faddr = faddr ; loc_iaddr = va })#ci) l in
  let rec find_last_instr (va:doubleword_int) (prev:doubleword_int) =
    let instr = get_instr va in
    if va#equal wordzero then
      (Some [],prev,[])
    else if is_return_instruction instr#get_opcode then
      (Some [],va#add_int 4,[])
    else if instr#is_block_entry then
      (None,prev,[])
    else if is_nr_call_instruction instr then
      (Some [],va#add_int 4,[])
    else if is_conditional_jump_instruction instr#get_opcode
            || is_fp_conditional_jump_instruction instr#get_opcode then
      let nextblock = va#add_int 8 in
      let tgtblock = get_direct_jump_target_address instr#get_opcode in
      (Some (mk_ci_succ [ nextblock ; tgtblock ]),va#add_int 4,[])
    else if is_direct_jump_instruction instr#get_opcode then
      let tgtblock = get_direct_jump_target_address instr#get_opcode in
      (Some (mk_ci_succ [ tgtblock ]),va#add_int 4,[])
    else if is_indirect_jump_instruction instr#get_opcode then
      if system_info#has_jump_table_target faddr va then
        let loc = make_location { loc_faddr = faddr ; loc_iaddr = va } in
        let ctxtiaddr = loc#ci in
        let finfo = get_function_info faddr in
        let (jt,_,lb,ub) = system_info#get_jump_table_target faddr va in
        let targets = jt#get_targets jt#get_start_address lb ub in
        let reg = MIPSRegister (get_indirect_jump_instruction_register instr#get_opcode) in
        let _ = finfo#set_jumptable_target ctxtiaddr jt#get_start_address jt reg in
        (Some (mk_ci_succ targets),va#add_int 4,[])
      else
        (Some [],va#add_int  4,[])
    else if instr#is_delay_slot then
      (None,va,[])
    else if is_halt_instruction instr#get_opcode then
      (Some [],va,[])
    else if instr#is_inlined_call then
      let a = match instr#get_opcode with
        | BranchLTZeroLink (_,tgt)
          | BranchGEZeroLink (_,tgt)
          | BranchLink tgt
          | JumpLink tgt when tgt#is_absolute_address ->
           tgt#get_absolute_address
        | _ ->
           raise (BCH_failure (LBLOCK [ STR "Internal error in trace block" ])) in
      let fn = mips_assembly_functions#get_function_by_address a in
      let returnsite = get_next_instr_addr va in
      let _ = set_block_entry returnsite in
      let ctxt =
        FunctionContext
          { ctxt_faddr = faddr ;
            ctxt_callsite = a ;
            ctxt_returnsite = returnsite } in
      let callloc = make_location { loc_faddr = a ; loc_iaddr = a } in
      let ctxtcallloc = make_c_location callloc ctxt in
      let callsucc = ctxtcallloc#ci in 
      let inlinedblocks =
        List.map
          (fun b ->
            let succ =
              match b#get_successors with
              | [] -> [ (make_location { loc_faddr = faddr ; loc_iaddr = returnsite })#ci  ]
              | l -> List.map (fun s -> add_ctxt_to_ctxt_string faddr s ctxt) l in
            make_ctxt_mips_assembly_block ctxt b succ) fn#get_blocks in
      (Some [ callsucc ],va,inlinedblocks)
    else find_last_instr (get_next_instr_addr va) va in
  let (succ,lastaddr,inlinedblocks) =
    let opcode = (get_instr baddr)#get_opcode in
    if is_return_instruction opcode then
      (Some [],baddr#add_int 4,[])
    else if is_indirect_jump_instruction opcode then
      if system_info#has_jump_table_target faddr baddr then
        let (jt,_,lb,ub) = system_info#get_jump_table_target faddr baddr in
        let targets = jt#get_targets jt#get_start_address lb ub in
        (Some (mk_ci_succ targets),baddr#add_int 4,[])
      else
        (Some [],baddr#add_int 4,[])
    else if is_conditional_jump_instruction opcode then
      let nextblock = baddr#add_int 8 in
      let tgtblock = get_direct_jump_target_address opcode in
      (Some (mk_ci_succ [ nextblock ; tgtblock ]),baddr#add_int 4,[])
    else if is_direct_jump_instruction opcode then
      let tgtblock = get_direct_jump_target_address opcode in
      (Some (mk_ci_succ [ tgtblock ]),baddr#add_int 4,[])
    else
      find_last_instr (get_next_instr_addr baddr) baddr in
  let successors =
    match succ with Some s ->  s | _ -> get_successors faddr lastaddr in
  (inlinedblocks,make_mips_assembly_block faddr baddr lastaddr successors)

let trace_function (faddr:doubleword_int) =
  let workSet = new DoublewordCollections.set_t in
  let doneSet = new DoublewordCollections.set_t in
  let set_block_entry a = (!mips_assembly_instructions#at_address a)#set_block_entry in
  let get_iaddr s = (ctxt_string_to_location faddr s)#i in  
  let add_to_workset l =
    List.iter (fun a -> if doneSet#has a then () else workSet#add a) l in
  let blocks = ref [] in
  let rec add_block (entry:doubleword_int) =
    let (inlinedblocks,block) = trace_block faddr entry in
    let blocksuccessors = block#get_successors in
    begin
      set_block_entry entry ;
      workSet#remove entry ;
      doneSet#add entry ;
      blocks := (block :: inlinedblocks) @ !blocks ;
      add_to_workset (List.map get_iaddr blocksuccessors) ;
      match workSet#choose with Some a -> add_block a | _ -> ()
    end in
  let _ = add_block faddr in
  let blocklist =
    List.sort (fun b1 b2 ->
        P.compare b1#get_context_string b2#get_context_string) !blocks in
  let successors =
    List.fold_left (fun acc b ->
        let src = b#get_context_string in
        (List.map (fun tgt -> (src,tgt)) b#get_successors) @ acc) []  blocklist in
  make_mips_assembly_function faddr blocklist successors

let construct_mips_assembly_function (count:int) (faddr:doubleword_int) =
  try
    let _ = pverbose [ STR "  trace function " ; faddr#toPretty ; NL ] in
    let fn = trace_function faddr in
    let _ = pverbose [ STR "  add function " ; faddr#toPretty ; NL ;
                       fn#toPretty ; NL ] in
    mips_assembly_functions#add_function fn
  with
  | BCH_failure p ->
     raise (BCH_failure (LBLOCK [ STR "Error in constructing function " ;
                                  faddr#toPretty ; STR ": " ;  p ]))
                                                                   
let construct_functions f =
  let _ = system_info#initialize_function_entry_points f in
  let _ = set_block_boundaries () in
  let functionentrypoints = functions_data#get_function_entry_points in
  let count = ref 0 in
  List.iter (fun faddr ->
      let fndata = functions_data#get_function faddr in
      if fndata#is_library_stub then
        ()
      else
        try
          begin
            count := !count + 1;
            pverbose [ STR "Construct function " ; faddr#toPretty ; NL ] ;
            construct_mips_assembly_function !count faddr
          end
        with
        | BCH_failure p ->
           ch_error_log#add
             "construct functions"
             (LBLOCK [ STR "function " ; faddr#toPretty ; STR ": " ; p ])
    ) functionentrypoints


let record_call_targets () =
  mips_assembly_functions#itera
    (fun faddr f ->
      try
        let finfo = get_function_info faddr in
        begin
          f#iteri
            (fun _ ctxtiaddr instr ->
              match instr#get_opcode with
              | BranchLink op
              | JumpLink op ->
                 if finfo#has_call_target ctxtiaddr then
                   ()
                 else
                   begin
                     match get_so_target instr with
                     | Some tgt -> finfo#set_so_target ctxtiaddr tgt
                     | _ ->
                        if op#is_absolute_address then
                          finfo#set_app_target ctxtiaddr op#get_absolute_address
                   end
              | JumpLinkRegister (ra,op) ->
                 if finfo#has_call_target ctxtiaddr then
                   ()
                 else
                   finfo#set_unknown_target ctxtiaddr
              | _ -> ())
        end
      with
      | BCH_failure p ->
         ch_error_log#add
           "record call targets"
           (LBLOCK [ STR "function " ; faddr#toPretty ; STR ": " ; p ]))



let decorate_functions () =
  begin
    record_call_targets ()
  end

let construct_functions_mips () =
  begin
    construct_functions collect_function_entry_points ;
    decorate_functions ()
  end

let set_call_address (floc:floc_int) (op:mips_operand_int) =
  let env = floc#f#env in
  let opExpr = op#to_expr floc in
  let opExpr = floc#inv#rewrite_expr opExpr env#get_variable_comparator in
  let logerror msg = ch_error_log#add "set call address" msg in
  match opExpr with
  | XConst (IntConst c) ->
     let dw = numerical_to_doubleword c in
     if mips_assembly_functions#has_function_by_address dw then
       floc#set_application_target dw
     else
       ()
  | XVar v when env#is_global_variable v ->
     let gaddr =  env#get_global_variable_address v in
     if elf_header#is_program_address gaddr then
       let dw = elf_header#get_program_value gaddr in
       if functions_data#has_function_name dw then
         let name = (functions_data#get_function dw)#get_function_name in
         if function_summary_library#has_so_function name then
             floc#set_so_target name
         else
           if mips_assembly_functions#has_function_by_address dw then
             floc#set_application_target dw
           else
             logerror
               (LBLOCK [ STR "Function name not associated with address: "  ;
                         STR name ])
       else
         if mips_assembly_functions#has_function_by_address dw then
           floc#set_application_target dw
         else
           logerror
             (LBLOCK [ STR "reference does not resolve to function address: " ;
                       dw#toPretty ])
     else
       logerror
         (LBLOCK [ STR "reference is not in program space: " ; gaddr#toPretty ])
  | _ ->
     ()

let resolve_indirect_mips_calls (f:mips_assembly_function_int) =
  let _ =
    f#iteri
      (fun faddr ctxtiaddr instr ->
        let loc = ctxt_string_to_location faddr ctxtiaddr in
        match instr#get_opcode with
        | JumpLinkRegister (ra,tgt) ->
           let floc = get_floc loc in
           if floc#has_unknown_target then
             set_call_address floc tgt
        | JumpRegister tgt ->
           let floc = get_floc loc in
           let env = floc#f#env in
           let ra_op = mips_register_op MRra RD in
           let ra = floc#inv#rewrite_expr (ra_op#to_expr floc) floc#env#get_variable_comparator in
           begin
             match ra with
             | XVar ra_var ->
                if env#is_initial_register_value ra_var then
                  if floc#has_unknown_target || floc#has_no_call_target then
                    set_call_address floc tgt
             | _ ->
                pr_debug [ floc#l#toPretty ; STR ": ra = " ; x2p ra ; NL ]
           end
        | _ ->
           ()) in
  ()


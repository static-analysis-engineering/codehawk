(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2021      Aarno Labs LLC

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
open CHNumerical
open CHBounds
open CHLanguage

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHUtil

(* xprlib *)
open Xprt
open XprToPretty

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHCallTarget
open BCHCppClass
open BCHCPURegisters
open BCHDataBlock
open BCHDoubleword
open BCHFloc
open BCHFunctionInterface
open BCHFunctionData
open BCHFunctionInfo
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHGlobalState
open BCHJni
open BCHJumpTable
open BCHLibTypes
open BCHLocation
open BCHLocationInvariant
open BCHMakeCallTargetInfo
open BCHPreFileIO
open BCHStreamWrapper
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities
open BCHVariable
open BCHVariableNames

(* bchlibpe *)
open BCHLibPETypes
open BCHPEHeader
open BCHPESectionHeader
open BCHPESections

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
open BCHPullData
open BCHX86OpcodeRecords
open BCHX86Opcodes


let pr_expr = xpr_formatter#pr_expr

module DoublewordCollections = CHCollections.Make (
  struct
    type t = doubleword_int
    let compare d1 d2 = d1#compare d2
    let toPretty d = d#toPretty
  end)

let byte_to_string (b:int) =
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l
    
let hex_string s =
  let ch = IO.input_string s in
  let h = ref "" in
  let len = String.length s in
  begin
    for i = 0 to len-1 do h := !h ^ (byte_to_string (IO.read_byte ch)) done ;
    !h
  end
    
let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c -> if (Char.code c) < 33 then found  := true) s in
  !found

let disassemble (displacement:int) (header:pe_section_header_int) =
  let sname = 
    let name = header#get_name in
    if has_control_characters name then 
      ("hex_encoded_" ^ (hex_string name)) 
    else name in
  let _ = chlog#add "initialization"
    (LBLOCK [ STR "Disassemble section " ; STR sname ; STR " with displacement " ; 
	      INT displacement ]) in
  let section = pe_sections#get_section header#index in
  let sectionVA = section#get_section_VA in
  let codeString = section#get_exe_string in
  let codeString = system_info#decode_string codeString sectionVA in
  let add_instruction position opcode bytes =
    let index = position + displacement in
    let va = sectionVA#add_int position in
    let instruction = make_assembly_instruction va opcode bytes in
    !assembly_instructions#set index instruction in
  let ch = system_info#get_string_stream codeString in
  let size = String.length codeString in
  let is_data_block (pos:int) = 
    (!assembly_instructions#at_index (pos+displacement))#is_non_code_block in
  let is_not_code (pos:int) = 
    let instr = !assembly_instructions#at_index (pos+displacement) in
    match instr#get_opcode with | NotCode None -> true | _ -> false in
  let skip_data_block (pos:int) ch =
    let nonCodeBlock = 
      (!assembly_instructions#at_index (pos+displacement))#get_non_code_block in
    let len = not_code_length nonCodeBlock in
    let dataString = Bytes.make len ' ' in
    let _ = Bytes.blit (Bytes.of_string codeString) pos dataString 0 len in
    begin
      chlog#add "skip data block" (LBLOCK [ STR "pos: " ; INT pos ;
                                            STR "; length: " ; INT len ]) ;
      ch#skip_bytes len  ;
      not_code_set_string nonCodeBlock (Bytes.to_string dataString)
    end in
  try
    while ch#pos < size do
      let prevPos = ch#pos in
      try
	if is_data_block prevPos  then
	  skip_data_block prevPos ch
	else if is_not_code prevPos then
	  begin
	    ch_error_log#add "disassembly" 
	      (LBLOCK [ STR "Unexpected not-code at " ; 
			(sectionVA#add_int prevPos)#toPretty ]) ;
	    while is_not_code ch#pos do ignore ch#read_byte done
	  end
	else
	  (* let index = prevPos + displacement in *)
	  let va = sectionVA#add_int (* index *) prevPos in
	  if system_info#is_cfnop va then
	    let (len,desc) = system_info#get_cfnop va in
	    let opcode = CfNop(len,desc) in
	    let dataString = Bytes.make len ' ' in
	    let _ = Bytes.blit (Bytes.of_string codeString) prevPos dataString 0 len in
	    let _ = add_instruction prevPos opcode (Bytes.to_string dataString) in
	    ch#skip_bytes len
	  else if system_info#is_cfjmp va then
	    let (tgt,len,desc) = system_info#get_cfjmp va in
	    let tgt = absolute_op tgt 4 RD in
	    let opcode = CfJmp(tgt,len,desc) in
	    let dataString = Bytes.make len ' ' in
	    let _ = Bytes.blit (Bytes.of_string codeString) prevPos dataString 0 len in
	    let _ = add_instruction prevPos opcode (Bytes.to_string dataString) in
	    ch#skip_bytes len
	  else
	    let firstByte = ch#read_byte in
	    let opcode = disassemble_instruction ch sectionVA firstByte in
	    let curPos = ch#pos in
	    let instrLen = curPos - prevPos  in
	    let instrBytes = String.sub codeString prevPos instrLen in
	    let _ = add_instruction prevPos opcode instrBytes in
	    ()
      with
	Invalid_argument s ->
	  begin
	    ch_error_log#add "disassembly"
	      (LBLOCK [ STR "failure in disassembling instruction at " ; 
			(sectionVA#add_int prevPos)#toPretty ]) ;
	    raise (Invalid_argument s)
	  end
    done
  with
  | BCH_failure p ->
    ch_error_log#add "disassembly"
      (LBLOCK [ STR "failure in disassembling section " ; 
		STR header#get_name ; STR ": " ; p ])
  | Invalid_argument s ->
    ch_error_log#add "disassembly"
      (LBLOCK [ STR "failure in disassembling section " ; 
		STR header#get_name ; STR ": " ; STR s ])
  | IO.No_more_input ->
     begin
       ch_error_log#add "disassembly"
                        (LBLOCK [ STR "No more input when reading section at " ;
                                  sectionVA#toPretty ]) ;
       ()
     end

let disassemble_string (displacement:int) (vastart:doubleword_int) (codestring:string) =
  let size = String.length codestring in
  let imageBase = system_info#get_image_base in
  let baseOfCodeRVA = system_info#get_base_of_code_rva in
  let baseOfCode = imageBase#add baseOfCodeRVA in
  let ch = make_pushback_stream ~little_endian:true codestring in
  let _ = initialize_assembly_instructions
            displacement size system_info#get_code_size#to_int baseOfCode [] [] in
  let add_instruction position opcode bytes =
    let index = position + displacement in
    let va = vastart#add_int position in
    let instr =  make_assembly_instruction va opcode bytes in
    !assembly_instructions#set index instr in
  try
    while ch#pos < size do
      let prevpos =  ch#pos in
      try
        let firstbyte = ch#read_byte in
        let opcode = disassemble_instruction ch vastart firstbyte in
        let curpos = ch#pos  in
        let instrlen = curpos - prevpos in
        let instrbytes = String.sub codestring prevpos instrlen in
        add_instruction prevpos  opcode instrbytes
      with
      | Invalid_argument s ->
         begin
           ch_error_log#add "string disassembly"
                            (LBLOCK [ STR "failure disassembling instruction at " ;
                                      (vastart#add_int prevpos)#toPretty ]) ;
           raise (Invalid_argument s)
         end
    done
  with
  | BCH_failure p ->
     ch_error_log#add "stream disassembly"
                      (LBLOCK [ STR "failure in disassembling codestring: " ;  p ])
  |  IO.No_more_input -> ()
  

let add_class_functions classes isCodeAddress =
  List.iter (fun c ->
      let _ =
        c#initialize_function_interfaces pe_sections#get_virtual_function_address in
      let add l isstatic =
        let classname = c#get_name in
        List.iter (fun (fa,functionname)  -> 
            if isCodeAddress fa then 
              let fd = functions_data#add_function fa in
              begin
                fd#set_class_info ~classname ~isstatic ;
                fd#add_name functionname ;
	        chlog#add "add class method"
	                  (LBLOCK [ fa#toPretty ; STR "  " ;
		                    STR classname ; STR "::" ;
                                    STR functionname ])
	end) l in
      begin
        add c#get_instance_functions false ;
        add c#get_class_functions true
      end) classes

(* Look for code patterns of the form:
      movzx dreg, ooffset(_,ireg,_)
      jmp* joffset(_,dreg,4) 
*)
let identify_data_blocks is_code_address header =
  let section = pe_sections#get_section header#index in
  let sectionVA = section#get_section_VA in
  let codestring = section#get_exe_string in
  let newDataBlocks = ref 0 in
  let is_code n =
    try
      is_code_address (numerical_to_doubleword n)
    with
    | BCH_failure p ->
       let msg = LBLOCK [ STR "identify_data_blocks.is_code: " ; n#toPretty ;
                          STR " (" ; p ; STR ")" ] in
       begin
         chlog#add "doubleword conversion" msg;
         false
       end in
  let get_instr = !assembly_instructions#at_address in
  let has_next_instr = !assembly_instructions#has_next_valid_instruction in
  let get_next_instr iaddr = 
    get_instr (!assembly_instructions#get_next_valid_instruction_address iaddr) in
  let get_jumptable = !assembly_instructions#get_jumptable in
  let add_data_block instr nextInstr offset jtoffset jt =
    let jtlength = jt#get_length - (jtoffset#subtract jt#get_start_address)#to_int in
    let jtlength = jtlength / 4 in
    let db =
      try
        create_jumptable_offset_block
          (numerical_to_doubleword offset) sectionVA codestring jtlength
      with
      | BCH_failure p ->
         raise (BCH_failure
                  (LBLOCK [ STR "identify_data_blocks.db: " ; p ])) in
    begin
      system_info#set_jump_target nextInstr#get_address jtoffset jt db ;
      system_info#add_data_block db ;
      newDataBlocks := !newDataBlocks + 1 ;
      chlog#add "jumptable offset block"
	(LBLOCK [ db#get_start_address#toPretty ; STR " - " ; 
		  db#get_end_address#toPretty ; STR " (" ;
		  instr#toPretty ; STR ", " ; nextInstr#toPretty ; STR ")" ;
		  STR " jtlength = " ; INT jtlength ])
    end in    
  !assembly_instructions#itera (fun iaddr instr ->
    match instr#get_opcode with
    | Movzx (_,dst,src) ->
      begin
	match (dst#get_kind,src#get_kind) with
	| (Reg dreg, IndReg (_,offset))
	| (Reg dreg, ScaledIndReg (_,_,_,offset)) when is_code offset ->
	   if system_info#has_data_block (numerical_to_doubleword offset) then
             ()
           else
	     if has_next_instr iaddr then
	       begin
		 let nextInstr = get_next_instr iaddr in
		 match nextInstr#get_opcode with
		 | IndirectJmp op ->
		    begin
		      match op#get_kind with
		      | ScaledIndReg (_,Some ireg,_,jtoffset)
                           when is_code jtoffset && ireg = dreg ->
		         let jtoffset = numerical_to_doubleword jtoffset in
		         (try
			    begin
			      match get_jumptable jtoffset with
			      | Some jt -> add_data_block instr nextInstr offset jtoffset jt
			      | _ ->
			         match create_jumptable jtoffset sectionVA is_code_address codestring with
			         | Some jt ->
			            begin
				      system_info#add_jumptable jt ;
				      add_data_block instr nextInstr offset jtoffset jt ;
				      chlog#add "add 2-jump table"
				                (LBLOCK [ jtoffset#toPretty ; STR ": " ;
					                  nextInstr#toPretty ])
			            end
			         | _ -> ()
			    end
		          with
			    BCH_failure p ->
			    ch_error_log#add
                              "incorrect data block"
			      (LBLOCK [ iaddr#toPretty ;
				        STR "; jtoffset: " ; jtoffset#toPretty ;
				        STR "; offset: " ; offset#toPretty]))
		      | _ -> ()
		    end
	         | _ -> ()
	       end
	| _ -> ()
      end
    | _ -> ())

let identify_misaligned_functions header =
  let section = pe_sections#get_section header#index in
  let sectionVA = section#get_section_VA in
  let codestring = section#get_exe_string in
  let codelen = String.length codestring in
  let newDataBlocks = ref 0 in
  let is_code = system_info#is_code_address in
  let is_valid_instr a = 
    is_code a && (!assembly_instructions#at_address a)#is_valid_instruction in
  let add_datablock start endaddr =
    let db = make_data_block start endaddr "zeroes" in
    begin
      newDataBlocks := !newDataBlocks + 1 ;
      chlog#add "align function entry point" 
	(LBLOCK [ endaddr#toPretty ; STR ": " ; 
		  INT (endaddr#subtract start)#to_int ; STR " bytes" ]) ;
      system_info#add_data_block db
    end in
  let feps = functions_data#get_function_entry_points in
  List.iter (fun fe ->
    if is_valid_instr fe then () else
      try
	if sectionVA#le fe then
	  let feindex = (fe#subtract sectionVA)#to_int in
	  if feindex < codelen then
	    let index = ref (feindex - 1) in
	    begin
	      while !index > 0 && Char.code (Bytes.get (Bytes.of_string codestring) !index) = 0 do 
		index := !index - 1
	      done ;
	      index := !index + 1 ;
	      let dblen = feindex - !index in
	      if dblen > 0 then
		add_datablock (fe#subtract_int dblen) fe
	    end
      with
	Invalid_argument s ->
	  pr_debug [ STR s ; STR ": " ; fe#toPretty ; NL ]) feps

let disassemble_sections (headers:pe_section_header_int list) =
  let imageBase = system_info#get_image_base in
  let baseOfCodeRVA = system_info#get_base_of_code_rva in
  let baseOfCode = imageBase#add baseOfCodeRVA in
  let codeSize = system_info#get_code_size in
  let isCodeAddress = system_info#is_code_address in
  let readOnlySections = List.filter 
    (fun s -> s#is_read_only || s#is_executable) pe_sections#get_sections in
  let  _ = pverbose [ STR "filter readonly section strings ... " ; NL ] in
  let readOnlySectionStrings = List.map (fun s -> 
    (s#get_section_VA, s#get_exe_string)) readOnlySections in
  let _ = system_info#initialize_jumptables isCodeAddress readOnlySectionStrings in
  let _ = pverbose [ STR "initialized jump tables" ; NL ] in
  let classes = get_cpp_classes () in
  let _ = add_class_functions classes isCodeAddress in
  let _ = initialize_instructions codeSize#to_int in
  let _ = chlog#add "initialization" 
    (LBLOCK [ STR "Create space for " ; codeSize#toPretty ; STR " (" ;
	      INT codeSize#to_int ; STR ")" ; STR "instructions" ]) in
  let _ = List.iter 
    (fun header ->
      let section = pe_sections#get_section header#index in
      let displacement = ((section#get_section_VA)#subtract baseOfCode)#to_int in
      let endSection = displacement + header#get_size#to_int in
      let newDataBlocks = ref true in
      let datablockCount = ref (List.length system_info#get_data_blocks) in
      let itcount = ref 0 in
      while !newDataBlocks && !itcount < 5 do
	let jumpTables = system_info#get_jumptables in
	let dataBlocks = system_info#get_data_blocks in
	begin
	  itcount := !itcount + 1 ;
	  initialize_assembly_instructions 
	    displacement endSection codeSize#to_int baseOfCode jumpTables dataBlocks ;
	  disassemble displacement header ;
	  identify_data_blocks isCodeAddress header ;
	  (* identify_misaligned_functions header ; *)
	  (let dbCount = List.length system_info#get_data_blocks in
	  if dbCount > !datablockCount then
	    datablockCount := dbCount
	  else
	    newDataBlocks := false)
	end
      done) headers in
  let _ = List.iter
            (fun (vastart,s) ->
              let displacement = (vastart#subtract baseOfCode)#to_int in
              disassemble_string displacement vastart s)
            system_info#get_initialized_memory_strings in
              
  codeSize#to_int

let get_dll_target (instr:assembly_instruction_int) =
(*
      I: ..: call a           text section
         ..: ....
         a : jump *b
         -----------------
         b : c                data section  
*)
  let check_case_I target_address =
    if !assembly_instructions#is_code_address target_address then
      let targetOpcode = (!assembly_instructions#at_address target_address)#get_opcode in
      match targetOpcode with
      | IndirectJmp jumpTarget ->
	  if jumpTarget#is_absolute_address then
	    pe_sections#get_imported_function jumpTarget#get_absolute_address
	  else
	    None
      | _ -> None
    else
      None in
  (*
     II: ..: call *a          text section
         ------------------
         a : c                data section
         where c is the index into an import lookup table

          ..: call *a
          -----------------
          a : c               data section
         where c is a code address
  *)
  let check_case_II target_address = pe_sections#get_imported_function target_address in
  match instr#get_opcode with
  | DirectCall op when op#is_absolute_address -> check_case_I op#get_absolute_address
  | IndirectCall op when op#is_absolute_address -> check_case_II op#get_absolute_address
  | _ -> None
    
let is_dll_target (instr:assembly_instruction_int) = 
  match get_dll_target instr with Some _ -> true | _ -> false
		
let is_dll_jump_target (target_address:doubleword_int) =
  match pe_sections#get_imported_function target_address with 
  | Some _ -> true 
  | _ -> match pe_sections#get_imported_function_by_index target_address with
    | Some _ -> true
    | _ -> false


let get_indirect_jump_targets (op:operand_int) =
  if op#is_jump_table_target then
    let (jumpBase,reg) = op#get_jump_table_target in
    try
      let jumpBase = numerical_to_doubleword jumpBase in
      match system_info#is_in_jumptable jumpBase with
      | Some jt -> Some (jumpBase,jt,reg)
      | _ ->
	chlog#add "jump table" 
	  (LBLOCK [ STR "not found for offset " ; jumpBase#toPretty ]) ;
	None
    with
    | BCH_failure p ->
       raise (BCH_failure
                (LBLOCK [ STR "get_indirect_jump_targets: " ; op#toPretty ;
                          STR " (" ; p ; STR ")" ]))
    | Invalid_argument s ->
      begin
	ch_error_log#add "invalid argument"
	  (LBLOCK [ STR "get_indirect_jump_targets: " ; STR s ; STR ": " ; 
		    op#toPretty ]) ;
	None
      end
  else
    None

(* Checks for non-returning functions *)

let is_nr_dllfname (dll:string) (name:string) =
  function_summary_library#has_dll_function dll name &&
    (function_summary_library#get_dll_function dll name)#is_nonreturning

let is_nr_declared (faddr:doubleword_int) =
  ((functions_data#is_function_entry_point faddr)
  && (functions_data#get_function faddr)#is_non_returning)
  || (functions_data#has_function_name faddr &&
	(let fname = (functions_data#get_function faddr)#get_function_name in
	  match function_summary_library#search_for_library_function fname with
	  | Some dll ->	is_nr_dllfname dll fname
	  | _ -> false))

(* Check for non-returning function before functions are created *)
let is_nr_call_instruction (instr:assembly_instruction_int) =
  match get_dll_target instr with
  | Some (dll,name) -> is_nr_dllfname dll name
  | _ -> 
    match instr#get_opcode with
    | DirectCall op when op#is_absolute_address ->
      is_nr_declared op#get_absolute_address
    | _ -> false

(* Check for non-returning function when containing function is known *)
let is_nr_call (floc:floc_int) (instr:assembly_instruction_int) =
  floc#has_call_target && floc#get_call_target#is_nonreturning
  || (is_nr_call_instruction instr)
  || (match instr#get_opcode with
      | DirectCall op when op#is_absolute_address ->
         is_nr_declared op#get_absolute_address
      | _ -> false)
      
let set_block_boundaries () =
  try
    let jumpTables = system_info#get_jumptables in
    let set_block_entry a = (!assembly_instructions#at_address a)#set_block_entry in
    let set_inlined_call a = (!assembly_instructions#at_address a)#set_inlined_call in
    let is_in_range = !assembly_instructions#is_in_code_range in
    let feps = functions_data#get_function_entry_points in
    begin
      (* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ record targets of jump tables *)
      List.iter (fun jt -> 
          try
	    List.iter set_block_entry jt#get_all_targets
          with
          | BCH_failure p ->
	     chlog#add "disassembly" 
	               (LBLOCK [ STR "jump table targetb incorrect: " ; p ;
		                 STR " (start: " ; jt#get_start_address#toPretty ; STR ")" ])
          | Invalid_argument s ->
             raise (BCH_failure (LBLOCK [ STR "record jump-table targets: " ;
                                          jt#get_start_address#toPretty ; STR ": " ; STR  s ]))
        ) jumpTables ; 
      
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
      !assembly_instructions#itera
       (fun va instr ->
	 try
	   let opcode = instr#get_opcode in
	   match opcode with
	   | IndirectJmp op when op#is_absolute_address && 
		                   is_dll_jump_target op#get_absolute_address -> ()
	   | _ ->
	      if is_direct_jump_instruction instr#get_opcode then
	        let targetOp =
		  match get_operands opcode with
                  | [ op ] | [ op ; _ ] -> op
                  | _ ->
		     raise (BCH_failure 
			      (LBLOCK [ STR "Internal error in set_block_boundaries "])) in
	        if targetOp#is_absolute_address then
		  let targetAddress = targetOp#get_absolute_address in
		  if is_in_range targetAddress then
		    set_block_entry targetAddress
		  else
		    disassembly_log#add "disassembly"
		                        (LBLOCK [ STR "Jump target address is outside code range: " ; 
			                          targetAddress#toPretty ])
	        else
		  ()
	      else
	        ()
	 with
	 | BCH_failure p ->
	    disassembly_log#add "disassembly" 
	                        (LBLOCK [ STR "assembly instruction creates incorrect block entry: " ; 
			                  instr#toPretty ; NL ; p ])
         | Invalid_argument s ->
            raise (BCH_failure (LBLOCK [ STR "record targets of jumps: " ; va#toPretty ;
                                         STR ": " ; STR s ]))
       ) ;
      (* ~~~~~~~~~~~~~~~~~~ add block entries due to previous block-ending instruction *)
      !assembly_instructions#itera
       (fun va instr ->
         try
	   let opcode = instr#get_opcode in
	   let isBlockEnding = 
	     is_jump_instruction opcode || 
	       (match opcode with 
	          Ret _ | BndRet _ | RepzRet | InterruptReturn _ -> true 
	          | IndirectCall _ | DirectCall _ when is_nr_call_instruction instr -> true
                  | DirectCall op when
                         op#is_absolute_address
                         && system_info#is_inlined_function op#get_absolute_address ->
                     begin
                       chlog#add "add inlined call" va#toPretty ;
                       pverbose [ STR  "set inlined call " ; va#toPretty ; NL ] ;
                       set_inlined_call va ;
                       true
                     end
	          |	_ -> false) in
	   if isBlockEnding && !assembly_instructions#has_next_valid_instruction va then
	     set_block_entry (!assembly_instructions#get_next_valid_instruction_address va)
	   else
	     ()
         with
         | Invalid_argument s ->
            raise (BCH_failure (LBLOCK [ STR "previous block-ending instructions: " ;
                                         va#toPretty ; STR ": " ; STR s ])))
    end
  with
  | BCH_failure p ->
     raise (BCH_failure (LBLOCK [ STR "Error in set-block-boundaries: " ; p ]))
  | Invalid_argument s ->
     raise (BCH_failure (LBLOCK [ STR "Error in set-block-boundaries: " ; STR s ]))

(* it is assumed that these are successors to a toplevel block;
   blocks of inlined functions are incorporated all at once *)
let get_successors (faddr:doubleword_int) (iaddr:doubleword_int) =
  if system_info#is_nonreturning_call faddr iaddr then [] else
    let loc = make_location { loc_faddr = faddr ; loc_iaddr = iaddr } in
    let ctxtiaddr = loc#ci in
    let instr = !assembly_instructions#at_address iaddr in
    let finfo = get_function_info faddr in
    let opcode = instr#get_opcode in
    let next () =
      if !assembly_instructions#has_next_valid_instruction iaddr then
        [ !assembly_instructions#get_next_valid_instruction_address iaddr ]
      else
        begin
	  disassembly_log#add "disassembly" 
	                      (LBLOCK [ STR "Next instruction for " ; iaddr#toPretty ; STR " " ; 
		                        instr#toPretty ; STR " was not found" ]) ;
	  []
        end in
    let get_absolute_op (op:operand_int) = 
      let floc = get_floc (make_location {loc_faddr = faddr; loc_iaddr = iaddr}) in
      let opExpr = op#to_expr floc in
      let opExpr = floc#inv#rewrite_expr opExpr finfo#env#get_variable_comparator in
      match opExpr with
      | XVar v when finfo#env#is_global_variable v && finfo#env#has_constant_offset v ->
         let gaddr = finfo#env#get_global_variable_address v in
         pe_sections#get_read_only_initialized_doubleword gaddr
      | XConst (IntConst c) ->
         begin
	   try
	     Some (numerical_to_doubleword c)
	   with
	     _ -> None 
         end
      | _ -> None in
    let is_dll_jump_target_op op =
      (op#is_absolute_address && is_dll_jump_target op#get_absolute_address)
      || (match get_absolute_op op with Some dw -> is_dll_jump_target dw | _ -> false) in
    let get_dll_jump_target_op op =
      let dw =
        if op#is_absolute_address then
	  op#get_absolute_address 
        else
	  match get_absolute_op op with
	  | Some dw -> dw
	  | _ -> raise 
	           (BCH_failure (STR "Internal failure in get_dll_jump_target_op (1)")) in
      match pe_sections#get_imported_function_by_index dw with
      | Some (lib, fname) -> (lib,fname) 
      | _ ->
         match pe_sections#get_imported_function dw with
         | Some (lib,fname) -> (lib,fname)
         | _ -> raise (BCH_failure 
		         (STR "Internal failure in get_dll_jump_target_op (2)")) in    
    let successors = match opcode with
      (* | RepzRet | Ret None | BndRet None -> get_return_successors (get_floca faddr iaddr) *)
      | Ret _ | BndRet _ | RepzRet -> []
      | DirectJmp op 
        | CfJmp(op,_,_) when op#is_absolute_address -> [ op#get_absolute_address ]
      | Jcc (_,op) when system_info#is_fixed_true_branch iaddr && op#is_absolute_address ->
         [ op#get_absolute_address ]
      | IndirectJmp _ when system_info#has_jump_target iaddr -> 
         let (base,jt,db) = system_info#get_jump_target iaddr in
         begin
	   finfo#set_offsettable_target ctxtiaddr base jt db ;
	   (get_floc loc)#get_jump_successors
      end
    | IndirectJmp op when finfo#is_dll_jumptarget ctxtiaddr -> []
    | IndirectJmp op when is_dll_jump_target_op op ->
       let (lib,fname) = get_dll_jump_target_op op in
       let ctinfo = mk_dll_target lib fname in
      begin
	finfo#set_dll_jumptarget ctxtiaddr lib fname ctinfo ;
	[]
      end
    | IndirectJmp _ when finfo#has_jump_target ctxtiaddr -> 
      (get_floc loc)#get_jump_successors
    | IndirectJmp op ->
      begin
	match get_indirect_jump_targets op with
	| Some (jumpBase,table,reg) ->
	  begin
	    finfo#set_jumptable_target ctxtiaddr jumpBase table reg ;
	    (get_floc loc)#get_jump_successors
	  end
	| _ -> 
	  if finfo#has_jump_target ctxtiaddr then [] else
	    let floc = get_floc loc in
	    let tgtexpr = op#to_expr floc in
	    let tgtexpr = floc#inv#rewrite_expr tgtexpr 
	      (finfo#env#get_variable_comparator) in
	    begin
	      match tgtexpr with
	      | XVar tgtvar when not tgtvar#isTmp ->
		 if finfo#env#is_global_variable tgtvar then
		   begin 
		     chlog#add "jump on global" 
		               (LBLOCK [ floc#l#toPretty ; STR ": " ; tgtvar#toPretty ]) ;
		     finfo#set_global_jumptarget ctxtiaddr tgtvar ; 
		    []
		   end
		else
		  begin finfo#set_unknown_jumptarget ctxtiaddr ; [] end 
	      | _ -> begin finfo#set_unknown_jumptarget ctxtiaddr ; [] end
	    end
      end
    | IndirectCall _ | DirectCall _
         when finfo#has_call_target ctxtiaddr
              && (finfo#get_call_target ctxtiaddr)#is_nonreturning ->
      begin
	chlog#add "non-returning instruction"
	  (LBLOCK [ faddr#toPretty ; STR " " ; iaddr#toPretty ; STR " " ;
		    instr#toPretty ]) ;
	[]
      end
    | IndirectCall _ | DirectCall _
         when finfo#has_call_target ctxtiaddr
              && (finfo#get_call_target ctxtiaddr)#is_nonreturning ->
      begin
	chlog#add "non-returning instruction"
	  (LBLOCK [ faddr#toPretty ; STR " " ; iaddr#toPretty ; STR " " ;
		    instr#toPretty ]) ;
	[]
      end
    | DirectCall op when op#is_absolute_address && 
	(functions_data#add_function op#get_absolute_address)#is_non_returning ->
      begin
	chlog#add "non-returning instruction"
	  (LBLOCK [ faddr#toPretty ; STR " " ; iaddr#toPretty ; STR " " ;
		    instr#toPretty ]) ;
	[]
      end
    | IndirectCall op | DirectCall op -> 
      if is_nr_call_instruction instr || 
	   finfo#has_call_target ctxtiaddr
           && (finfo#get_call_target ctxtiaddr)#is_nonreturning then 
	let _ = chlog#add "non-returning instruction"
	  (LBLOCK [ faddr#toPretty ; STR " " ; STR ctxtiaddr ; STR " " ; 
		    instr#toPretty ]) in
	[ ] 
      else
	(next ())
    | DirectLoop op ->
      if op#is_absolute_address then
	(next ()) @ [ op#get_absolute_address ]
      else
	begin
	  chlog#add "disassembly"
	    (LBLOCK [ STR "Target operand of loop instruction is not an absolute address: " ; 
		      iaddr#toPretty ; STR " " ; op#toPretty ]) ;
	  (next ())
	end
    | _ ->
      if is_conditional_jump_instruction opcode then
	let targetOp = get_jump_operand opcode in
	if targetOp#is_absolute_address then
	  (next ())  @ [ targetOp#get_absolute_address ]
	else
	  begin
	    chlog#add "disassembly"
	      (LBLOCK [ STR "Target operand of conditional jump instruction is not an absolute address: " ;
			iaddr#toPretty ; STR "  " ; targetOp#toPretty ]) ;
	    (next ())
	  end
      else
	(next ()) in
    List.map
      (fun va -> (make_location { loc_faddr = faddr ; loc_iaddr = va })#ci)
      (List.filter
         (fun va ->
           if !assembly_instructions#is_code_address va then true else
             begin 
	       chlog#add "disassembly"
	                 (LBLOCK [ STR "Successor of " ; va#toPretty ; 
		                   STR " is not a valid code address" ]) ;
	       false
             end) successors)


let get_call_addr instr =
  match instr#get_opcode with
  | DirectCall op when op#is_absolute_address -> op#get_absolute_address
  | _ -> raise (BCH_failure (LBLOCK [ STR "Internal error in get_call_addr" ]))

(* it is assumed that the block is at the toplevel; blocks for inlined
   functions are incorporated together all at once *)
let trace_block (faddr:doubleword_int) (baddr:doubleword_int) =
  let set_block_entry a = (!assembly_instructions#at_address a)#set_block_entry in  
  let get_instr = !assembly_instructions#at_address in
  let get_next_instr_address = 
    !assembly_instructions#get_next_valid_instruction_address in
  let rec find_last_instruction (va:doubleword_int) (prev:doubleword_int) =
    let instr = get_instr va in
    let floc = get_floc (make_location (mk_base_location faddr va)) in
    if va#equal wordzero then
      (Some [],prev,[])
    else if instr#is_block_entry then
      (None,prev,[])
    else if is_nr_call floc instr then
      (Some [],va,[])
    else if instr#is_inlined_call then
      let a = match instr#get_opcode with
        | DirectCall op -> op#get_absolute_address
        | _ ->
           raise (BCH_failure (LBLOCK [ STR "Internal error in trace block" ])) in
      let fn = assembly_functions#get_function_by_address a in
      let _ = chlog#add "inline blocks" a#toPretty in
      let returnsite = get_next_instr_address va in
      let _ = set_block_entry returnsite in
      let ctxt =
        FunctionContext
          { ctxt_faddr = faddr ;
            ctxt_callsite = va ;
            ctxt_returnsite = returnsite } in
      let tgtloc = make_location { loc_faddr = a ; loc_iaddr = a } in
      let ctxttgtloc = make_c_location tgtloc ctxt in
      let callsucc = ctxttgtloc#ci in 
      let inlinedblocks =
        List.map
          (fun b ->
            let succ =
              match b#get_successors with
              | [] -> [ (make_location { loc_faddr = faddr ; loc_iaddr = returnsite })#ci  ]
              | l -> List.map (fun s -> add_ctxt_to_ctxt_string faddr s ctxt) l in
            make_ctxt_assembly_block ctxt b succ) fn#get_blocks in
      (Some [ callsucc ],va,inlinedblocks)
    else if !assembly_instructions#has_next_valid_instruction va then
      find_last_instruction (get_next_instr_address va) va
    else
      (None,va,[]) in
  let (succ,lastAddress,inlinedblocks) = 
    if !assembly_instructions#has_next_valid_instruction baddr then
      find_last_instruction (get_next_instr_address baddr) baddr
    else (None,baddr,[]) in
  let successors = match succ with
    | Some s -> s
    | _ -> get_successors faddr lastAddress in
  (inlinedblocks,make_assembly_block faddr baddr lastAddress successors)

let trace_function (faddr:doubleword_int) =
  let workSet = new DoublewordCollections.set_t in   (* toplevel only *)
  let doneSet = new DoublewordCollections.set_t in   (* toplevel only *)
  let set_block_entry a = (!assembly_instructions#at_address a)#set_block_entry in
  let get_iaddr s = (ctxt_string_to_location faddr s)#i in
  let add_to_workset l = 
    List.iter (fun a -> if doneSet#has a then () else workSet#add a) l in
  let blocks = ref [] in
  let rec add_block (blockEntry:doubleword_int) =
    let (inlinedblocks,block) = trace_block faddr blockEntry in
    let blockSuccessors =
      match inlinedblocks with
      | []  ->  block#get_successors
      | _ -> [] in
    let inlinedblocksuccessors =
      List.fold_left
        (fun acc b ->
          match b#get_successors with
          | [ h ] when is_iaddress h -> h::acc
          | _ -> acc) [] inlinedblocks in
    begin
      set_block_entry blockEntry ;
      workSet#remove blockEntry ;
      doneSet#add blockEntry ;
      blocks := (block :: inlinedblocks) @ !blocks ;
      add_to_workset (List.map get_iaddr (blockSuccessors @ inlinedblocksuccessors)) ;
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


let collect_function_entry_points () =
  let addresses = new DoublewordCollections.set_t in
  begin
    !assembly_instructions#itera
     (fun va instr ->
       try
         if is_dll_target instr then () else
	   match instr#get_opcode with
	   | DirectCall op when op#is_absolute_address -> 
	      addresses#add op#get_absolute_address
	   | _ -> ()
       with
       | Invalid_argument s ->
          begin
            ch_error_log#add
              "collect function entry points"
              (LBLOCK [ va#toPretty ; STR ": " ; STR s]) ;
            raise (BCH_failure
                     (LBLOCK [ STR "Error in collect functin entry points: " ;
                               va#toPretty ; STR ": " ; STR s ]))
          end);
    chlog#add
      "initialization" 
      (LBLOCK [ STR "Collected " ; INT addresses#size ; STR " functions" ]) ;
    system_info#import_ida_function_entry_points ;
    addresses#addList system_info#get_ida_function_entry_points ;
    chlog#add
      "initialization"
      (LBLOCK [ STR "Total number of function entry points: " ;
                INT addresses#size ]) ;
      addresses#toList
    end

let construct_assembly_function
      (count:int) (starttime:float) (faddr:doubleword_int) =
  let ftime = ref (Unix.gettimeofday ()) in
  let _ = pverbose [ NL ] in
  try
    if !assembly_instructions#is_code_address faddr then
      let _ = pverbose [ STR "." ] in
      let _ = if system_settings#is_verbose then
	  begin
	    pverbose [ faddr#toPretty ; STR "  " ] ;
	    ftime := Unix.gettimeofday () 
	  end in
      let fn = trace_function faddr in
      let finfo = load_function_info faddr in
      let _ = if fn#is_complete then () else finfo#set_incomplete in
      let _ = finfo#set_stack_adjustment fn#get_stack_adjustment in
      let _ = if fn#is_nonreturning then finfo#set_nonreturning in
      let _ = if system_settings#is_verbose then
	  let t = Unix.gettimeofday () in
	  let dt = t -. !ftime in
	  let dtt = t -. starttime in
	  let prt t = STR (Printf.sprintf "%10.4f" t) in
	  pverbose [ fixed_length_pretty ~alignment:StrRight (INT count) 6 ; STR "  " ;
		     faddr#toPretty ; STR "  " ; 
		     prt dt ; STR "  " ; prt dtt ; NL ] in		     
      assembly_functions#add_function fn
    else if system_info#has_data_block faddr && functions_data#has_function_name faddr then
      let bname = (functions_data#get_function faddr)#get_function_name in
      (system_info#get_data_block faddr)#set_name bname
    else
      ch_error_log#add "function entry point not code" faddr#toPretty
  with
  | BCH_failure p ->
    begin
      ch_error_log#add "construct assembly function" 
	(LBLOCK [ faddr#toPretty ; STR ": " ; p ]) ;
      raise (BCH_failure (LBLOCK [ STR "Error in constructing function " ; 
				   faddr#toPretty ; STR ": " ; p ]))
    end


let construct_functions () =
  let _ = system_info#initialize_function_entry_points collect_function_entry_points in
  let _ = set_block_boundaries () in
  let count = ref 0 in
  let starttime = ref (Unix.gettimeofday ()) in
  (* let ftime = ref (Unix.gettimeofday ()) in *)
  let functionEntryPoints = functions_data#get_function_entry_points in
  let _ = pverbose [ NL ; STR "Tracing " ; INT (List.length functionEntryPoints) ;
		     STR " function entry points ... " ; NL ] in
  let _ = chlog#add "initialization" 
    (LBLOCK [ STR "constructing functions for " ; 
	      pp_quantity  (List.length functionEntryPoints) 	
		"function entry point" "function entry points" ]) in
  begin
    List.iter (fun faddr ->
      try
	begin
	  count := !count + 1 ;
	  construct_assembly_function !count !starttime faddr
	end
      with
      | BCH_failure p ->
	ch_error_log#add "construct functions"
	                 (LBLOCK [ STR "Function " ; faddr#toPretty ; STR ": " ; p])
      | Invalid_argument s ->
         ch_error_log#add "construct functions"
                          (LBLOCK [ STR "Function " ; faddr#toPretty ; STR ": " ; STR s ])
    ) functionEntryPoints ;
    pverbose [ NL ; STR "Adding functions found by preamble ... " ; NL ] ;
    List.iter (fun faddr ->
      begin
	count := !count + 1 ;
	construct_assembly_function !count !starttime faddr
      end) assembly_functions#add_functions_by_preamble
  end

let record_call_targets () =
  let starttime = ref (Unix.gettimeofday ()) in
  let prt f = STR (Printf.sprintf "%8.4f" f) in
  let prl i = fixed_length_pretty ~alignment:StrRight (INT i) 8 in
  let count = ref 0 in
  assembly_functions#itera
    (fun faddr f ->
      try
	let finfo = get_function_info faddr in
	let ftime = Unix.gettimeofday () in
	begin
	  count := !count + 1 ;
	  f#iteri
            (fun _ ctxtiaddr instr ->
              let iaddr = (ctxt_string_to_location faddr ctxtiaddr)#i in
	      match instr#get_opcode with
	      | DirectCall op | IndirectCall op ->
	         if finfo#has_call_target ctxtiaddr
                    && (finfo#get_call_target ctxtiaddr)#is_app_call
                    && has_callsemantics
                         (finfo#get_call_target ctxtiaddr)#get_app_address then
                   (* ----- predefined call semantics ----- *)
                   let appaddr =
                     (finfo#get_call_target ctxtiaddr)#get_app_address in
                   let predefined_ctinfo = get_callsemantics_target appaddr in
                   if predefined_ctinfo#is_static_lib_call
                      || predefined_ctinfo#is_inlined_call then
		     begin
		       finfo#set_call_target ctxtiaddr predefined_ctinfo ;
		       finfo#schedule_invariant_reset ;
		       chlog#add
                         "reset invariants"
                         (LBLOCK [ finfo#a#toPretty ; 
				   STR ":" ; STR ctxtiaddr ])
		     end
	           else
                     chlog#add
                       "unrecognized predefined call semantics"
                       (LBLOCK [ faddr#toPretty ; STR ": " ;
                                 STR predefined_ctinfo#get_name ])
                 else
		   if system_info#has_call_target faddr iaddr then
                     let calltgt = system_info#get_call_target faddr iaddr in
                     let ctinfo = mk_call_target_info calltgt in
                     finfo#set_call_target ctxtiaddr ctinfo
                     (* ----- user-provided target -----
		     match system_info#get_call_target faddr iaddr with
		     | ("dll",dllname,dllfn) ->
                        let ctinfo = mk_dll_target dllname dllfn in
                        finfo#set_call_target ctxtiaddr ctinfo
		     | ("app",tgtAddr,_) when 
		            has_callsemantics (string_to_doubleword tgtAddr) -> 
		        finfo#set_call_target
                          ctxtiaddr
		          (get_callsemantics_target (string_to_doubleword tgtAddr))
		     | ("app",tgtAddr,_) ->
		        let ctinfo = mk_app_target (string_to_doubleword tgtAddr) in
		        finfo#set_call_target ctxtiaddr ctinfo
		     | ("jni",index,_) ->
                        let ctinfo = mk_jni_target (int_of_string index) in
                        finfo#set_call_target ctxtiaddr ctinfo
		     | _ -> raise (BCH_failure 
				     (STR "system_info#get_call_target internal error"))
                      *)
		   else
		     begin 
		       match get_dll_target instr with
		       | Some (dll,tgt) ->
                          let _ =
                            track_function
                              ~iaddr:ctxtiaddr
                              faddr
                              (LBLOCK [ STR "Dll: " ; STR dll ; STR "; function: " ;
                                        STR tgt ]) in
                          let ctinfo = mk_dll_target dll tgt in
                          finfo#set_call_target ctxtiaddr ctinfo
		       | _ ->
		          match instr#get_opcode with
		          | DirectCall op
                               when op#is_absolute_address
			            && has_callsemantics op#get_absolute_address ->
			     finfo#set_call_target
                               ctxtiaddr
			       (get_callsemantics_target op#get_absolute_address)
		          | DirectCall op when op#is_absolute_address ->
                             let _ = track_function
                                       ~iaddr:ctxtiaddr
                                       faddr
                                       (LBLOCK [ STR "App: " ;
                                                 op#get_absolute_address#toPretty ]) in
                             let ctinfo = mk_app_target op#get_absolute_address in
			     finfo#set_call_target ctxtiaddr ctinfo
		          | _ ->
                             finfo#set_call_target ctxtiaddr (mk_unknown_target ())
		     end
	      | _ -> ()) ;
	  if system_settings#is_verbose then
	    let etime = Unix.gettimeofday () in
	    pverbose [
                prl !count; STR "  ";
                faddr#toPretty; STR "  ";
		prt (etime -. ftime); STR "  ";
		prt (etime -. !starttime); STR "  ";
		prl f#get_block_count; STR "  ";
		prl f#get_instruction_count; STR "  ";
		prl finfo#env#get_var_count; STR "  ";
		prl finfo#get_call_count; NL]
	end
      with
      | BCH_failure p ->
	 ch_error_log#add
           "record call targets"
	   (LBLOCK [STR "Function "; faddr#toPretty; STR ": "; p])
    )
  
  
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
	  disassembly_log#add "cc user without setter"
	    (LBLOCK [ loc#toPretty ; STR ": " ; 
		      (!assembly_instructions#at_address loc#i)#toPretty ])
      | instr :: tl ->
	match get_flags_set instr#get_opcode with
	| [] -> set tl
	| flags_set -> 
	   if List.for_all (fun fUsed -> List.mem fUsed flags_set) flags_used then
             let iloc = ctxt_string_to_location faddr ctxtiaddr in
             let instrctxt = (make_i_location iloc instr#get_address)#ci in
	     finfo#connect_cc_user ctxtiaddr instrctxt
           else
             chlog#add
               "no flag setter"
               (LBLOCK [faddr#toPretty;
                        STR ", ";
                        STR ctxtiaddr;
                        STR ": ";
                        instr#toPretty]) in
    set revInstrs in
  assembly_functions#itera
    (fun faddr assemblyFunction ->
      assemblyFunction#iter
	(fun block ->
	  block#itera
	    (fun ctxtiaddr instr ->
	      match get_flags_used instr#get_opcode with
	      | [] -> ()
	      | flags -> set_condition flags faddr ctxtiaddr block) ) )
    
    
    
(* -----------------------------------------------------------------------------
   associate values that get pushed onto the stack immediately before a call
   instruction with the call, with arguments counted upwards going back from
   the call. Collect push statements until the beginning of the block or up
   to the number of arguments if the function prototype is known. Exclude
   pushing of Ebp
     ----------------------------------------------------------------------------- 
*)
    
let is_save_caller_reg op = op#is_register && op#get_register = Ebp 
  
let associate_function_arguments_push () =
  let _ = pverbose [ NL ; STR "Associating function arguments for non-gcc compilers" ; NL ] in
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
    let callloc = ctxt_string_to_location faddr callAddress in
    block#itera
      ~high:callloc#i ~reverse:true
      (fun ctxtiaddr instr ->
	if !first then
          first := false        (* skip the call itself *)
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
		let fintf = floc#get_call_target#get_function_interface in
                let fts = fintf.fintf_type_signature in
		match fts.fts_stack_adjustment with
		| Some adj -> compensateForPop := !compensateForPop + (adj / 4)
		| _ -> valid := false
	      else ()
	    | Sub (dst,_) 
	      | Add (dst,_ ) when dst#is_register && dst#get_cpureg = Esp ->
               valid := false
	    | Mov (4,dst,_) when dst#is_memory_access ->
		(match dst#get_kind with
		| IndReg (Esp, offset)
		| ScaledIndReg (None, Some Esp, 1, offset)
		| ScaledIndReg (Some Esp, None, 1, offset) ->
		  if offset#equal numerical_zero then valid := false
		| _ -> ())
	    | _ -> ()) in
  
  let identify_arguments ~(callAddress:ctxt_iaddress_t) ~(block:assembly_block_int) =
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
          first := false        (* skip the call itself *)
	else
	  if !valid && !active then
	    match instr#get_opcode with
	    | Pop _ -> compensateForPop := true
	    | Push _ when !compensateForPop -> compensateForPop := false
	    (*| Push op when is_save_caller_reg op -> () *)
	    | Push (_,op) -> 
	      begin 
		argNr := !argNr + 1 ;
		op#set_function_argument callAddress !argNr;
	      end
	    | Sub (dst,_) 
	    | Add (dst,_ ) when dst#is_register && dst#get_cpureg = Esp -> valid := false
	    | Mov (4,dst,_) when dst#is_memory_access ->
		(match dst#get_kind with
		| IndReg (Esp, offset)
		| ScaledIndReg (None, Some Esp, 1, offset)
		| ScaledIndReg (Some Esp, None, 1, offset) ->
		  if offset#equal numerical_zero then valid := false
		| _ -> ())
	    | DirectCall _ | IndirectCall _ -> active := false
	    | _ -> ())  in
  
  assembly_functions#itera
    (fun faddr assemblyFunction ->
      try
	assemblyFunction#iter
	  (fun block ->
	    block#itera
	      (fun ctxtiaddr instr ->
                let loc = ctxt_string_to_location faddr ctxtiaddr in
                let iaddr = loc#i in
		let floc = get_floc loc in
		match instr#get_opcode with
		| DirectCall op when 
		       op#is_absolute_address
                       && has_callsemantics op#get_absolute_address ->
		  let semantics = get_callsemantics op#get_absolute_address in
		  let numParams = semantics#get_parametercount in
		  identify_known_arguments ~callAddress:ctxtiaddr ~numParams ~block faddr
		| DirectCall _ | IndirectCall _ ->
		   if floc#has_call_target
                      && floc#get_call_target#is_signature_valid then
		      let fintf = floc#get_call_target#get_function_interface in
		      let numParams =
                        List.length (get_stack_parameter_names fintf) in
		      identify_known_arguments
                        ~callAddress:ctxtiaddr ~numParams ~block faddr
		    else if system_info#has_esp_adjustment faddr iaddr then
		      let numParams = system_info#get_esp_adjustment faddr iaddr in
		      identify_known_arguments
                        ~callAddress:ctxtiaddr ~numParams ~block faddr
		    else
		      identify_arguments ~callAddress:ctxtiaddr ~block
		| _ -> ())
	  )
      with
      | BCH_failure p ->
	 ch_error_log#add
           "associate function arguments (push)"
	   (LBLOCK [
                STR "Function ";
                assemblyFunction#get_address#toPretty;
                STR ": ";
                p])
    )
		
let associate_function_arguments_mov () =
  let _ =
    pverbose [
        NL;
        STR "Associating function arguments for gcc-like compilers" ;
	NL] in
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
		     (List.init
                        numParams
                        (fun i->i)) !argumentsFound (fun x y -> x=y) in
		 begin
		   (match argumentsNotFound with
		    | [] -> ()
		    | _ ->
		       ch_error_log#add
                         "function arguments"
		         (LBLOCK [
                              STR "Unable to collect all arguments for ";
			      STR callAddress;
			      STR ". Arguments ";
			      pretty_print_list argumentsNotFound
				(fun n -> INT n) "[" ";" "]";
			      STR " are missing"]));
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
	  if !first then first := false          (* skip the call itself *)
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
		       op#is_absolute_address
                       && has_callsemantics op#get_absolute_address ->
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
  let starttime = ref (Unix.gettimeofday ()) in
  let prt t = STR (Printf.sprintf "%8.4f" t) in
  let get_time () = (Unix.gettimeofday ()) -. !starttime in
  begin
    record_call_targets () ;
    pverbose [ STR "-- record call targets: " ; prt (get_time ()) ; NL ] ;
    associate_condition_code_users () ;
    pverbose [ STR "-- associate condition codes: " ; prt (get_time ()) ; NL ] ;
    associate_function_arguments () ;
    pverbose [ STR "-- associate function arguments: " ; prt (get_time ()) ; NL ]
  end


let get_arg_var_offset (floc:floc_int) (var:variable_t) = None
                                                        
let get_init_reg_offset (floc:floc_int) (var:variable_t) = None
                                                         
let is_jni_environment_variable (floc:floc_int) (v:variable_t) =
  (not v#isTmp) &&
    (((floc#f#env#variable_name_to_string v) = "jni$Env") ||
	((floc#f#env#variable_name_to_string v) = "special_jni$Env"))


let set_call_address (floc:floc_int) (op:operand_int) =
  let _ = pverbose [ STR "Resolve " ; floc#l#toPretty ; STR ": " ; op#toPretty ] in
  let env = floc#f#env in
  let variable_to_pretty = env#variable_name_to_pretty in
  let opExpr = op#to_expr floc in
  let opExpr = floc#inv#rewrite_expr opExpr env#get_variable_comparator in
  let _ = pverbose [ STR " rewrites to " ; xpr_formatter#pr_expr opExpr ; NL ] in
  let changes_stack_adjustment () =
    if floc#has_call_target
       && floc#get_call_target#is_signature_valid then
      match floc#get_call_target#get_stack_adjustment with
      | Some adj -> adj > 0
      | _ -> false
    else
      false in
  let reset () = 
    if (floc#has_call_target && floc#get_call_target#has_sideeffects)
       || changes_stack_adjustment () then 
      begin 
	floc#f#schedule_invariant_reset ;
	chlog#add "reset invariants" (LBLOCK [ floc#l#toPretty ])
      end in
  let logmsg msg = chlog#add "indirect call resolved" 
    (LBLOCK [ floc#l#toPretty ; STR ": " ; msg ]) in
  let pull_data v =
    match pull_call_targets floc v with
    | [] -> 
      chlog#add "indirect call not resolved"
	(LBLOCK [ floc#l#toPretty ; STR ": " ; v#toPretty ])
    | [ StubTarget (DllFunction (dll,fname)) ] ->
       let ctinfo = mk_dll_target dll fname in
      begin 
	pverbose [ STR "Set dll target " ; STR fname ; NL ] ;
	floc#set_call_target ctinfo
      end
    | [ AppTarget addr ] ->
       let ctinfo = mk_app_target addr in
      begin
	pverbose [ STR "Set app target " ; addr#toPretty ; NL ] ;
	floc#set_call_target ctinfo
      end
    | [ StubTarget (JniFunction jni) ] ->
       floc#set_call_target (mk_jni_target jni)
    | l -> () in
  match opExpr with
  | XConst (IntConst c) ->
    begin
      match get_constant_call_targets floc c with
      | [ tgt ] -> 
	begin
	  (match tgt with
	   | StubTarget (DllFunction (dll,name)) ->
              floc#set_call_target (mk_dll_target dll name)
	   | AppTarget dw ->
              floc#set_call_target (mk_app_target dw)
	  | _ -> ()) ;
	  logmsg (call_target_to_pretty tgt) ;
	  reset ()
	end
      | _ -> ()
    end

  | XVar v when env#is_calltarget_value v ->
    let tgt = env#get_calltarget_value v in
    begin
      (match tgt with
       | StubTarget (DllFunction (dll,name)) ->
          floc#set_call_target (mk_dll_target dll name)
       | AppTarget dw ->
          floc#set_call_target (mk_app_target dw)
      | _ -> ()) ;
      logmsg (call_target_to_pretty tgt) ;
      reset ()
    end

  | XVar v when env#is_global_variable v && env#has_constant_offset v ->
    let gaddr = env#get_global_variable_address v in
    begin
      match pe_sections#get_read_only_initialized_doubleword gaddr with
      | Some dw ->
	if (!assembly_instructions)#is_code_address dw then
	  if assembly_functions#has_function_by_address dw then
	    begin
	      logmsg (LBLOCK [ STR "application call to " ; dw#toPretty ]) ;
	      floc#set_call_target (mk_app_target dw) ;
	      reset ()
	    end
	  else
	    begin
	      ignore (functions_data#add_function dw) ;
              pverbose [ STR "add funcion entry point: " ; dw#toPretty ; NL ] ;
	      chlog#add "global variable function entry point" dw#toPretty
	    end
	else
	  begin
	    match pe_sections#get_imported_function gaddr with
	      Some (dll,name) ->
		begin
		  logmsg (LBLOCK [ STR "library call to " ; STR name ]) ;
		  floc#set_call_target (mk_dll_target dll name) ;
		  reset () ;
		  (* check_nonreturning name floc *)
		end
	    | _ -> 
	      chlog#add "indirect call not resolved" 
		(LBLOCK [ floc#l#toPretty ; 
			  STR " Indirect call resolves to address outside code section: " ;
			  dw#toPretty ])
	  end
      | _ ->       
	match pe_sections#get_imported_function gaddr with
	| Some (dll,name) -> 
	  begin
	    logmsg (LBLOCK [ STR "library call to " ; STR name ]) ;
	    floc#set_call_target (mk_dll_target dll name) ;
	    reset ()
	  end
	| _ -> pull_data v
    end
  | XVar v when env#is_virtual_call v ->
     let ctinfo = mk_virtual_target (env#get_virtual_target v) in
    begin
      chlog#add "indirect call resolved"
	        (LBLOCK [ floc#l#toPretty ;
                          STR ": virtual call " ; variable_to_pretty v ]) ;
      floc#set_call_target ctinfo
    end
  | XVar v -> pull_data v
  | _ -> 
    chlog#add "indirect call not resolved" 
      (LBLOCK [ floc#l#toPretty ; STR ": expression not recognized " ; pr_expr opExpr ])
      
let resolve_indirect_calls (f:assembly_function_int) =
  let _ =
    f#iteri
      (fun faddr ctxtiaddr instr ->
        let loc = ctxt_string_to_location faddr ctxtiaddr in
        match instr#get_opcode with
        | IndirectCall op ->
           let floc = get_floc loc in
           if (not floc#has_call_target)
              || floc#get_call_target#is_unknown then
             set_call_address floc op
        | _ -> ()) in
  ()

let disassemble_pe () =
  let entrypointVA = system_info#get_address_of_entry_point in
  let codeSectionHeaders =
    List.find_all (fun h ->
      h#is_executable || h#includes_VA entrypointVA ||
	List.exists h#includes_VA system_info#get_userdeclared_codesections)
      pe_header#get_section_headers in
  let msg = ref [] in
  match codeSectionHeaders with
  | [] -> (false, LBLOCK [ STR "No executable sections found" ; NL ])
  | l ->
    try
      let numSections = List.length l in
      let _ =
	if numSections > 1 then
	  msg := (LBLOCK [ STR "Found " ; INT numSections ; 
			   STR " executable sections" ; NL ]) :: !msg in
      let size = disassemble_sections codeSectionHeaders in
      begin
	msg := (LBLOCK [ STR "Disassembled " ; INT size ; STR " bytes into " ; 
			 INT !assembly_instructions#get_num_instructions ;
			 STR " instructions" ; NL ]) :: !msg ;
	(true,LBLOCK (List.rev !msg))
      end
    with
    | Invocation_error s
    | Invalid_argument s 
    | Failure s ->
      begin
	msg := (LBLOCK [ STR "Failure in disassembly: " ; STR s ; NL ]) :: !msg ;
	(false, LBLOCK (List.rev !msg))
      end
    | BCH_failure p ->
      begin
	msg := (LBLOCK [ STR "Failure in disassembly: " ; p ; NL ]) :: ! msg ;
	(false, LBLOCK (List.rev !msg))
      end

let construct_functions_pe () =
  try
    begin
      construct_functions () ;
      decorate_functions () ;
      (true, LBLOCK [ STR "Constructed " ; 
		      INT (List.length assembly_functions#get_functions) ;
		      STR " functions" ; NL ])
    end
  with
  | Invocation_error s
  | Invalid_argument s
  | Failure s ->
    (false, LBLOCK [ STR "Failure in constructing functions: " ; STR s ; NL ])
  | BCH_failure p ->
    (false, LBLOCK [ STR "Failure in constructing functions: " ; p ; NL ])
      

      


		

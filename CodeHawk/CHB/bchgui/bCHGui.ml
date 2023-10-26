(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Cody Schuffelen and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHCommon
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHPrettyUtil
open CHFileIO
open CHLogger
open CHCHIFXml
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHDoubleword
open BCHFunctionInfo
open BCHLibTypes
open BCHMemoryReference
open BCHPreFileIO
open BCHSystemInfo
open BCHVariable
open BCHXmlUtil

(* bchlibpe *)
open BCHPESections
open BCHPEHeader

(* bchlibx86 *)
open BCHAssemblyInstructions
open BCHAssemblyInstructionAnnotations
open BCHAssemblyFunction
open BCHAssemblyFunctions
open BCHConditionalJumpExpr
open BCHDisassemble
open BCHDisassemblyMetrics
open BCHIFSystem
open BCHLibx86Types
open BCHLoopStructure
open BCHPreFileIO
open BCHTranslateToCHIF
open BCHX86Opcodes

(* bchlibelf
open BCHELFHeader
open BCHDWARFLineNumbers
*)

(* bchanalyze *)
open BCHTrace

(* bchgui *)
open BCHGuiUtil
open BCHCanvasUtil
open BCHDllFunctionsDisplay
open BCHFunctionsDisplay
open BCHSystemDisplay
open BCHStateDialogs

module H = Hashtbl
module TR = CHTraceResult


(*
module BTypeCollections = CHCollections.Make
  (struct
    type t = btype_t
    let compare = btype_compare 
    let toPretty = btype_to_pretty
   end) *)

let flush_x () = while Glib.Main.iteration false do () done
let delete_event ev = false
let destroy () = GMain.Main.quit ()

let string_printer = CHPrettyUtil.string_printer

(* ---------------------------------------------------- dll functions display --

let dll_functions_page =
  let label = GMisc.label ~text:"              DYNAMICALLY LOADED FUNCTIONS             " () in
  let _ = BCHDllFunctionsDisplay.dll_functions_display#initialize in
  main_notebook#append_page ~tab_label:label#coerce 
    (BCHDllFunctionsDisplay.dll_functions_display#get_display)#coerce

*)

(* -------------------------------------------------------- functions display -- *)

let functions_page =
  let label = GMisc.label ~text:"              APPLICATION FUNCTIONS             " () in
(*
  let dll_functions_page_activation = (fun () -> main_notebook#goto_page dll_functions_page) in
*)
  let _ = BCHFunctionsDisplay.functions_display#initialize window in
  main_notebook#append_page ~tab_label:label#coerce 
    (BCHFunctionsDisplay.functions_display#get_display)#coerce

(*
let opt_statically_linked_functions_page = ref None

let make_statically_linked_functions_page (staticallyLinkedFunctions:assembly_function_int list) =
  let dll_functions_page_activation = (fun () -> main_notebook#goto_page dll_functions_page) in
  let statically_linked_functions_display = 
    make_statically_linked_functions_display dll_functions_page_activation staticallyLinkedFunctions window in
  let label = GMisc.label ~text:"      STATICALLY LINKED LIBRARY FUNCTIONS      " () in
  opt_statically_linked_functions_page :=
    Some (main_notebook#append_page ~tab_label:label#coerce 
	    (statically_linked_functions_display#get_display)#coerce) 

*)

(* ----------------------------------------~--------------------- menu action -- *)

let all_files () = GFile.filter ~name:"All" ~patterns:["*"] ()
let exe_filter () = GFile.filter ~name:"executables" ~patterns:["*.exe"] ()

let about_codehawk () = about_codehawk ()

let save_system_display () =  save_system_display_contents ()

let save_user_data () = ()
(*
  let msg_pp = user_provided_application_facts#save in
  write_message_pp msg_pp
*)

let save_chif () =
  let filename = system_info#get_filename in
  try
    let outputFilename = filename ^ "_chif" in
    begin
      file_output#saveFile outputFilename chif_system#get_system#toPretty ;
      write_message ("Saved chif to " ^ outputFilename)
    end
  with
    CHIOFailure s ->
      write_message ("Unable to save chif: " ^ s)

let save_session () = ()
(*
  let filename = system_info#get_filename in
  let doc = system_to_xml chif_system#get_system in
  try
    let outputFilename = filename ^ "_ch_session.xml" in
    begin
      file_output#saveFile outputFilename doc#toPretty ;
      write_message ("Saved session to " ^ outputFilename)
    end
  with
    CHIOFailure s ->
      write_message ("Unable to save session: " ^ s)
 *)
let save_variable_types () = ()

let save_variables () = ()

let save_memory_references () = ()

let reset_log () = 
  begin
    chlog#reset ;
    write_message "Reset log"
  end

let quit_analyzer () =
(*
  if user_provided_application_facts#changes_made then
    let yes_action = (fun () -> 
      let msg = user_provided_application_facts#save in
      write_message_pp msg) in
    let no_action = (fun () -> destroy ()) in
    confirmation_dialog ~title:"Save changes"
      ~label:"Changes were made to the user-provided facts.\nDo you want to save them?"
      ~yes_action ~no_action ~parent:window 
  else   *)
    destroy ()

let executable_headers = ref []

let read_pe () =
	(* elfHeader := None; *)
	pe_header#read;
	executable_headers := 
	  List.find_all (fun header -> header#is_executable) pe_header#get_section_headers;
	()

(* Ugly hack to force it to load the text section and symbol table
let read_elf exeString =
	let elf = BCHELFHeader.makeFileHeader exeString in
	elfHeader := Some (elf);
	elf#update_globals;
	dwarfLineNumbers :=
		(try Some (makeDWARFDebugLines elf (elf#get_section_by_name ".debug_line"))
		with e -> print_endline "error constructing debug lines"; None);
	executable_headers := [elf#get_text_section#disguiseAsPE];
	()
*)
(*
let read_executable () = 
  let maxStringSize = 1000000000 in
  let ch = open_in_bin !filename in 
  let ch = IO.input_channel ch in
  let exeString = IO.nread ch maxStringSize in
  let size = String.length exeString in
  let hexSize = BCHDoubleword.int_to_doubleword size in
  try
    let _ = system_info#set_exe_string exeString in
    (* let _ = if (String.sub exeString 1 4) = "ELF" then  *)
    let _ = if Filename.check_suffix !filename "exe" || Filename.check_suffix !filename "dll" then
	begin
	  pr_debug [ STR "Read PE file" ; NL ] ;
	  read_pe () 
	end 
      else
	begin
	  pr_debug [ STR "Reading in ELF file" ; NL ] ;
	  read_elf exeString 
	end in
    let fileBasename = 
      try Filename.chop_extension !filename with 
	Invalid_argument _ -> !filename in
    begin
      dll_functions_display#set_model pe_sections#get_imported_functions ;
      write_message_pp (LBLOCK [ STR "Reading in " ; STR !filename ; STR " (size: " ; INT size ;
				 STR " (" ; hexSize#toPretty ; STR ") bytes)" ; NL ]) ; 
    (* write_to_system_display_pp "PEheader" pe_header#toPretty ; *)
    end
  with
    Sys_error s ->
      write_message ("Unable to read " ^ !filename ^ ": " ^ s ) ;
  | BCH_failure p ->
    write_message_pp (LBLOCK [ STR "Unable to read " ; STR !filename ; STR ": " ; p ])
  | XmlDocumentError (line,col,p) ->
    write_message_pp (LBLOCK [ STR "Xml error (" ; INT line ; STR ", " ; INT col ; STR "): " ; p ])
*)

(*
let disassemble () =
(*  BCHApplicationSignatures.appsigs#register_variable_names ;
  let codeSectionHeaders = List.find_all (fun header -> header#is_executable) pe_header#get_section_headers in *)
  let codeSectionHeaders = !executable_headers in
  let _ = match codeSectionHeaders with 
      [] ->
	write_message ("File does not contain any executable sections; no disassembly peformed")
    | l ->
      (try
	 let numSections = List.length l in
	 let _ = (if numSections > 1 then
	     write_message ("Disassembling " ^ (string_of_int numSections) ^ " code sections .......") 
	   else
	     write_message ("Disassembling code section .......")) in
	 let _ = BCHCanvasCallgraph.canvas_call_graph#reset in
	 let _ = BCHOrphanCode.orphan_code#reset in
	 let size = BCHDisassemble.disassemble_sections codeSectionHeaders in
	 let _ = BCHFunctionsDisplay.functions_display#reset in
	 let message = LBLOCK [ STR "Disassembled " ; INT size ; STR " bytes into " ; 
				INT !assembly_instructions#get_num_instructions ; 
				STR " instructions" ] in
	 begin
	   write_to_system_display_pp "ch_message" message ;
	   write_message_pp message
	 end
       with
	 BCH_failure p -> 
	   begin
	     write_message_pp  (LBLOCK [ STR "Failure in disassembly: " ; p ]) ;
	   end ) in
  ()


let disassemble () =
  let entryPointVA = system_info#get_address_of_entry_point in
  let codeSectionHeaders =
    List.find_all (fun h -> h#is_executable || h#includes_VA entryPointVA)
      pe_header#get_section_headers in
  match codeSectionHeaders with
  | [] -> pr_debug [ STR "No executable sections found " ; NL ]
  | l ->
    try
      let numSections = List.length l in
      let _ = 
	if numSections > 1 then
	  pr_debug [ STR "Disassembling " ; INT numSections ; 
		     STR " executable sections" ; NL ] in
      let size = disassemble_sections codeSectionHeaders in
      pr_debug [ STR "Disassembled " ; INT size ; STR " bytes into " ; 
		 INT !assembly_instructions#get_num_instructions ; STR " instructions" ; NL ]
    with
      BCH_failure p -> pr_debug [ STR "Failure in disassembly: " ; p ; NL ]

*)
    
let opt_statically_linked_functions_display = ref None

let initial_display_to_pretty () =  ()
(*
  begin
    file_metrics#load_xml ;
    LBLOCK [ 
      STR "Viewing the analysis results of " ; 
      STR (get_filename ()) ; NL ; NL ;
      STR "At startup only the entry function is loaded. " ;
      STR "Use the Functions menu or the Callers/Callees buttons to load more functions" ;
      NL ; NL ;
      STR "Go to the APPLICATION FUNCTIONS tab to view the functions loaded" ; NL ; NL ;
      file_metrics#toPretty ; NL ]
  end
 *)
let construct_functions () = ()
(*
  try
    let instructionCount = !assembly_instructions#get_num_instructions in
    let fentry = system_info#get_address_of_entry_point in
    begin
      write_message ("Finding functions in " ^ (string_of_int instructionCount) ^ 
			" assembly instructions .......");
      let (success,msg) = BCHDisassemble.construct_functions_pe () in
      (if assembly_functions#has_function_by_address fentry then
	  begin
	    ignore (add_function_listed fentry#to_hex_string) ;
	    let f = get_assembly_function fentry in
	    functions_display#set_model [ f ] ;
	    ignore (load_function_info fentry) ;
	    translate_assembly_function f  ;
	    record_cfg_info fentry ;
	    write_message_pp (LBLOCK [ msg ; STR ". " ; 
				       STR "Loaded function entry point " ; 
				       fentry#toPretty ]) 
	  end
       else
	  write_message_pp (LBLOCK [ STR "Function entry point " ; fentry#toPretty ;
				     STR " was not found. No functions loaded" ])) ;
      write_to_system_display_pp "initial" ( initial_display_to_pretty () )
    end

      let functions = match fns with 
	| [] -> assembly_functions#get_application_functions
	| _ -> List.map (fun a -> 
	  assembly_functions#get_function_by_address (string_to_doubleword a)) fns in
      let _ = set_functions_listed (List.map (fun f -> f#get_address#to_hex_string) functions) in
      let message = 
	LBLOCK [ STR "Constructed " ; INT (List.length functions) ; STR " functions" ; NL ] in
      begin
	write_message_pp 
	  (LBLOCK [ message ; STR "; now initializing function access list ....... " ]) ;
	functions_display#set_model functions ;
	(match staticallyLinkedFunctions with
	    [] -> ()
	  | _ -> make_statically_linked_functions_page staticallyLinkedFunctions) ;
	write_to_system_display_pp "ch_message" (LBLOCK [ NL ; message ]) ;
	((!BCHAssemblyInstructions.assembly_instructions)#toString ()) ;
	write_message_pp message ;
      end
    end 
  with
      BCH_failure p ->
	begin
	  write_message_pp (LBLOCK [ STR "Failure in constructing functions: " ; p ] );
	  ch_error_log#add "disassembly"
	    (LBLOCK [ STR "Failure in constructing functions: " ; p ])
	end			    
 *)

let do_translation fns =
  let total = List.length (assembly_functions#get_functions) in
  let completed = ref 0 in
  let functions_skipped = ref 0 in
  let functions_failed = ref 0 in
  try
    begin
      write_message ("Translating " ^ (string_of_int total)  ^ " functions .......") ;
      assembly_functions#iter
	(fun f -> 
	  if fns = [] || List.mem f#get_address#to_hex_string fns then
	  try
	   (* let _ = if check_interrupt () then raise RequestInterrupt in
	    let _ = if check_skip () then raise RequestSkip in  *)
	    (* let faddr = f#get_address in *)
	    (* let fname = faddr#to_hex_string in *)
	    begin
	      translate_assembly_function_by_address f#get_address ;
	      completed := !completed + 1 ;
	      set_progress_bar !completed total
	    end
	  with
	  | CHFailure p ->
	    begin
	      ch_error_log#add "translation"
		(LBLOCK [ STR "CHFailure in translating assembly function " ; 
			  f#get_address#toPretty ;
			  STR ": " ; p ]) ;
	      functions_failed := !functions_failed + 1
	    end
	  | BCH_failure p ->
	    begin
	      ch_error_log#add "translation"
		(LBLOCK [ STR "Failure in translating assembly function " ; 
			  f#get_address#toPretty ;
			  STR ": " ; p ]) ;
	      functions_failed := !functions_failed + 1
	    end
	  | Internal_error s ->
	    begin
	      ch_error_log#add "translation" 
		(LBLOCK [ STR "Internal error in " ; f#get_address#toPretty ;
			  STR ": " ; STR s]) ;
	      functions_failed := !functions_failed + 1
	    end
	  | Invocation_error s ->
	    begin
	      ch_error_log#add "translation" 
		(LBLOCK [ STR "Invocation error in " ; f#get_address#toPretty ;
			  STR ": " ; STR s]) ;
	      functions_failed := !functions_failed + 1
	    end
	  | Invalid_input s ->
	    begin
	      ch_error_log#add "translation" 
		(LBLOCK [ STR "Invalid input in " ; f#get_address#toPretty ;
			  STR ": " ; STR s]) ;
	      functions_failed := !functions_failed + 1
	    end
	  | _ ->
	    begin
	      chlog#add "skip" 
		(LBLOCK [ STR "Skip requested in translation of " ; 
			  f#get_address#toPretty ]) ;
	      (* interrupt_handler#clear_skip ; *)
	      functions_skipped := !functions_skipped + 1
	    end
	)	;
      write_message_pp 
	(LBLOCK [ STR "Translated " ; INT !completed ; STR " functions " ;
		  (if !functions_skipped > 0 then 
		      LBLOCK [ STR "(" ; INT !functions_skipped ; STR " were skipped) "] 
		   else STR "") ;
		  (if !functions_failed > 0 then
		      LBLOCK [ STR "(" ; INT !functions_failed ; 
			       STR " failed to translate) " ]
		   else STR "") ]) ;
      reset_progress_bar () ;
    end
  with
    _ ->
      begin
	chlog#add "interrupt" (LBLOCK [ STR "Interrupt requested in translation " ]) ;
	(* interrupt_handler#reset ; *)
	write_message_pp 
	  (LBLOCK [ STR "Translated " ; INT !completed ; STR " functions out of " ; 
		    INT total ; STR ". Translation was interrupted" ]) ;
	reset_progress_bar ()
      end

let translate_functions fns =
  let _ = do_translation fns in
  begin
    write_to_system_display_pp "SystemTranslationStatistics" 
      (LBLOCK [ STR "Translation completed" ; NL ]) ;
    goto_system_page ()
  end

let open_file_dialog () =
  let dialog = 
    GWindow.file_chooser_dialog ~action:`OPEN ~title:"Open File" ~parent:window () in
  begin
    dialog#add_button_stock `CANCEL `CANCEL ;
    ignore (dialog#set_current_folder (Sys.getcwd ())) ;
    dialog#add_select_button_stock `OPEN `OPEN ;
    dialog#add_filter (all_files ()) ;
    dialog#add_filter (exe_filter ()) ;
    dialog#set_filter (exe_filter ()) ;
    (match dialog#run () with
    | `OPEN -> 
	begin
	  match dialog#filename with
	    Some name -> 
	      let filename = Filename.basename name in
	      begin
		system_info#set_filename filename ;
		write_message ("Selected file " ^ name)
	      end
	  | _ -> write_message "No file selected"
	end
    | `CANCEL 
    | `DELETE_EVENT -> write_message "No file selected") ;
    dialog#destroy () ;
    if system_info#get_filename = "" then ()
    else match load_pe_header_file () with
    | Some node ->
      begin
	(* appsigs#read_appsig_file !filename ; *)
	pe_header#read_xml node ;
	ignore (disassemble_pe ()) ;
	ignore (construct_functions ()) ;
      end
    | _ -> write_message ("No xml file found with pe-header for " ^ system_info#get_filename)
  end

let view_pe_header () =
  begin
    write_to_system_display_pp
      "PEheader" (LBLOCK [pe_header#coff_file_header_to_pretty ; NL ; 
			  pe_header#optional_header_to_pretty ]) ;
    write_message "Displayed PE Header" ;
    goto_system_page ()
  end

let view_data_directory  () =
  begin
    write_to_system_display_pp "DataDirectory" pe_header#data_directory_to_pretty ;
    write_message "Displayed data directory" ;
    goto_system_page ()
  end

let view_section_headers () = 
  begin
    write_to_system_display_pp "SectionHeaders" pe_header#section_headers_to_pretty ;
    write_message "Displayed section headers" ;
    goto_system_page ()
  end

let view_export_table    () = 
  begin
    write_to_system_display_pp "ExportTable" pe_sections#export_directory_table_to_pretty ;
    write_message "Displayed export table" ;
    goto_system_page ()
  end

let view_import_tables   () = 
  begin
    write_to_system_display_pp "ImportTables" pe_sections#import_directory_table_to_pretty ;
    write_message "Displayed import tables" ;
    goto_system_page ()
  end

let view_load_configuration_directory () =
  begin
    write_to_system_display_pp "ConfigurationDirectory" 
      pe_sections#load_configuration_directory_to_pretty ;
    write_message "Displayed load configuration directory" ;
    goto_system_page ()
  end

let view_resource_table () = 
  begin
    write_to_system_display_pp "ResourceTable" pe_header#resource_directory_to_pretty ;
    write_message "Displayed resource table" ;
    goto_system_page ()
  end

let view_table_layout   () =
  begin
    write_to_system_display_pp "TableLayout" pe_header#table_layout_to_pretty ;
    write_message "Displayed table layout" ;
    goto_system_page ()
  end

let view_raw_sections () =
  let section_headers = pe_header#get_section_headers in
  let section_data =
    List.map (fun h -> (h#index,h#get_name, h#get_RVA#to_hex_string,
			h#get_virtual_size#to_hex_string)) section_headers in
  let select_action = (fun index ->
    let section = pe_sections#get_section index in
    let _ = write_message ("Preparing section " ^ section#get_name ^ " .......") in
    let pp = LBLOCK [ section#get_header#toPretty ; NL ; NL ; STR (section#raw_data_to_string []) ] in
    let name = "Section_" ^ section#get_name in
    let _ = write_message ("Displaying section " ^ section#get_name ^ " .......") in
    let _ = write_to_system_display_pp name pp in
    let _ = write_message ("Displayed section " ^ section#get_name) in
    ()) in
  let _ = select_section_dialog ~window_title:"Select a section" 
    ~data:section_data ~parent_window:window 
    ~label_text:"Double click the name of a section" ~select_action:select_action in
  goto_system_page ()

(*
let view_elf_header () =
	match !elfHeader with
		None -> ()
		| Some elf ->
			write_to_system_display_pp "ELFHeader" elf#toPretty;
			write_message "Displayed ELF header." ;
			goto_system_page ()

let view_elf_section_headers () =
	match !elfHeader with
		None -> ()
		| Some elf ->
			let pp = LBLOCK (List.map (fun f -> LBLOCK[f#toPretty; NL; NL]) elf#get_all_section_headers) in
			write_to_system_display_pp "ELF Section Headers" pp;
			write_message "Displayed ELF Section Headers.";
			goto_system_page ()

let view_elf_symbol_table () =
	match !elfHeader with
		None -> ()
		| Some elf ->
			write_to_system_display_pp "Symbol Table" (elf#get_symbol_table_by_string ".symtab")#toPretty;
			write_message "Displayed ELF Symbol Table";
			goto_system_page ()

let view_elf_dynamic_symbol_table () =
	match !elfHeader with
		None -> ()
		| Some elf ->
			write_to_system_display_pp "Dynamic Symbol Table" (elf#get_symbol_table_by_string ".dynsym")#toPretty;
			write_message "Displayed ELF Dynamic Symbol Table";
			goto_system_page ()

let view_elf_plt_relocation_table () =
	match !elfHeader with
		None -> ()
		| Some elf ->
			write_to_system_display_pp "PLT Relocation Table" (elf#get_relocation_table_by_string ".rel.plt")#toPretty;
			write_message "Displayed PLT Relocation Table";
			goto_system_page ()

let view_elf_dynamic_relocation_table () =
	match !elfHeader with
		None -> ()
		| Some elf ->
			write_to_system_display_pp "PLT Relocation Table" (elf#get_relocation_table_by_string ".rel.dyn")#toPretty;
			write_message "Displayed Dynamic Relocation Table";
			goto_system_page ()
*)
let view_raw_assembly () =
  begin
    write_to_system_display "RawAssemblyCode"
      ((!BCHAssemblyInstructions.assembly_instructions)#toString ())  ;
    write_message "Displayed raw assembly code" ;
    goto_system_page ()
  end

let view_data_blocks () =
  begin 
    write_to_system_display "DataBlocks"
      (String.concat "\n\n" (List.map (fun b -> b#toString) !assembly_instructions#get_data_blocks)) ;
    write_message "Displayed data blocks" ;
    goto_system_page ()
  end

let view_call_instructions () = 
  let filter = 
    (fun instr -> match instr#get_opcode with DirectCall _ | IndirectCall _ -> true | _ -> false) in
  begin
    write_to_system_display "CallInstructions"
      ((!BCHAssemblyInstructions.assembly_instructions)#toString ~filter ()) ;
    write_message "Displayed call instructions" ;
    goto_system_page ()
  end

let view_indirect_calls () =
  let filter = (fun instr -> match instr#get_opcode with IndirectCall _ -> true | _ -> false) in
  begin
    write_to_system_display "IndirectCalls"
      ((!BCHAssemblyInstructions.assembly_instructions)#toString ~filter ()) ; 
    write_message "Displayed indirect calls" ;
    goto_system_page ()
  end

let view_indirect_jumps () =
  let filter = (fun instr -> match instr#get_opcode with IndirectJmp _ -> true | _ -> false) in
  begin
    write_to_system_display "IndirectJumps"
      ((!BCHAssemblyInstructions.assembly_instructions)#toString ~filter ()) ;
    write_message "Displayed indirect jumps" ;
    goto_system_page ()
  end

let view_conditional_jumps () = ()
(*
  let filter = (fun instr -> 
      BCHConditionalJumps.conditional_jumps#has_associated_jump instr#get_address || 
	BCHDisassemblyUtils.is_conditional_jump_instruction instr#get_opcode) in
  begin
    write_to_system_display "ConditionalJumps"
      ((!BCHAssemblyInstructions.assembly_instructions)#toString ~filter ()) ;
    write_message "Displayed conditional jumps" ;
    goto_system_page ()
  end
*)

let view_assignments () = ()
(*
  let numRegisterAssignments = assignment#count_register_assigns in
  let numMemoryAssignments = assignment#count_memory_assigns in
  let numUnknownMemoryAssignments = assignment#count_unknown_memory_assigns in
  let unknownMemoryAssigns = assignment#get_unknown_memory_assigns in
  let unknownMemoryAssignsPP =
    List.fold_left (fun functionsAcc (functionAddress, assigns) ->
      let functionTmpAssignsPP = 
	List.fold_left (fun functionAcc (loc,operand) ->
	  LBLOCK [ functionAcc ; NL ; INDENT (3, LBLOCK [ loc#i#toPretty ; STR "  " ; operand#toPretty ]) ])
	  (functionAddress#toPretty) assigns in
      LBLOCK [ functionsAcc ; NL ; functionTmpAssignsPP ]) (STR "") unknownMemoryAssigns in
  let pp = LBLOCK [
    STR "Number of unknown writes: " ; INT numUnknownMemoryAssignments ; 
    STR " (out of " ; INT numMemoryAssignments ;  STR " memory assignments)" ; NL ; 
    STR "Number of register assignments: " ; INT numRegisterAssignments ; NL ; NL ; unknownMemoryAssignsPP ] in
  begin
    write_message "Collecting assignments ......." ;
    write_to_system_display_pp "Assignments" pp ;
    write_message "Displayed assignments made" ;
    goto_system_page ()
  end
*)

let view_globals () = ()
(*
  let _ = record_memory_accesses () in
  let table = Hashtbl.create 53 in
  let names = new StringCollections.set_t in
  let globalMemrefs = memory_reference_manager#get_global_variable_references in
  let globalMemrefs = 
    List.fold_left (fun a m ->
      if m#get_offset#is_constant_offset then 
	let address = numerical_to_doubleword m#get_offset#get_constant_offset in
	match pe_header#get_containing_section_name address with
	  Some name -> begin names#add name ; (name, address, m) :: a end
	| _ -> a
      else
	a) [] globalMemrefs in
  let _ = List.iter (fun (s,a,m) -> Hashtbl.add table s (a,m)) globalMemrefs in
  let pp_name s = 
    let addresses = Hashtbl.find_all table s in
    let addresses = List.sort (fun (a1,_) (a2,_) -> Pervasives.compare a1#index a2#index) addresses in
    let mempp acc = 
      let loc = get_memory_access_location acc in
      LBLOCK [ loc#toPretty ; STR "   " ; (annotation_table#get loc)#toPretty ] in
    let pp = ref [] in
    let _ = List.iter (fun (a,m) ->
      let readers = memory_accesses#get_readers m in
      let writers = memory_accesses#get_writers m in
      let name = a#to_hex_string in
      pp := [ STR name ; NL ; 
	      INDENT (3, LBLOCK [ STR "readers" ; NL ;
				  INDENT (3, pretty_print_list readers 
				    (fun r -> LBLOCK [ mempp r ; NL ]) "" "" "" ) ] ) ;
	      STR "writers" ; NL ;
	      INDENT (3, pretty_print_list writers
		(fun w -> LBLOCK [ mempp w ; NL ]) "" "" "" ) ; NL ] @ !pp) addresses in
    LBLOCK [ STR "section " ; STR s ; NL ; LBLOCK !pp ; NL ] in
  let names = names#toList in
  let pp = List.fold_left (fun a n -> LBLOCK [ a ; NL ; (pp_name n) ]) (STR "") names in
  begin
    write_to_system_display_pp "GlobalVars" pp ;
    write_message "Displayed global references" ;
    goto_system_page ()
  end
*) 

let view_global_types () = write_message "--- Temporarily unavailable ---"
                         (*
  let table = H.create 3 in
  let add (v:variable_t) t =
    let name = v#getName#getBaseName in
    let entry = if H.mem table name then H.find table name else 
	let s = new BTypeCollections.set_t in begin H.add table name s ; s end in
    entry#add t in      
  let _ = assembly_functions#iter (fun f ->
    let finfo = get_function_info f#get_address in
    let varFacts = finfo#ftinv#get_facts in
    List.iter (fun f ->
      match f#get_fact with
      | VarTypeFact (v,t,_) when finfo#env#is_global_variable v -> add v t
      | ConstTypeFact (c,t) when is_pointer t && c#gt numerical_zero ->
	begin
	  match t with
	  | TPtr (ty,_) -> add (finfo#env#mk_global_variable c) ty
	  | _ -> ()
	end
      | _ -> ()) varFacts) in
  let result = ref [] in
  let _ = H.iter (fun k v -> result := (k,v) :: !result) table in
  let result = List.sort Stdlib.compare !result in
  let pp = List.map (fun (k,v) ->
    LBLOCK [ STR k ; NL ; 
	     INDENT (3, LBLOCK (List.map (fun t -> 
	       LBLOCK [ btype_to_pretty t ; NL ]) v#toList)) ; NL ]) result in
  write_to_system_display_pp "Global_types" 
    (LBLOCK [ STR "Global variable types" ; NL ; NL ; (LBLOCK pp) ]) *)

let view_stats () = write_message "--- Temporarily unavailable ---"
(*
  begin
    write_message "Collecting assembly code statistics ......." ;
    write_to_system_display_pp "Statistics" (get_disassembly_stats ()) ;
    write_message "Displayed assembly code statistics" ;
    goto_system_page ()
  end
*)

let view_analysis_metrics () = ()
(*
  begin
    write_to_system_display_pp "AnalysisMetrics" file_metrics#toPretty ;
    write_message "Displayed analysis metrics" ;
    goto_system_page ()
  end
 *)
let view_orphan_code () = 
  begin
    write_message "Collecting code blocks not used in any function ......." ;
    write_to_system_display "OrphanCode" BCHAssemblyFunctions.assembly_functions#dark_matter_to_string ;
    write_message "Displayed code blocks not used in any function" ;
    goto_system_page ()
  end

let view_missing_summaries () = ()
(*
  let missingFunctions = get_missing_library_functions () in
  let len = List.length missingFunctions in
  let str = "Missing summaries: " ^ (string_of_int len) ^ "\n\n" ^ (String.concat "\n" missingFunctions) in
  begin
    write_to_system_display "MissingSummaries" str ;
    write_message "Displayed missing library function summaries" ;
    goto_system_page ()
  end
*)

let view_unresolved_calls () = ()
(*
  let pp = get_unresolved_calls () in
  begin
    write_to_system_display_pp "UnresolvedCalls" pp ;
    write_message "Displayed unresolved calls" ;
    goto_system_page ()
  end
 *)
(*
let view_jni_calls () =
  let pp = get_jni_calls () in
  begin
    write_to_system_display_pp "JniCalls" pp ;
    write_message "Displayed jni calls" ;
    goto_system_page ()
  end
*)

let view_unprocessed_instructions () = ()
(*
  let pp () = 
  let unprocessedInstructions = BCHTranslateToCHIF.get_unprocessed_instructions () in
    LBLOCK [ STR "Unprocessed instructions: " ; INT (List.length unprocessedInstructions) ; NL ; NL ;
	     pretty_print_list unprocessedInstructions 
		      (fun instr -> LBLOCK [ instr#toPretty ; NL ]) "" "" "" ] in
  begin
    write_message "Collecing unprocessed intructions ......." ;
    write_to_system_display_pp "UnprocessedInstructions" (pp ()) ;
    write_message "Displayed unprocessed instructions" ;
    goto_system_page ()
  end
*)
      
let view_strings () =
  let strings = BCHStrings.string_table#get_strings in
  let strings = List.sort (fun (dw1,_) (dw2,_) -> dw1#compare dw2) strings in
  let pp =
    LBLOCK 
      (List.map
         (fun (address,s) ->
           LBLOCK [STR address#to_hex_string; STR "  "; STR s; NL]) strings) in
  begin
    write_message "Collecing strings ......." ;
    write_to_system_display_pp "Strings" pp ;
    write_message "Displayed strings" ;
    goto_system_page ()
  end

let view_wide_strings () = ()

let view_user_provided_facts () = ()
(*
  begin
    write_message "Retrieving user-provided application facts ....... " ;
    write_to_system_display_pp "UserProvidedFacts" user_provided_application_facts#toPretty ;
    write_message "Displayed user-provided application facts" ;
    goto_system_page ()
  end
*)
let view_log () = 
  begin
    write_message "Retrieving log ....... " ;
    write_to_system_display_pp "CHLog" CHLogger.chlog#toPretty ;
    write_message "Displayed log" ;
    goto_system_page ()
  end

let view_error_log ():unit = 
  begin
    write_message "Retrieving error log ....... " ;
    write_to_system_display_pp "CHErrorLog" CHLogger.ch_error_log#toPretty ;
    write_message "Displayed error log" ;
    goto_system_page ()
  end

let load_function_entry () =
  let faddr = system_info#get_address_of_entry_point in
  if add_function_listed faddr#to_hex_string then
    begin
      translate_assembly_function_by_address faddr ;
      record_cfg_info faddr ;
      functions_display#set_model 
	(List.map (fun a -> 
	     assembly_functions#get_function_by_address
               (TR.tget_ok (string_to_doubleword a)))
	   (get_functions_listed ()));
      write_message_pp 
	(LBLOCK [STR "Added function entry point: "; STR faddr#to_hex_string])
    end
  else
    write_message_pp 
      (LBLOCK [
           STR "Function entry point ";
           STR faddr#to_hex_string;
	   STR " is already included in the list of functions "])

let prepare_fn (faddr:doubleword_int) =
  try
    begin
      translate_assembly_function_by_address faddr ;
      record_cfg_info faddr 
    end
  with 
  | BCH_failure p ->
    begin
      write_message_pp 
	(LBLOCK [
             STR "Error in translation of "; faddr#toPretty; STR ": "; p]);
      ch_error_log#add "translation error"
	(LBLOCK [faddr#toPretty; STR ": "; p])
    end
  | Internal_error s | Invocation_error s ->
    begin
      write_message ("Internal error in translation of " ^ faddr#to_hex_string)
    end

let add_fn a = 
  let s = a#to_hex_string in
  if has_function_listed s then
    begin
      write_message_pp
        (LBLOCK [STR "Function "; STR s; STR " is already listed "]);
    end
  else
    try
      let faddr = TR.tget_ok (string_to_doubleword s) in
      let _ = add_function_listed s in
      begin
	translate_assembly_function_by_address faddr;
	record_cfg_info faddr ;
	functions_display#set_model 
	  (List.map (fun a -> 
	       assembly_functions#get_function_by_address
                 (TR.tget_ok (string_to_doubleword a)))
	     (get_functions_listed ()));
	write_message_pp (LBLOCK [STR "Added function: "; STR s]);
      end
    with
      BCH_failure p -> 
	begin
	  write_message_pp
            (LBLOCK [
                 STR "Error in loading function "; STR s; STR ": "; p]);
	end

let add_fns (l:doubleword_int list) =
  let l = List.filter (fun a -> not (has_function_listed a#to_hex_string)) l in
  let len = List.length l in
  if len > 0 then
    let completed = ref 0 in
    let _ = List.iter (fun faddr ->
      begin
	ignore (add_function_listed faddr#to_hex_string) ;
	prepare_fn faddr ;
	completed := !completed + 1 ;
	set_progress_bar !completed len ;
      end ) l in
    begin
      functions_display#set_model
        (List.map (fun a ->
	     get_assembly_function
               (TR.tget_ok (string_to_doubleword  a)))
           (get_functions_listed ()));
      write_message_pp (LBLOCK [STR "Added "; INT len; STR " functions"]);
      reset_progress_bar () 
    end
  else
    write_message_pp (LBLOCK [STR "No new functions to be added"])

let load_function_by_address () = 
  let add_fn s = 
    if has_function_listed s then
      begin
	write_message_pp
          (LBLOCK [STR "Function "; STR s; STR " is already listed "]);
	None
      end
    else
      try
	let faddr = TR.tget_ok (string_to_doubleword s) in
	let _ = add_function_listed s in
	begin
	  translate_assembly_function_by_address faddr;
	  record_cfg_info faddr ;
	  functions_display#set_model 
	    (List.map (fun a -> 
	         assembly_functions#get_function_by_address
                   (TR.tget_ok (string_to_doubleword a)))
	       (get_functions_listed ()));
	  write_message_pp (LBLOCK [STR "Added function: "; STR s]);
	  None
	end
      with
	BCH_failure p -> 
	  begin
	    write_message_pp
              (LBLOCK [
                   STR "Error in loading function "; STR s; STR ": "; p]);
	    None
	  end in
  let _ = data1_entry_dialog ~height:100 ~width:300
    ~title:"Enter function address" ~label:"Function address: "
    ~action:add_fn ~parent:window in
  ()

let show_library_callers () = ()
(*
  let action s = 
    let flocs = get_lib_calls s in
    match flocs with
    | [] -> begin write_message ("No library calls to " ^ s ^ " found") ; None end
    | _ -> 
      let len = List.length flocs in
      begin 
	show_lib_callers_dialog ("Calls to " ^ s ^ " (" ^ (string_of_int len) ^ ")") 
	  flocs add_fns window ; 
	None 
      end in
  let _ = data1_entry_dialog ~height:100 ~width:300
    ~title:"Enter name of library function" ~label:"Function name: "
    ~action ~parent:window in
  ()
 *)
let show_jni_callers () = ()
(*
  let flocs = get_jni_calls () in
  match flocs with
  | [] -> write_message_pp (STR "No jni callbacks found")
  | _ -> show_lib_callers_dialog "Calls to jni functions" flocs add_fns window
 *)
let show_external_inputters () = ()
(*
  let flocs = get_external_input_calls () in
  match flocs with
  | [] -> write_message "No calls to functions with external inputs found"
  | _ ->
    show_external_effects_dialog "Calls to functions with external inputs" 
      flocs add_fns window
*)

let show_external_effecters () = ()
(*
  let flocs = get_external_effects () in
  match flocs with
  | [] -> write_message "No calls to functions with external effects found"
  | _ ->
    show_external_effects_dialog "Calls to functions with external effects" 
      flocs add_fns window
*)

let load_all_functions () =
  let fns = assembly_functions#get_application_functions in
  let count = List.length fns in
  let load_functions () = 
    let completed = ref 0 in
    begin
      set_functions_listed (List.map (fun f -> f#get_address#to_hex_string) fns);
      write_message_pp
        (LBLOCK [
             STR "Initializing function list with ";
	     INT count;
             STR " functions ....... " ]);
      functions_display#set_model fns;
      write_message_pp
        (LBLOCK [
             STR "Translating ";
             INT count;
	     STR " functions ......." ]);
      List.iter (fun faddr ->
	begin
	  prepare_fn faddr ;
	  completed := !completed + 1;
	  set_progress_bar !completed count
	end)  (List.map (fun f -> f#get_address) fns);
      write_message_pp
        (LBLOCK [
             STR "Loaded and translated "; INT count; STR " functions"]);
      reset_progress_bar ()
    end in
  if count > 500 then
    let _ = confirmation_dialog
      ~title:"Confirm loading all functions"
      ~label:("There are "
              ^ (string_of_int count)
              ^ " functions.\nLoading them all may take some time. "
              ^ " \nDo you want to proceed? ")
      ~yes_action:load_functions 
      ~no_action:(fun () -> ())
      ~parent:window in
    ()
  else
    load_functions ()
      
let clear_functions () = 
  let len = List.length (get_functions_listed ()) in 
  let cf () =
    begin
      clear_functions_listed () ;
      functions_display#set_model [] ;
      write_message_pp (STR "Removed all functions listed")
    end in
  if len = 0 then
    write_message "No functions to remove"
  else
    let _ = confirmation_dialog
      ~title:"Confirm removing all functions"
      ~label:("Are you sure you want to remove all \n" ^
		 (string_of_int len) ^ " functions?")
      ~yes_action:cf
      ~no_action:(fun () -> ())
      ~parent:window in
    ()

let annotate_function_address () =
  let action = fun address_string function_name ->
    let optAddress =
      try
        Some (TR.tget_ok (string_to_doubleword address_string))
      with
      | _ -> None in
    match optAddress with
      None -> Some "Address is not a valid hexadecimal number"
    | Some address ->
      if assembly_functions#has_function_by_address address then
	begin
	  write_message
            ("Address "
             ^ address_string
             ^ " has been associated with name "
             ^ function_name);
	  None
	end 
      else
        Some "Address is not the address of an existing function" in
  data_entry_dialog ~title:"Associate addres with function name"
    ~label_1: "Address (in hexadecimal):"
    ~label_2: "Function name:"
    ~action
    ~parent:window

(*
let annotate_jni_offset () = 
  let action = fun offset_string method_name ->
    let optOffset = try Some (string_to_doubleword offset_string) with _ -> None in
    match optOffset with
      None -> Some "Offset should be expressed as a hexadecimal number"
    | Some offset ->
	begin
	  write_message ("JNI offset " ^ offset_string ^ " has been associated with " ^ method_name) ;
	  None
	end in
  data_entry_dialog ~title:"Associate offset with JNI method name"
    ~label_1: "Offset (in hexadecimal):"
    ~label_2: "Method name:"
    ~action
    ~parent:window

let redo_disassembly () =
  begin 
    disassemble () ;
    construct_functions () ;
  end

let refresh_function_list () = 
  begin
    write_message "Updating the list of functions to incorporate new names ......." ;
    functions_display#set_model assembly_functions#get_application_functions ;
    write_message "Updated the list of functions with new names"
  end

*)

let show_call_graph () = 
  begin
    write_message "Constructing system call graph ......." ;
    canvas#call_graph_to_dot ;
    write_message "Displayed system call graph on canvas" 
  end

let show_orphan_code_graph () = 
  begin
    write_message "Collecting orphan code and constructing graph ....... " ;
    canvas#orphan_code_to_dot ;
    write_message "Displayed orphan code graph on canvas"
  end

let show_function_time_out () =
  let action s =
    try
      (* let f = float_of_string s in *)
      begin 
	(* time_out#set_value f ;  *)
	write_message ("Function time-out value was changed to " ^ s) ;
	None 
      end
    with
      Failure f -> Some ("Error in input: " ^ f) in
  data1_entry_dialog ~height:100 ~width:300 ~title:"Enter time-out value" ~label:"Time-out value (msec)" ~action ~parent:window

(* ----------------------------------------~------------------- main menu bar -- *)
let set_menu () =
  let create_menu label =
    let item = GMenu.menu_item ~label:label ~packing:menubar#append () in
    GMenu.menu ~packing:item#set_submenu () in
  let codehawk_menu = create_menu "CodeHawk" in
  let file_menu  = create_menu "File" in
  let pe_menu = create_menu "PE" in
(*  let elf_menu = create_menu "ELF" in *)
  let view_menu  = create_menu "View" in
  let fns_menu = create_menu "Functions" in
  (* let annotate_menu = create_menu "Annotate" in *)
  let graph_menu = create_menu "Graph" in
  let settings_menu = create_menu "Settings" in

  let codehawk_entries = [
    `I ("About", about_codehawk) ;
    `I ("Quit", quit_analyzer)
  ] in
  let _ = GToolbox.build_menu codehawk_menu ~entries:codehawk_entries in

  let file_entries = [
    `I ("Open", open_file_dialog) ;
    `I ("Save system display", save_system_display_contents) ;
    `I ("Save user data", save_user_data) ;
    `I ("Save chif", save_chif) ;
    `I ("Save session", save_session) ; 
    `I ("Save variable types", save_variable_types) ;
    `I ("Save variables", save_variables) ;
    `I ("Save memory references", save_memory_references );
    `I ("Reset log", reset_log) 
  ] in
  let _ = GToolbox.build_menu file_menu ~entries:file_entries in
  
  let pe_entries = [
    `I ("PE header", view_pe_header) ;
    `I ("Data directory", view_data_directory) ;
    `I ("Section headers", view_section_headers) ;
    `I ("Export table", view_export_table) ;
    `I ("Import tables", view_import_tables) ;
    `I ("Load configuration directory", view_load_configuration_directory) ;
    `I ("Resource table", view_resource_table) ;
    `I ("Table layout", view_table_layout) ;
    `S ;
    `I ("Raw sections", view_raw_sections) ;
  ] in
  let _ = GToolbox.build_menu pe_menu ~entries:pe_entries in
 
(* 
  let elf_entries = [
    `I ("Header", view_elf_header) ;
    `I ("Section Headers", view_elf_section_headers);
    `I ("Symbol Table", view_elf_symbol_table);
    `I ("Dynamic Symbol Table", view_elf_dynamic_symbol_table);
    `I ("PLT Relocation Table", view_elf_plt_relocation_table);
    `I ("Dynamic Relocation Table", view_elf_dynamic_relocation_table);
  ] in
  let _ = GToolbox.build_menu elf_menu ~entries:elf_entries in  
*)
 
  let view_entries = [
    `I ("Raw assembly code", view_raw_assembly) ;
    `I ("Data blocks", view_data_blocks) ;
    `I ("Call instructions", view_call_instructions) ;
    `I ("Indirect calls", view_indirect_calls) ; 
    `I ("Indirect jumps", view_indirect_jumps) ;
    `I ("Conditional jumps", view_conditional_jumps) ;
    `I ("Assignments", view_assignments) ;
    `I ("Global variable types", view_global_types) ;
    `S ;
    `I ("Disassembly Statistics", view_stats ) ;
    `I ("Analysis Metrics", view_analysis_metrics ) ;
    `I ("Orphan code", view_orphan_code) ;
    `I ("Unprocessed instructions", view_unprocessed_instructions) ;
    `I ("Unresolved calls", view_unresolved_calls) ;
    `I ("Missing summaries", view_missing_summaries) ;
    `S ;
    `I ("Strings", view_strings ) ;
    `S ;
    `I ("User-provided facts", view_user_provided_facts) ;
    `S ;
    `I ("Log", view_log) ;
    `I ("Error log", view_error_log) 
  ] in
  let _ = GToolbox.build_menu view_menu ~entries:view_entries in

  let fns_entries = [
    `I ("Load all", load_all_functions) ;
    `I ("Load entry point", load_function_entry) ;
    `I ("Load by address", load_function_by_address) ;
    `S ;
    `I ("Clear", clear_functions) ;
    `S ;
    `I ("with library calls", show_library_callers) ;
    `I ("with JNI calls", show_jni_callers) ;
    `I ("with external inputs", show_external_inputters) ;
    `I ("with external effects", show_external_effecters)
  ] in 
  let _ = GToolbox.build_menu fns_menu ~entries:fns_entries in
(*  
  let annotate_entries = [
    `I ("Function address", annotate_function_address) ;
    `I ("Redo disassembly", redo_disassembly) ;
    `I ("JNI offset", annotate_jni_offset) ;
    `S ;
    `I ("Refresh function list", refresh_function_list )        
  ] in
  let _ = GToolbox.build_menu annotate_menu ~entries:annotate_entries in *)

  let graph_entries = [
    `I ("Call graph", show_call_graph) ;
    `S ;
    `I ("Orphan code", show_orphan_code_graph) ;
  ] in
  let _ = GToolbox.build_menu graph_menu ~entries:graph_entries in

  let settings_entries = [
    `I ("Function time-out", show_function_time_out)
  ] in
  let _ = GToolbox.build_menu settings_menu ~entries:settings_entries in

  ()


let run_gui () =
  let _ = window#event#connect#delete ~callback:delete_event in
  let _ = window#connect#destroy ~callback:destroy in
  let filename = system_info#get_filename in
  begin 
    set_menu () ; 
    window#show () ; 
    (if filename = "" then
      write_message "Please load a file using Open"
     else
	begin
	  write_message ("File " ^ filename ^ " selected for analysis") ;
	  match load_pe_header_file () with
	  | Some node ->
	    let _ = pe_header#read_xml node in
	    let (success,msg) = disassemble_pe () in
	    if success then
	      let _ = pr_debug [ msg ] in
	      construct_functions ()
	  | _ -> write_message ("No xml file found with pe-header for " ^ filename)
	end) ;
    GMain.Main.main () 
  end
  

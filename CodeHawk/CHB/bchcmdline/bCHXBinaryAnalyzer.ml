(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
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

(* chutil *)
open CHFileIO
open CHGc
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDisassemblySummary
open BCHDoubleword
open BCHGlobalState
open BCHMetrics
open BCHPreFileIO
open BCHSpecializations
open BCHSystemInfo
open BCHSystemSettings
open BCHXmlUtil

(* bchlibpe *)
open BCHPESections
open BCHPEHeader

(* bchlibelf *)
open BCHELFHeader

(* bchlibx86 *)
open BCHAssemblyFunctions
open BCHDisassemble
open BCHDisassembleELF
open BCHDisassembleStream
open BCHIFSystem
open BCHLoopStructure
open BCHPredefinedCallSemantics
open BCHTranslateToCHIF
open BCHX86AnalysisResults
   
(* bchlibmips32 *)
open BCHDisassembleMIPS
open BCHMIPSAnalysisResults
open BCHMIPSAssemblyFunctions   
open BCHMIPSAssemblyInstructions

(* bchlibarm32 *)
open BCHARMAnalysisResults
open BCHARMAssemblyFunctions
open BCHDisassembleARM

(* bchanalyze *)
open BCHAnalysisTypes
open BCHAnalyzeApp
open BCHFileIO
open BCHSaveExports

(* bchcmdline *)
open BCHVersion

(* -------------------------------------------------------------------------
 * Command-line switches:
 * - set_vftables: for all jump tables, if one of the targets is a function entry
 *       then declare all targets to be function entry points, if enabled
 *       default setting: disabled
 *)

let cmd = ref "version"
let export_directory = ref ""
let savecfgs = ref false
let save_xml = ref false  (* save disassembly status in xml *)
let save_asm = ref false

let architecture = ref "x86"
let fileformat = ref "pe"

let stream_start_address = ref wordzero
let set_stream_start_address s =
  stream_start_address := string_to_doubleword s

let show_chif = ref None
let set_chif s = show_chif := Some s

let speclist =
  [ ("-version", Arg.Unit (fun () -> ()), "show version information and exit") ;
    ("-gc", Arg.Unit (fun () -> cmd := "gc"), 
     "show ocaml garbage collector settings and exit") ;
    ("-set_vftables",Arg.Unit  (fun () -> system_settings#set_vftables),
     "declare jumptable targets as funcion entry points") ;
    ("-extracthex", Arg.Unit (fun () -> cmd := "extracthex"),
     "extract executable content from lisphex encoded executable") ;
    ("-stream", Arg.Unit (fun () -> cmd := "stream"),
     "stream disassemble a hex-encoded stream of bytes") ;
    ("-startaddress",  Arg.String set_stream_start_address,
     "start address of the code stream") ;
    ("-arm", Arg.Unit (fun () -> architecture := "arm"), "arm executable");
    ("-thumb", Arg.Unit (fun () -> system_settings#set_thumb),
     "arm executable includes thumb instructions");
    ("-mips", Arg.Unit (fun () -> architecture := "mips"), "mips executable");
    ("-elf", Arg.Unit (fun () -> fileformat := "elf"), "ELF executable");
    ("-extract", Arg.Unit (fun () -> cmd := "extract"),
     "extract executable content from executable and save in xml format");
    ("-xsize", Arg.Int system_info#set_xfilesize,
     "size of the executable in bytes");
    ("-dump", Arg.Unit (fun () -> cmd := "dump"),
     "dump entire executable to xml (max size 1MB)");
    ("-disassemble", Arg.Unit (fun () -> cmd := "disassemble"),
     "save an assembly listing of the executable in text format") ;
    ("-analyze", Arg.Unit (fun () -> cmd := "analyze"),
     "analyze the executable and save intermediate results in xml format (applicable to xml rep only)") ;
    ("-ignore_stable", Arg.Unit (fun () -> BCHAnalyzeApp.analyze_all := true),
     "continue analyzing functions that have stabilized");
    ("-no_lineq", Arg.String (fun s -> add_no_lineq s),
     "do not apply linear equality analysis to this function");
    ("-preamble_cutoff", Arg.Int system_info#set_preamble_cutoff,
     "minimum number of preamble instructions observed to add as function entry point");
    ("-save_cfgs", Arg.Unit (fun () -> savecfgs := true),
     "save basic blocks and loops (applicable to .exe file)") ;
    ("-summaries", Arg.String system_settings#set_summary_jar,
     "path to the jar that holds the library function summaries");
    ("-so_library", Arg.String system_settings#add_so_library,
     "name of a library with shared objects to be searched for summaries");
    ("-appsdir", Arg.String system_settings#set_apps_dir,
     "directory that holds application-dependent summaries") ;
    ("-save_exports", Arg.Unit (fun () -> cmd := "saveexports"),
     "save function summary of exported functions in named directory")  ;
    ("-verbose", Arg.Unit (fun () -> system_settings#set_verbose),
     "print out analysis intermediate results and progress messages") ;
    ("-show_chif", Arg.String (fun s -> set_chif s),
     "print out CHIF code");
    ("-save_disassembly_status_in_xml", Arg.Unit (fun () -> save_xml := true),
     "save disassembly status in xml for bulk evaluation");
    ("-save_asm", Arg.Unit (fun () -> save_asm := true),
     "save assembly listing in the analysis directory");
    ("-specialization", Arg.String specializations#activate_specialization,
     "apply named specialization")
  ]

let usage_msg = "chx86_analyze <options> <name of executable file>"
let read_args () = Arg.parse speclist system_info#set_filename usage_msg

let exit_with_error cmd msg =
  begin
    pr_debug [ msg ] ;
    save_log_files cmd ;
    exit 1
  end

let function_stats_to_pretty l =
  let (smallentries,largeentries) = l in
  let flp = fixed_length_pretty in
  let psmall =
    LBLOCK (List.map (fun (flen,count) ->
                LBLOCK [ flp ~alignment:StrRight (LBLOCK [ STR "< " ; INT flen ]) 8 ;
                         STR " instrs: " ; INT count ; NL ]) smallentries) in
  let dlarge =
    List.map (fun f ->
        try
          let _ = translate_assembly_function f in
          (f#get_address,
           f#get_instruction_count,
           f#get_block_count,
           get_cfg_loop_complexity f)
        with
        | BCH_failure p ->
           begin
             ch_error_log#add "translation"
                              (LBLOCK [ f#get_address#toPretty ; STR "; " ; p ]) ;
             (f#get_address,0,0,0)
           end) largeentries in
  let dlarge = List.sort (fun (_,l1,_,_) (_,l2,_,_) -> Stdlib.compare l1 l2) dlarge in
  let plarge =
    LBLOCK (List.map (fun (faddr,flen,fblocks,fcompl) ->
                LBLOCK [ flp faddr#toPretty 10 ; STR "  " ;
                         flp ~alignment:StrRight (INT flen) 12 ; STR "  " ;
                         flp ~alignment:StrRight (INT fblocks) 12 ; STR "  " ;
                         flp ~alignment:StrRight (INT fcompl) 12 ; NL ]) dlarge) in
  let ptitle = LBLOCK [ flp (STR "address") 10 ; STR "       " ;
                        flp (STR "instructions") 12 ; STR "  " ;
                        flp ~alignment:StrCenter (STR "blocks")  12 ; STR "  " ;
                        flp ~alignment:StrCenter (STR "complexity")  12  ; STR "  " ; NL ]  in
  let pplarge = if List.length largeentries > 0 then
                  LBLOCK [ STR "Large functions" ; NL ; ptitle ;
                           STR (string_repeat "-" 80) ; NL ; plarge ; 
                           STR (string_repeat "-" 80) ; NL ]
                else
                  STR "" in
  LBLOCK [ STR "Small functions" ; NL ; STR (string_repeat "-" 80) ; NL ; psmall ; NL ;
           pplarge ]
              

let get_dll_functions () =
  if pe_sections#has_import_directory_table then
    let table = pe_sections#get_import_directory_table in
    List.iter (fun e ->
        begin
          pr_debug [ STR e#get_name ; NL ] ;
          List.iter (fun f ->
              pr_debug [ STR "   " ; STR f ; NL ] ) e#get_functions ;
          pr_debug [ NL ]
        end) table
  

let main () =
  try
    let _ = read_args () in
    let _ = chlog#set_max_entry_size 1000 in
    if !cmd = "version" then
      begin
	pr_debug [ version#toPretty ; NL ] ;
	exit 0
      end
	
    else if !cmd = "gc" then
      begin
	pr_debug [ garbage_collector_settings_to_pretty () ; NL ] ;
	exit 0
      end

    else if !cmd = "stream" then
      let codestring = read_hex_stream_file system_info#get_filename in
      begin
        disassemble_stream !stream_start_address codestring ;
        pr_debug
	  [ STR ((!BCHAssemblyInstructions.assembly_instructions)#toString ()) ]
      end

    else if !cmd = "extracthex" then
      let _ = register_hashed_functions () in
      let (success,msg) = read_hexlified_pe_file system_info#get_filename in
      if success then
        begin
          pverbose [ msg ; NL ] ;
          save_pe_files () ;
          save_log_files "extracthex" ;
          exit 0
        end
      else
        exit_with_error !cmd msg
	
    else if !cmd = "extract" && !architecture = "x86" && !fileformat = "pe" then
      let _ = register_hashed_functions () in
      let (success,msg) = read_pe_file system_info#get_filename version#get_maxfilesize in
      if success then
	begin
	  pverbose [ msg ; NL ] ;
	  save_pe_files () ;
	  save_log_files "extract" ;
	  exit 0
	end
      else 
	exit_with_error !cmd msg

    else if !cmd = "extract" && !fileformat = "elf" then
      let _ = if !architecture = "mips" then system_info#set_mips in
      let _ = if !architecture = "arm" then system_info#set_arm in
      let _ = system_info#initialize in
      let (success, msg) =
        read_elf_file system_info#get_filename system_info#get_xfilesize in
      if success then
        begin
          pverbose [ msg ; NL ] ;
          save_elf_files () ;
          save_log_files "extract" ;
          exit 0
        end
      else
        exit_with_error !cmd msg

    else if !cmd = "dump" then
      dump_pe_file system_info#get_filename

    else if !cmd = "disassemble" && !architecture = "x86" && !fileformat = "pe" then
      let _ = register_hashed_functions () in
      let t = ref (Unix.gettimeofday ()) in
      let _ = system_info#initialize in
      let _ = load_pe_files () in
      let (success, msg) = disassemble_pe () in
      if success then
	let _ = disassembly_summary#record_disassembly_time ((Unix.gettimeofday ()) -. !t) in
        let _ = pverbose [ msg ] in
	let t = ref (Unix.gettimeofday ()) in
	let (success,msg) = construct_functions_pe () in
	if success then
	  let _ = disassembly_summary#record_construct_functions_time 
	            ((Unix.gettimeofday ()) -. !t) in
          if !save_xml then
            begin
              save_disassembly_status () ;
              exit 0
            end          
          else
            let _ = disassembly_summary#set_disassembly_metrics (get_disassembly_metrics ()) in
	    let _ = pr_debug [ disassembly_summary#toPretty ; NL ] in
            let _ = pr_debug [ function_stats_to_pretty
                                 assembly_functions#get_function_stats ] in
	    let _ = pr_debug [ msg ] in
	    begin
	      file_output#saveFile
                (get_asm_listing_filename ())
	        (STR ((!BCHAssemblyInstructions.assembly_instructions)#toString ())) ;
	      file_output#saveFile
                (get_orphan_code_listing_filename ())
	        (STR ((BCHAssemblyFunctions.assembly_functions#dark_matter_to_string))) ;
              file_output#saveFile
                (get_duplicate_coverage_filename ())
                (STR (BCHAssemblyFunctions.assembly_functions#duplicates_to_string)) ;
              save_log_files !cmd ;
	      exit 0
	    end
	else
	    exit_with_error !cmd msg
      else
	exit_with_error !cmd msg

    else if !cmd = "disassemble" && !architecture = "x86" && !fileformat = "elf" then
      let _ = system_info#set_elf in
      let _ = load_bdictionary () in      
      let _ = system_info#initialize in
      let t = ref (Unix.gettimeofday ()) in
      let _ = pr_debug [ STR "Load elf files ... " ; NL ] in
      let _ = load_elf_files () in
      let _ = pr_debug [ STR "disassemble sections ... " ; NL ] in
      let _ = disassemble_elf_sections ()  in
      let _ = disassembly_summary#record_disassembly_time
                ((Unix.gettimeofday ()) -. !t) in
      let t = ref (Unix.gettimeofday ()) in
      let _ = construct_functions_elf () in
      let _ = disassembly_summary#record_construct_functions_time
                ((Unix.gettimeofday ()) -. !t) in
      let _ = disassembly_summary#set_disassembly_metrics (get_disassembly_metrics ()) in      
      let _ =  pr_debug [ disassembly_summary#toPretty ; NL ] in
      begin
        file_output#saveFile
          (get_asm_listing_filename ())
          (STR ((!BCHAssemblyInstructions.assembly_instructions)#toString ())) ;
	file_output#saveFile
          (get_orphan_code_listing_filename ())
	  (STR ((BCHAssemblyFunctions.assembly_functions#dark_matter_to_string))) ;
        file_output#saveFile
          (get_duplicate_coverage_filename ())
          (STR (BCHAssemblyFunctions.assembly_functions#duplicates_to_string)) ;
          save_log_files "disassemble" 
      end

    else if !cmd = "disassemble" && !architecture = "mips" && !fileformat = "elf" then
      let _ = system_info#set_elf in
      let _ = system_info#set_mips in
      let _ = system_info#initialize in
      let t = ref (Unix.gettimeofday ()) in
      let _ = pr_debug [ STR "Load MIPS file ..." ; NL ] in
      let _ = load_elf_files () in
      let _ = pr_debug [ STR "disassemble sections ... " ; NL ] in
      let _ = disassemble_mips_sections ()  in
      let _ = disassembly_summary#record_disassembly_time
                ((Unix.gettimeofday ()) -. !t) in
      let t = ref (Unix.gettimeofday ()) in
      let _ = construct_functions_mips () in
      let _ = mips_assembly_functions#inline_blocks in
      let _ = disassembly_summary#record_construct_functions_time
                ((Unix.gettimeofday ()) -. !t) in
      let _ = disassembly_summary#set_disassembly_metrics (get_mips_disassembly_metrics ()) in      
      let _ = pr_debug [ disassembly_summary#toPretty ; NL ] in
      begin
        file_output#saveFile
          (get_asm_listing_filename ())
          (STR ((!BCHMIPSAssemblyInstructions.mips_assembly_instructions)#toString ()));
	file_output#saveFile
          (get_orphan_code_listing_filename ())
	  (STR ((BCHMIPSAssemblyFunctions.mips_assembly_functions#dark_matter_to_string)));
        save_mips_assembly_instructions ();
	save_system_info ();
        save_mips_dictionary ();
        save_interface_dictionary ();
        save_bdictionary ();
        save_log_files "disassemble";
      end

    else if !cmd = "disassemble" && !architecture = "arm" && !fileformat = "elf" then
      let _ = system_info#set_elf in
      let _ = system_info#set_arm in
      let _ = system_info#initialize in
      let t = ref (Unix.gettimeofday ()) in
      let _ = pr_debug [ STR "Load ARM file ..." ; NL ] in
      let _ = load_elf_files () in
      let _ = pr_debug [ STR "disassemble sections ..." ; NL ] in
      let _ = disassemble_arm_sections () in
      let _ = disassembly_summary#record_disassembly_time
                ((Unix.gettimeofday ()) -. !t) in
      let _ = construct_functions_arm() in
      let _ = disassembly_summary#record_construct_functions_time
                ((Unix.gettimeofday ()) -. !t) in
      let _ = disassembly_summary#set_disassembly_metrics
                (get_arm_disassembly_metrics ()) in
      let _ =  pr_debug [ NL; NL; disassembly_summary#toPretty ; NL ] in
      begin
        if !save_asm then
          begin
            file_output#saveFile
              (get_asm_listing_filename ())
              (STR ((!BCHARMAssemblyInstructions.arm_assembly_instructions)#toString ()));
	    file_output#saveFile
              (get_orphan_code_listing_filename ())
	      (STR ((BCHARMAssemblyFunctions.arm_assembly_functions#dark_matter_to_string)));
            file_output#saveFile
              (get_duplicate_coverage_filename ())
              (STR (BCHARMAssemblyFunctions.arm_assembly_functions#duplicates_to_string));
            save_arm_assembly_instructions ();
            save_system_info ();
            save_arm_dictionary ();
            save_interface_dictionary ();
            save_bdictionary ()
          end;
        save_log_files "disassemble"
      end
                

    else if !cmd = "analyze" && !architecture = "x86" && !fileformat = "pe" then
      let _ = register_hashed_functions () in
      let starttime = Unix.gettimeofday () in
      let _ = load_bdictionary () in
      let _ = system_info#initialize in
      let _ = load_interface_dictionary () in      
      let _ = load_x86dictionary () in
      let _ = global_system_state#initialize in
      let _ = file_metrics#load_xml in
      let _ = pverbose [ STR "Load pe files ... " ; NL ] in
      let _ = load_pe_files () in
      let index = file_metrics#get_index in
      let logcmd = "analyze_" ^ (string_of_int index) in
      let _ = pverbose [ STR "Start disassembly ... " ; NL ] in
      let (success,msg) = disassemble_pe () in
      if success then
	let _ = pverbose [ msg ] in
	let (success,msg) = construct_functions_pe () in
	if success then
	  let _ = pverbose [ msg ] in
	  let _ = analyze starttime in
          let _ = file_metrics#set_disassembly_results (get_disassembly_metrics ()) in
	  begin
	    save_functions_list ();
	    save_file_results ();
	    save_global_state ();
            x86_analysis_results#save;
            save_x86dictionary ();
	    save_system_info ();
            save_interface_dictionary ();
            save_bdictionary ();
	    save_log_files logcmd;
	    (if !save_asm then
              begin
	        file_output#saveFile
                  (get_asm_listing_filename ())
	          (STR ((!BCHAssemblyInstructions.assembly_instructions)#toString ()));
	        file_output#saveFile
                  (get_orphan_code_listing_filename ())
	          (STR ((BCHAssemblyFunctions.assembly_functions#dark_matter_to_string)));
                file_output#saveFile
                  (get_duplicate_coverage_filename ())
                  (STR (BCHAssemblyFunctions.assembly_functions#duplicates_to_string));
                save_log_files !cmd;
	      end);
            exit 0
	  end
	else
	  exit_with_error logcmd msg
      else
	exit_with_error logcmd msg	    
      
    else if !cmd = "analyze" && !architecture = "x86" && !fileformat = "elf" then
      let _ = register_hashed_elf_functions () in
      let starttime = Unix.gettimeofday () in
      let _ = system_info#set_elf in
      let _ = load_bdictionary () in
      let _ = system_info#initialize in      
      let _ = load_interface_dictionary () in
      let _ = load_x86dictionary () in
      let _ = global_system_state#initialize in
      let _ = file_metrics#load_xml in
      let _ = load_elf_files ()  in
      let index = file_metrics#get_index in
      let logcmd = "analyze_"  ^  (string_of_int index) in
      let _ = disassemble_elf_sections () in
      let _ = construct_functions_elf () in
      let _ = analyze starttime in
      let _ = file_metrics#set_disassembly_results (get_disassembly_metrics ()) in      
      begin
	save_functions_list ();
	save_system_info ();
	save_file_results ();
	save_global_state ();
        x86_analysis_results#save;
        save_x86dictionary ();
        save_interface_dictionary ();
        save_bdictionary ();
	save_log_files logcmd;
	exit 0
      end

    else if !cmd = "analyze" && !architecture = "mips" && !fileformat="elf" then
      let starttime = Unix.gettimeofday () in
      let _ = system_info#set_elf in
      let _ = system_info#set_mips in
      let _ = load_bdictionary () in
      let _ = system_info#initialize in
      let _ = load_interface_dictionary () in
      let _ = load_mips_dictionary () in
      let _ = global_system_state#initialize in
      let _ = file_metrics#load_xml in
      let _ = load_elf_files () in
      let index = file_metrics#get_index in
      let logcmd = "analyze_" ^ (string_of_int index) in
      let _ = disassemble_mips_sections () in
      let _ = construct_functions_mips () in
      let _ = mips_assembly_functions#inline_blocks in
      let _ = analyze_mips starttime in
      let _ = file_metrics#set_disassembly_results (get_mips_disassembly_metrics ()) in      
      begin
	save_functions_list ();
	save_system_info ();
	save_file_results ();
	save_global_state ();
        mips_analysis_results#save;
        save_mips_assembly_instructions ();
        save_mips_dictionary ();
        save_interface_dictionary ();
        save_bdictionary ();
        (file_output#saveFile
           (get_asm_listing_filename ())
           (STR ((!BCHMIPSAssemblyInstructions.mips_assembly_instructions)#toString ())));
	file_output#saveFile
          (get_orphan_code_listing_filename ())
	  (STR ((BCHMIPSAssemblyFunctions.mips_assembly_functions#dark_matter_to_string)));
	save_log_files logcmd;
	exit 0
      end

    else if !cmd = "analyze" && !architecture = "arm" && !fileformat = "elf" then
      let starttime = Unix.gettimeofday () in
      let _ = system_info#set_elf in
      let _ = system_info#set_arm in
      let _ = load_bdictionary () in
      let _ = system_info#initialize in
      let _ = load_interface_dictionary () in
      let _ = load_arm_dictionary () in
      let _ = global_system_state#initialize in
      let _ = file_metrics#load_xml in
      let _ = load_elf_files () in
      let index = file_metrics#get_index in
      let logcmd = "analyze_" ^ (string_of_int index) in
      let _ = disassemble_arm_sections () in
      let _ = construct_functions_arm () in
      let _ = analyze_arm starttime in
      let _ = file_metrics#set_disassembly_results (get_arm_disassembly_metrics ()) in
      begin
        save_functions_list ();
        save_system_info ();
        save_file_results ();
        save_global_state ();
        arm_analysis_results#save;
        save_arm_assembly_instructions ();
        save_arm_dictionary ();
        save_interface_dictionary ();
        save_bdictionary ();
        (file_output#saveFile
           (get_asm_listing_filename ())
           (STR ((!BCHARMAssemblyInstructions.arm_assembly_instructions)#toString ())));
        file_output#saveFile
          (get_orphan_code_listing_filename ())
          (STR ((BCHARMAssemblyFunctions.arm_assembly_functions#dark_matter_to_string)));
        save_log_files logcmd;
        exit 0
      end
      

    else if !cmd = "saveexports" then
      begin
	system_info#initialize ;
	load_pe_files () ;
	if has_export_functions () || has_exported_data_values () then
	  let exportdir = if !export_directory = "" then
	      system_settings#get_export_dir
	    else !export_directory in
	  let (success,msg) = disassemble_pe () in
	  if success then
	    let _ = pverbose [ msg ] in
	    let (success,msg) = construct_functions_pe () in
	    if success then
	      let _ = pverbose [ msg ] in
	      begin
		save_exports exportdir ;
		save_ordinal_table exportdir ;
		save_log_files "saveexports" ;
		exit 0
	      end
	    else
	      exit_with_error !cmd msg
	  else
	    exit_with_error !cmd msg
      end

    else
      begin
	pr_debug [ STR "Command " ; STR !cmd ; STR " not recognized" ; NL ] ;
	exit 1
      end
  with
  | CHXmlReader.XmlParseError(line,col,p)
  | XmlReaderError (line,col,p)
  | XmlDocumentError (line,col,p) ->
    begin
      pr_debug [ STR "Xml error: (" ; INT line ; STR ", " ; INT col ; STR "): " ;
		 p ; NL ] ;
      exit 3
    end

  | CHCommon.CHFailure p
  | BCH_failure p ->
    begin
      save_log_files "failure" ;
      pr_debug [ STR "Failure: " ; p ; NL ] ;
      exit 1
    end
  | IO.No_more_input ->
     begin
       save_log_files "failure" ; 
       pr_debug [ STR "Error: No more input" ; NL ] ;
       exit 1
     end
  | Invalid_argument s
  | Internal_error s
  | Invocation_error s ->
    begin
      save_log_files "failure" ;
      pr_debug [ STR "Error: " ; STR s ; NL ] ;
      exit 1
    end

let _ = Printexc.print main ()
	    

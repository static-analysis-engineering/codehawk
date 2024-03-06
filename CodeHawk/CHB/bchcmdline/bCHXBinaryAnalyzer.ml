(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHTiming
open CHXmlDocument

(* bchcil *)
open BCHParseCilFile

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDisassemblySummary
open BCHDoubleword
open BCHFunctionInfo
open BCHGlobalState
open BCHMetrics
open BCHPreFileIO
open BCHSpecializations
open BCHSystemInfo
open BCHSystemSettings
open BCHVersion

(* bchlibpe *)
open BCHPEHeader

(* bchlibelf *)
open BCHELFHeader

(* bchlibx86 *)
open BCHAssemblyFunctions
open BCHDisassemble
open BCHDisassembleELF
open BCHLoopStructure
open BCHPredefinedCallSemantics
open BCHTranslateToCHIF
open BCHX86AnalysisResults

(* bchlibmips32 *)
open BCHDisassembleMIPS
open BCHMIPSAnalysisResults
open BCHMIPSAssemblyFunctions

(* bchlibarm32 *)
open BCHARMAnalysisResults
open BCHARMAssemblyFunctions
open BCHARMCallSitesRecords
open BCHDisassembleARM
open BCHDisassembleARMStream

(* bchlibpower32 *)
open BCHDisassemblePower
open BCHPowerAnalysisResults
open BCHPowerAssemblyFunctions

(* bchanalyze *)
open BCHAnalyzeApp
open BCHFileIO
open BCHSaveExports

module TR = CHTraceResult

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
let set_datablocks = ref false   (* only supported for arm *)
let construct_all_functions = ref false

let stream_start_address = ref wordzero
let set_stream_start_address s =
  stream_start_address := TR.tget_ok (string_to_doubleword s)

let show_chif = ref None
let set_chif s = show_chif := Some s

let speclist =
  [ ("-version", Arg.Unit (fun () -> ()), "show version information and exit") ;
    ("-gc", Arg.Unit (fun () -> cmd := "gc"),
     "show ocaml garbage collector settings and exit") ;
    ("-set_vftables",Arg.Unit  (fun () -> system_settings#set_vftables),
     "declare jumptable targets as funcion entry points") ;
    ("-extracthex", Arg.Unit (fun () -> cmd := "extracthex"),
     "extract executable content from lisphex encoded executable");
    ("-ssa", Arg.Unit (fun () -> system_settings#set_ssa),
     "use static single assignment for register assignments");
    ("-collectdata", Arg.Unit (fun () -> system_settings#set_collect_data),
     "analyze all functions, create ssa variables (if enabled), and "
     ^ " create stacklayouts and proof obligations");
    ("-stream", Arg.Unit (fun () -> cmd := "stream"),
     "stream disassemble a hex-encoded stream of bytes");
    ("-startaddress",  Arg.String set_stream_start_address,
     "start address of the code stream");
    ("-show_function_timing",
     Arg.Unit (fun () -> system_settings#set_show_function_timing),
     "show timing of analysis for every function");
    ("-gc_compact",
     Arg.Int system_settings#set_gc_compact_function_interval,
     ("call garbage collector to compact memory after this many functions "
     ^ "(expensive operation, suggested value > 1000)"));
    ("-arm", Arg.Unit (fun () -> system_settings#set_architecture "arm"),
     "arm executable");
    ("-arm_extension_registers",
     Arg.Unit (fun () -> system_settings#set_arm_extension_registers),
     "include arm floating point registers in analysis");
    ("-thumb", Arg.Unit (fun () -> system_settings#set_thumb),
     "arm executable includes thumb instructions");
    ("-mips", Arg.Unit (fun () -> system_settings#set_architecture "mips"),
     "mips executable");
    ("-power", Arg.Unit (fun () -> system_settings#set_architecture "power"),
     "power executable");
    ("-elf", Arg.Unit (fun () -> system_settings#set_fileformat "elf"),
     "ELF executable");
    ("-extract", Arg.Unit (fun () -> cmd := "extract"),
     "extract executable content from executable and save in xml format");
    ("-xsize", Arg.Int system_info#set_xfilesize,
     "size of the executable in bytes");
    ("-exclude_debug", Arg.Unit (fun () -> system_settings#exclude_debug),
     "do not extract the debug sections");
    ("-dump", Arg.Unit (fun () -> cmd := "dump"),
     "dump entire executable to xml (max size 1MB)");
    ("-disassemble", Arg.Unit (fun () -> cmd := "disassemble"),
     "save an assembly listing of the executable in text format") ;
    ("-analyze", Arg.Unit (fun () -> cmd := "analyze"),
     "analyze the executable and save intermediate results in xml format");
    ("-ignore_stable", Arg.Unit (fun () -> BCHAnalyzeApp.analyze_all := true),
     "continue analyzing functions that have stabilized");
    ("-fn_exclude", Arg.String (fun s -> exclude_function s),
     "exclude the function with the given address from the analysis");
    ("-fn_include", Arg.String (fun s -> include_function s),
     "include the function with the given address in the analysis");
    ("-fn_no_lineq", Arg.String (fun s -> add_no_lineq s),
     "do not apply linear equality analysis to the function with the given address");
    ("-lineq_instr_cutoff",
     Arg.Int system_settings#set_lineq_instr_cutoff,
     "maximum number of instructions for function to be analyzed with relational analysis");
    ("-lineq_block_cutoff",
     Arg.Int system_settings#set_lineq_block_cutoff,
     "maximum number of basic blocks for function to be analyzed with relational analysis");
    ("-preamble_cutoff", Arg.Int system_info#set_preamble_cutoff,
     "preamble cutoff factor for generating function entry points");
    ("-save_cfgs", Arg.Unit (fun () -> savecfgs := true),
     "save basic blocks and loops (applicable to .exe file)") ;
    ("-summaries", Arg.String system_settings#set_summary_jar,
     "path to the jar that holds the library function summaries");
    ("-so_library", Arg.String system_settings#add_so_library,
     "name of a library with shared objects to be searched for summaries");
    ("-appsdir", Arg.String system_settings#set_apps_dir,
     "directory that holds application-dependent summaries") ;
    ("-save_exports", Arg.Unit (fun () -> cmd := "saveexports"),
     "save function summary of exported functions in named directory");
    ("-verbose", Arg.Unit (fun () -> system_settings#set_verbose),
     "print out analysis intermediate results and progress messages");
    ("-diagnostics", Arg.Unit (fun () -> activate_diagnostics ()),
     "collect diagnostic messages and save in diagnostics log");
    ("-show_chif", Arg.String (fun s -> set_chif s),
     "print out CHIF code");
    ("-save_disassembly_status_in_xml", Arg.Unit (fun () -> save_xml := true),
     "save disassembly status in xml for bulk evaluation");
    ("-save_asm", Arg.Unit (fun () -> save_asm := true),
     "save assembly listing in the analysis directory");
    ("-construct_all_functions",
     Arg.Unit (fun () -> construct_all_functions := true),
     "construct all functions even if analyzing only a few of them");
    ("-set_datablocks", Arg.Unit (fun () -> set_datablocks := true),
     "set data blocks for code not included in any function");
    ("-specialization", Arg.String specializations#activate_specialization,
     "apply named specialization");
    ("-ifile", Arg.String system_info#add_ifile,
     "parse a preprocessed c file with cil")
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


let main () =
  try
    let _ = read_args () in
    let _ = chlog#set_max_entry_size 1000 in
    if !cmd = "version" then
      begin
	pr_debug [version#toPretty; NL];
	exit 0
      end

    else if !cmd = "gc" then
      begin
	pr_debug [garbage_collector_settings_to_pretty (); NL];
	exit 0
      end

    else if !cmd = "stream" then
      (* disable address checking in the creation of absolute addresses *)
      let _ = system_info#set_elf_is_code_address wordzero wordmax in
      (let codestring = read_hex_stream_file system_info#get_filename in
       if system_settings#is_x86 then
         begin
           disassemble_stream !stream_start_address codestring;
           pr_debug
	     [STR ((!BCHAssemblyInstructions.assembly_instructions)#toString ())]
         end
       else if system_settings#is_arm then
         let starttime = Unix.gettimeofday () in
         begin
           BCHDisassembleARMStream.disassemble_stream !stream_start_address codestring;
           for _i = 1 to 10 do
             analyze_arm starttime
           done;
           pr_debug [(get_function_info !stream_start_address)#finv#toPretty]
         end
       else
         pr_debug [STR "Stream disassembly currently not supported"; NL])

    else if !cmd = "extracthex" then
      let _ = register_hashed_functions () in
      let (success,msg) = read_hexlified_pe_file system_info#get_filename in
      if success then
        begin
          pverbose [msg; NL];
          save_pe_files ();
          save_log_files "extracthex";
          exit 0
        end
      else
        exit_with_error !cmd msg

    else if !cmd = "extract" && system_settings#is_x86 && system_settings#is_pe then
      let _ = register_hashed_functions () in
      let (success,msg) = read_pe_file system_info#get_filename version#get_maxfilesize in
      if success then
	begin
	  pverbose [msg; NL];
	  save_pe_files ();
	  save_log_files "extract";
	  exit 0
	end
      else
	exit_with_error !cmd msg

    else if !cmd = "extract" && system_settings#is_elf then
      let _ = system_info#initialize in
      let (success, msg) =
        read_elf_file system_info#get_filename system_info#get_xfilesize in
      if success then
        begin
          pverbose [msg; NL];
          save_elf_files ();
          save_log_files "extract";
          exit 0
        end
      else
        exit_with_error !cmd msg

    else if !cmd = "dump" then
      dump_pe_file system_info#get_filename

    else if !cmd = "disassemble"
            && system_settings#is_x86
            && system_settings#is_pe then
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

    else if !cmd = "disassemble"
            && system_settings#is_x86
            && system_settings#is_elf then
      let t0 = ref (Unix.gettimeofday ()) in
      let _ = load_bdictionary () in
      let _ = system_info#initialize in
      let _ = pr_timing [STR "system_info initialized"] in
      let _ = load_elf_files () in
      let _ = pr_timing [STR "elf files loaded"] in
      let _ = disassemble_elf_sections () in
      let _ = pr_timing [STR "sections disassembled"] in
      let _ =
        disassembly_summary#record_disassembly_time
          ((Unix.gettimeofday ()) -. !t0) in
      let t1 = ref (Unix.gettimeofday ()) in
      let _ = construct_functions_elf () in
      let _ = pr_timing [STR "functions constructed"] in
      let _ =
        disassembly_summary#record_construct_functions_time
          ((Unix.gettimeofday ()) -. !t1) in
      let _ =
        disassembly_summary#set_disassembly_metrics (get_disassembly_metrics ()) in
      let _ = pr_debug [disassembly_summary#toPretty; NL] in
      begin
        file_output#saveFile
          (get_asm_listing_filename ())
          (STR ((!BCHAssemblyInstructions.assembly_instructions)#toString ()));
        pr_timing [STR "assembly listing saved"];
	file_output#saveFile
          (get_orphan_code_listing_filename ())
	  (STR ((BCHAssemblyFunctions.assembly_functions#dark_matter_to_string)));
        pr_timing [STR "orphan-code listing saved"];
        file_output#saveFile
          (get_duplicate_coverage_filename ())
          (STR (BCHAssemblyFunctions.assembly_functions#duplicates_to_string));
        pr_timing [STR "duplicates listing saved"];
        save_log_files "disassemble";
        pr_timing [STR "log files saved"]
      end

    else if !cmd = "disassemble"
            && system_settings#is_mips
            && system_settings#is_elf then
      let _ = system_info#initialize in
      let t = ref (Unix.gettimeofday ()) in
      let _ = pr_debug [STR "Load MIPS file ..."; NL] in
      let ifiles = system_info#ifiles in
      let _ =
        if (List.length ifiles) > 0 then
          begin
            pr_debug [STR "Parse pre-processed c files"; NL];
            List.iter parse_cil_file ifiles
          end in
      let _ = load_elf_files () in
      let _ = pr_debug [STR "disassemble sections ... "; NL] in
      let _ = disassemble_mips_sections ()  in
      let _ = disassembly_summary#record_disassembly_time
                ((Unix.gettimeofday ()) -. !t) in
      let t = ref (Unix.gettimeofday ()) in
      let _ = construct_functions_mips () in
      let _ = mips_assembly_functions#inline_blocks in
      let _ = disassembly_summary#record_construct_functions_time
                ((Unix.gettimeofday ()) -. !t) in
      let _ =
        disassembly_summary#set_disassembly_metrics
          (get_mips_disassembly_metrics ()) in
      let _ = pr_debug [disassembly_summary#toPretty; NL] in
      (*
      let _ =
        pr_debug [
            LBLOCK
              (List.map (fun f ->
                   f#toPretty)
                 BCHDwarfQueryService.dwarf_query_service#debug_info_functions)] in
      let _ =
        pr_debug [
            NL;
            STR "Location operations";
            NL;
            BCHDwarfQueryService.dwarf_query_service#toPretty;
            NL] in
       *)
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
        (if (List.length ifiles) > 0 then
           begin
             save_bc_files ();
             save_interface_dictionary ();
             save_bdictionary ();
             save_bcdictionary ();
           end
         else
           begin
             save_interface_dictionary ();
             save_bdictionary ()
           end);
        save_log_files "disassemble";
      end

    else if !cmd = "disassemble"
            && system_settings#is_power
            && system_settings#is_elf then
      let _ = system_info#initialize in
      let _ = load_elf_files () in
      let _ = pr_timing [STR "elf power files loaded"] in
      let _ = List.iter parse_cil_file system_info#ifiles in
      let _ =
        if (List.length system_info#ifiles) > 0 then
          pr_timing [STR "c header files loaded"] in
      let _ = disassemble_pwr_sections () in
      let _ = pr_timing [STR "sections disassembled"] in
      let _ = construct_functions_pwr () in
      let _ = pr_timing [STR "functions constructed"] in
      let _ = disassembly_summary#set_disassembly_metrics
                (get_pwr_disassembly_metrics ()) in
      let _ = pr_debug [NL; NL; disassembly_summary#toPretty; NL] in
      let instrs = !BCHPowerAssemblyInstructions.pwr_assembly_instructions in
      begin
        pverbose [STR "Saving asm file ..."; NL];
        file_output#saveFile
          (get_asm_listing_filename ())
          (LBLOCK [STR (instrs#toString ()); NL]);
        save_log_files "disassemble"
      end

    else if !cmd = "disassemble"
            && system_settings#is_arm
            && system_settings#is_elf then
      let _ = system_info#initialize in
      let t = ref (Unix.gettimeofday ()) in
      let _ = load_elf_files () in
      let _ = pr_timing [STR "elf files loaded"] in
      let _ = List.iter parse_cil_file system_info#ifiles in
      let _ =
        if (List.length system_info#ifiles) > 0 then
          pr_timing [STR "c header files loaded"] in
      let _ = disassemble_arm_sections () in
      let _ = pr_timing [STR "sections disassembled"] in
      let _ = disassembly_summary#record_disassembly_time
                ((Unix.gettimeofday ()) -. !t) in
      let _ = construct_functions_arm
                ~construct_all_functions:!construct_all_functions in
      let _ = arm_assembly_functions#inline_blocks in
      let _ = pr_timing [STR "functions constructed"] in
      let _ = if !set_datablocks then
                arm_assembly_functions#set_datablocks in
      let _ = disassembly_summary#record_construct_functions_time
                ((Unix.gettimeofday ()) -. !t) in
      let _ = disassembly_summary#set_disassembly_metrics
                (get_arm_disassembly_metrics ()) in
      let _ = pr_debug [NL; NL; disassembly_summary#toPretty; NL] in
      (*
      let _ =
        pr_debug [
            LBLOCK
              (List.map (fun f ->
                   f#toPretty)
                 BCHDwarfQueryService.dwarf_query_service#debug_info_functions)] in
      let _ =
        pr_debug [
            NL;
            STR "Location operations";
            NL;
            BCHDwarfQueryService.dwarf_query_service#toPretty;
            NL] in
       *)
      begin
        if !save_asm then
          begin
            let datarefs = get_arm_data_references () in
            file_output#saveFile
              (get_asm_listing_filename ())
              (let instrs = !BCHARMAssemblyInstructions.arm_assembly_instructions in
               (LBLOCK [
                    STR (instrs#toString ~datarefs ());
                    arm_callsites_records#toPretty;
                    arm_callsites_records#summary_to_pretty]));
            pr_timing [STR "assembly listing saved"];
	    file_output#saveFile
              (get_orphan_code_listing_filename ())
	      (STR ((BCHARMAssemblyFunctions.arm_assembly_functions#dark_matter_to_string)));
            pr_timing [STR "orphan code listing saved"];
            file_output#saveFile
              (get_duplicate_coverage_filename ())
              (STR (BCHARMAssemblyFunctions.arm_assembly_functions#duplicates_to_string));
            pr_timing [STR "duplicates listing saved"];
            save_system_info ();
            pr_timing [STR "system_info saved"];
            save_arm_dictionary ();
            pr_timing [STR "dictionary saved"];
            save_interface_dictionary ();
            pr_timing [STR "interface dictionary saved"];
            save_bcdictionary ();
            pr_timing [STR "bcdictionary saved"];
            save_bdictionary ();
            pr_timing [STR "bdictionary saved"]
          end;
        save_log_files "disassemble";
        pr_timing [STR "log files saved"]
      end

    else if !cmd = "analyze"
            && system_settings#is_x86
            && system_settings#is_pe then
      let _ = register_hashed_functions () in
      let starttime = Unix.gettimeofday () in
      let _ = load_bcdictionary () in
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
            save_bcdictionary ();
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

    else if !cmd = "analyze"
            && system_settings#is_x86
            && system_settings#is_elf then
      (* let _ = register_hashed_elf_functions () in *)
      let starttime = Unix.gettimeofday () in
      let _ = load_bcdictionary () in
      let _ = pr_timing [STR "bcdictionary loaded"] in
      let _ = load_bdictionary () in
      let _ = pr_timing [STR "bdictionary loaded"] in
      let _ = load_bc_files () in
      let _ = pr_timing [STR "bc files loaded"] in
      let _ = system_info#initialize in
      let _ = pr_timing [STR "system_info initialized"] in
      let _ = load_interface_dictionary () in
      let _ = pr_timing [STR "interface dictionary loaded"] in
      let _ = load_x86dictionary () in
      let _ = pr_timing [STR "x86 dictionary loaded"] in
      let _ = global_system_state#initialize in
      let _ = pr_timing [STR "global system state initialized"] in
      let _ = file_metrics#load_xml in
      let _ =
        pr_timing [
            STR "file metrics loaded (index "; INT file_metrics#get_index; STR ")"] in
      let _ = load_elf_files () in
      let _ = pr_timing [STR "elf files loaded"] in
      let index = file_metrics#get_index in
      let logcmd = "analyze_"  ^ (string_of_int index) in
      let _ = disassemble_elf_sections () in
      let _ = pr_timing [STR "elf sections disassembled"] in
      let _ = construct_functions_elf () in
      let _ = pr_timing [STR "functions constructed"] in
      let _ = analyze starttime in
      let _ = pr_timing [STR "analysis is finished"] in
      let _ = file_metrics#set_disassembly_results (get_disassembly_metrics ()) in
      begin
	save_functions_list ();
        pr_timing [STR "functions list saved"];
	save_system_info ();
        pr_timing [STR "system_info saved"];
	save_file_results ();
        pr_timing [STR "file results saved"];
	save_global_state ();
        pr_timing [STR "global state saved"];
        x86_analysis_results#save;
        pr_timing [STR "analysis results saved"];
        save_x86dictionary ();
        pr_timing [STR "x86 dictionary saved"];
        save_bc_files ();
        pr_timing [STR "bc files saved"];
        save_interface_dictionary ();
        pr_timing [STR "interface dictionary saved"];
        save_bcdictionary ();
        pr_timing [STR "bcdictionary saved"];
        save_bdictionary ();
        pr_timing [STR "bdictionary saved"];
	save_log_files logcmd;
        pr_timing [STR "log files saved"];
	exit 0
      end

    else if !cmd = "analyze"
            && system_settings#is_mips
            && system_settings#is_elf then
      let starttime = Unix.gettimeofday () in
      let _ = load_bcdictionary () in
      let _ = pr_timing [STR "bcdictionary loaded"] in
      let _ = load_bdictionary () in
      let _ = pr_timing [STR "bdictionary loaded"] in
      let _ = load_bc_files () in
      let _ = pr_timing [STR "bc files loaded"] in
      let _ = system_info#initialize in
      let _ = pr_timing [STR "system info initialized"] in
      let _ = load_interface_dictionary () in
      let _ = pr_timing [STR "interface dictionary loaded"] in
      let _ = load_mips_dictionary () in
      let _ = pr_timing [STR "mips dictionary loaded"] in
      let _ = global_system_state#initialize in
      let _ = pr_timing [STR "global system state initialized"] in
      let _ = file_metrics#load_xml in
      let _ =
        pr_timing [
            STR "file metrics loaded (index ";
            INT file_metrics#get_index;
            STR ")"] in
      let _ = load_elf_files () in
      let _ = pr_timing [STR "elf files loaded"] in
      let _ =
        List.iter
          (fun f -> parse_cil_file ~removeUnused:false f) system_info#ifiles in
      let _ =
        if (List.length system_info#ifiles > 0) then
          pr_timing [STR "c header files parsed"] in
      let index = file_metrics#get_index in
      let logcmd = "analyze_" ^ (string_of_int index) in
      let _ = disassemble_mips_sections () in
      let _ = pr_timing [STR "elf sections disassembled"] in
      let _ = construct_functions_mips () in
      let _ = pr_timing [STR "functions constructed"] in
      let _ = mips_assembly_functions#inline_blocks in
      let _ = analyze_mips starttime in
      let _ = pr_timing [STR "analysis is finished"] in
      let _ =
        file_metrics#set_disassembly_results
          (get_mips_disassembly_metrics ()) in
      begin
	save_system_info ();
        pr_timing [STR "system info saved"];
	save_file_results ();
        pr_timing [STR "file results saved"];
	save_global_state ();
        pr_timing [STR "global state saved"];
        mips_analysis_results#save;
        pr_timing [STR "analysis results saved"];
        save_mips_assembly_instructions ();
        pr_timing [STR "assembly instructions saved"];
        save_mips_dictionary ();
        pr_timing [STR "mips dictionary saved"];
        save_bc_files ();
        save_interface_dictionary ();
        pr_timing [STR "interface dictionary saved"];
        save_bcdictionary ();
        pr_timing [STR "bcdictionary saved"];
        save_bdictionary ();
        pr_timing [STR "bdictionary saved"];
        (file_output#saveFile
           (get_asm_listing_filename ())
           (STR ((!BCHMIPSAssemblyInstructions.mips_assembly_instructions)#toString ())));
	file_output#saveFile
          (get_orphan_code_listing_filename ())
	  (STR ((BCHMIPSAssemblyFunctions.mips_assembly_functions#dark_matter_to_string)));
	save_log_files logcmd;
        pr_timing [STR "log files saved"];
	exit 0
      end

    else if !cmd = "analyze"
            && system_settings#is_arm
            && system_settings#is_elf then
      let _ = load_bcdictionary () in
      let _ = pr_timing [STR "bcdictionary loaded"] in
      let _ = load_bdictionary () in
      let _ = pr_timing [STR "bdictionary loaded"] in
      let _ = load_bc_files () in
      let _ = pr_timing [STR "bc files loaded"] in
      let _ = system_info#initialize in
      let _ = pr_timing [STR "system info initialized"] in
      let _ = load_interface_dictionary () in
      let _ = pr_timing [STR "interface dictionary loaded"] in
      let _ = load_arm_dictionary () in
      let _ = pr_timing [STR "arm dictionary loaded"] in
      let _ = global_system_state#initialize in
      let _ = pr_timing [STR "global system state initialized"] in
      let _ = file_metrics#load_xml in
      let _ =
        pr_timing [
            STR "file metrics loaded (index ";
            INT file_metrics#get_index;
            STR ")"] in
      let _ = load_elf_files () in
      let _ = pr_timing [STR "elf files loaded"] in
      let _ =
        List.iter
          (fun f -> parse_cil_file ~removeUnused:false f) system_info#ifiles in
      let _ =
        if (List.length system_info#ifiles > 0) then
          pr_timing [STR "c header files parsed"] in
      let index = file_metrics#get_index in
      let logcmd = "analyze_" ^ (string_of_int index) in
      let analysisstart = Unix.gettimeofday () in
      let _ = disassemble_arm_sections () in
      let _ = pr_timing [STR "elf sections disassembled"] in
      let _ = construct_functions_arm
                ~construct_all_functions:!construct_all_functions in
      let _ = arm_assembly_functions#inline_blocks in
      let _ = pr_timing [STR "functions constructed"] in
      let _ = analyze_arm analysisstart in
      let _ = pr_timing [STR "analysis is finished"] in
      (*        for i = 0 to (!analysisrepeats - 1) do
          let analysisstart = Unix.gettimeofday () in
          analyze_arm analysisstart
        done in *)
      let _ =
        file_metrics#set_disassembly_results (get_arm_disassembly_metrics ()) in
      begin
        save_functions_list ();
        pr_timing [STR "functions list saved"];
        save_system_info ();
        pr_timing [STR "system info saved"];
        save_file_results ();
        pr_timing [STR "file results saved"];
        save_global_state ();
        pr_timing [STR "global state saved"];
        arm_analysis_results#save;
        pr_timing [STR "analysis results saved"];
        (* save_arm_assembly_instructions (); *)
        save_arm_dictionary ();
        pr_timing [STR "arm dictionary saved"];
        save_bc_files ();
        pr_timing [STR "bc files saved"];
        save_interface_dictionary ();
        pr_timing [STR "interface dictionary saved"];
        save_type_constraint_dictionary ();
        pr_timing [STR "type constraint dictionary saved"];
        save_bcdictionary ();
        pr_timing [STR "bc dictionary saved"];
        save_bdictionary ();
        pr_timing [STR "bdictionary saved"];
        (if !save_asm then
           begin
             file_output#saveFile
               (get_asm_listing_filename ())
               (STR ((!BCHARMAssemblyInstructions.arm_assembly_instructions)#toString ()));
             pr_timing [STR "assembly listing saved"];
             file_output#saveFile
               (get_orphan_code_listing_filename ())
               (STR ((BCHARMAssemblyFunctions.arm_assembly_functions#dark_matter_to_string)));
             pr_timing [STR "orphan code listing saved"]
           end);
        save_log_files logcmd;
        pr_timing [STR "log files saved"];
        exit 0
      end

    else if !cmd = "analyze"
            && system_settings#is_power
            && system_settings#is_elf then
      let _ = load_bcdictionary () in
      let _ = load_bdictionary () in
      let _ = load_bc_files () in
      let _ = system_info#initialize in
      let _ = load_interface_dictionary () in
      let _ = load_pwr_dictionary () in
      let _ = global_system_state#initialize in
      let _ = file_metrics#load_xml in
      let _ = load_elf_files () in
      let _ =
        List.iter
          (fun f -> parse_cil_file ~removeUnused:false f) system_info#ifiles in
      let index = file_metrics#get_index in
      let logcmd = "analyze_" ^ (string_of_int index) in
      let analysisstart = Unix.gettimeofday () in
      let _ = disassemble_pwr_sections () in
      let _ = construct_functions_pwr () in
      let _ = analyze_pwr analysisstart in
      let _ =
        file_metrics#set_disassembly_results
          (get_pwr_disassembly_metrics ()) in
      begin
        save_functions_list ();
        save_system_info ();
        save_file_results ();
        save_global_state ();
        pwr_analysis_results#save;
        save_pwr_dictionary ();
        save_bc_files ();
        save_interface_dictionary ();
        save_bcdictionary ();
        save_bdictionary ();
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
	pr_debug [STR "Command "; STR !cmd; STR " not recognized"; NL];
	exit 1
      end
  with
  | CHXmlReader.XmlParseError(line, col, p)
  | CHXmlReader.XmlReaderError (line, col, p)
  | XmlDocumentError (line, col, p) ->
    begin
      pr_debug [
          STR "Xml error: ("; INT line; STR ", "; INT col; STR "): "; p; NL];
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
  | Invalid_argument s ->
     save_log_files "failure";
     pr_debug [STR "Error: Invalid_argument: "; STR s; NL];
     exit 1
  | Internal_error s ->
     save_log_files "failure";
     pr_debug [STR "Error: Internal_error: "; STR s; NL];
     exit 1
  | Invocation_error s ->
    begin
      save_log_files "failure";
      pr_debug [STR "Error: Invocation_error: " ; STR s; NL];
      exit 1
    end

let _ = Printexc.print main ()

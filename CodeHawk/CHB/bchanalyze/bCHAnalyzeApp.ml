(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
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

open Gc

(* chlib *)
open CHCommon
open CHPretty

(* chutil *)
open CHLogger
open CHTiming
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHDoubleword
open BCHLibTypes
open BCHFunctionInfo
open BCHMetrics
open BCHPreFileIO
open BCHSystemInfo
open BCHSystemSettings
open BCHUtilities

(* bchlibx86 *)
open BCHAssemblyFunctions
open BCHDisassemble
open BCHIFSystem
open BCHLoopStructure
open BCHTranslateToCHIF
open BCHX86AnalysisResults   
open BCHX86Metrics

(* bchlibmips32 *)
open BCHDisassembleMIPS
open BCHMIPSAnalysisResults
open BCHMIPSCHIFSystem
open BCHMIPSAssemblyFunctions
open BCHMIPSLoopStructure
open BCHMIPSMetrics
open BCHTranslateMIPSToCHIF

(* bchlibarm32 *)
open BCHDisassembleARM
open BCHARMAnalysisResults
open BCHARMAssemblyFunctions
open BCHARMCHIFSystem
open BCHARMLoopStructure
open BCHARMMetrics
open BCHTranslateARMToCHIF

(* bchlibpower32 *)
open BCHPowerAnalysisResults
open BCHPowerAssemblyFunction
open BCHPowerAssemblyFunctions
open BCHPowerCHIFSystem
open BCHPowerMetrics
open BCHPowerTypes
open BCHTranslatePowerToCHIF

(* bchanalyze *)
open BCHAnalysisTypes
open BCHAnalyzeProcedure
open BCHDefUse
open BCHDefUseHigh
open BCHDesignation
open BCHExtractInvariants
open BCHFileIO
open BCHReachingDefs
open BCHTrace

module TR = CHTraceResult


let analyze_all = ref false
let maxrelationalvarcomplexity = ref 150000.0
let maxrelationalloopcomplexity = ref 2000

let no_lineq = ref []
let add_no_lineq s = no_lineq := s :: !no_lineq


let analyze_x86_function faddr f count =
  let _ =
    if system_settings#show_function_timing then
      pr_timing [
          STR "analyzing function (";
          INT count;
          STR "): ";
          faddr#toPretty;
          STR ": ";
          INT (List.length f#get_blocks);
          STR " blocks; ";
          INT f#get_instruction_count;
          STR " instructions"] in
  let _ =
    if system_settings#gc_compact_function_interval > 0 then
      (if (count mod system_settings#gc_compact_function_interval) = 0 then
         begin
           pr_timing [STR "Initiate Gc.compact"];
           Gc.compact ();
           pr_timing [STR "Finish Gc.compact"]
         end) in
  let fstarttime = Unix.gettimeofday () in
  let finfo =  load_function_info faddr in
  let _ = translate_assembly_function f in
  if chif_system#has_procedure_by_address faddr then
    let loopcomplexity = get_cfg_loop_complexity f in
    let varcomplexity = get_vc_complexity f finfo#env in
    let relational =
      varcomplexity <= !maxrelationalvarcomplexity &&
	loopcomplexity <= !maxrelationalloopcomplexity in
    let proc = chif_system#get_procedure_by_address faddr in
    begin
      bb_invariants#reset;
      analyze_procedure_with_intervals proc chif_system#get_system ;
      (if relational then
	 analyze_procedure_with_linear_equalities proc chif_system#get_system 
       else
         begin
	   chlog#add "skip relational analysis" faddr#toPretty ;
           pr_info[
               STR "skip LR analysis of ";
               faddr#toPretty;
               STR " (loop complexity: ";
               INT loopcomplexity;
               STR ", variable complexity: ";
               STR (Printf.sprintf "%.0f" varcomplexity);
               STR ")";
               NL]
         end);
      analyze_procedure_with_valuesets proc chif_system#get_system ;
      extract_ranges finfo bb_invariants#get_invariants ;
      (if relational then
	 extract_linear_equalities finfo bb_invariants#get_invariants ) ;
      extract_valuesets finfo bb_invariants#get_invariants ;
      resolve_indirect_calls f ;
      record_fpcallback_arguments f ;
      finfo#reset_invariants ;
      save_function_info finfo ;
      save_function_invariants finfo ;
      save_function_type_invariants finfo ;
      x86_analysis_results#record_results f ;              
      save_function_variables finfo ;
      file_metrics#record_results
	~nonrel:(not relational)
	~reset:finfo#were_invariants_reset
	faddr
	((Unix.gettimeofday ()) -. fstarttime)
        (get_memory_access_metrics f finfo)
        (get_cfg_metrics f finfo#env) ;
    end
  else
    pr_error [STR "Translation failed"; NL]


let analyze starttime =
  let fns_included = included_functions () in
  let fns_excluded = excluded_functions () in
  let count = ref 0 in
  let failedfunctions = ref [] in
  let functionfailure failuretype faddr p =
    begin
      ch_error_log#add
        "function failure"
	(LBLOCK [
             STR failuretype;
             STR ". ";
             faddr#toPretty;
             STR ": ";
             p]);
      failedfunctions := faddr :: !failedfunctions
    end in

  begin
    (if (List.length fns_included) > 0 then
       List.iter
         (fun faddr ->
           let faddr =
             fail_tvalue
               (trerror_record
                  (LBLOCK [STR "analyze:faddr: "; STR faddr]))
               (string_to_doubleword faddr) in
           let f = assembly_functions#get_function_by_address faddr in
           let _ = count := !count + 1 in
           try
             analyze_x86_function faddr f !count;
             pr_interval_timing [STR "functions analyzed: "; INT !count] 60.0
	    with
	    | Failure s -> functionfailure "Failure" faddr (STR s)
	    | Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
	    | Internal_error s -> functionfailure "Internal error" faddr (STR s)
	    | Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
	    | CHFailure p -> functionfailure "CHFailure" faddr p
	    | BCH_failure p -> functionfailure "BCHFailure" faddr p) fns_included
     else
       assembly_functions#bottom_up_itera
         (fun faddr f ->
           if List.mem faddr#to_hex_string fns_excluded then
             ()
           else
             let callees = get_app_callees faddr in
             let _ =
               List.iter (fun callee ->
	           let cfinfo = get_function_info callee in
	           if cfinfo#sideeffects_changed then
	             begin
	               (get_function_info faddr)#reset_invariants;
	               chlog#add "reset invariants"
	                 (LBLOCK [
                              faddr#toPretty;
                              STR " due to callee ";
                              callee#toPretty])
	             end) callees in
             let appCallees = List.map (fun a -> a#to_hex_string) callees in
             if file_metrics#is_stable faddr#to_hex_string appCallees &&
	          (not !analyze_all) then
               x86_analysis_results#record_results ~save:false f
             else
	       let _ = count := !count + 1 in
               try
                 analyze_x86_function faddr f !count;
                 pr_interval_timing [STR "functions analyzed: "; INT !count] 60.0
	       with
	       | Failure s -> functionfailure "Failure" faddr (STR s)
	       | Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
	       | Internal_error s -> functionfailure "Internal error" faddr (STR s)
	       | Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
	       | CHFailure p -> functionfailure "CHFailure" faddr p
	       | BCH_failure p -> functionfailure "BCHFailure" faddr p));

    let propstarttime = Unix.gettimeofday () in
    let _ = pr_timing [STR "bottom-up analysis finished"] in
    if (List.length fns_included = 0) then
      begin
        assembly_functions#top_down_itera
          (fun faddr f ->
	    try
	      begin
	        f#iter_calls (fun _ floc ->
	            if floc#has_call_target && floc#get_call_target#is_app_call then
		      let tgtaddr = floc#get_call_target#get_app_address in
		      let tgtfinfo = get_function_info tgtaddr in
                      if not (List.mem tgtaddr !failedfunctions) then
		        begin
		          save_function_info tgtfinfo
		        end);
	        save_function_summary (get_function_info faddr)
	      end
	    with
	    | Failure s -> functionfailure "Failure" faddr (STR s)
	    | Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
	    | Internal_error s -> functionfailure "Internal error" faddr (STR s)
	    | Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
	    | CHFailure p -> functionfailure "CHFailure" faddr p
	    | BCH_failure p ->
	       ch_error_log#add
                 "pushing arguments"
                 (LBLOCK [faddr#toPretty; STR ": "; p]));
        file_metrics#record_propagation_time ((Unix.gettimeofday ()) -. propstarttime);
        file_metrics#record_runtime ((Unix.gettimeofday ()) -. starttime);
        pr_timing [STR "top-down analysis finished"];
        (match !failedfunctions with
         | [] -> ()
         | l ->
	    chlog#add
              "failed functions"
	      (LBLOCK (List.map (fun faddr -> LBLOCK [faddr#toPretty; NL]) l)))
      end
  end


let analyze_mips_function faddr f count =
  let fstarttime = Unix.gettimeofday () in
  let finfo = load_function_info faddr in
  let _ = pverbose [ STR "Analyze " ; faddr#toPretty ; STR " (started: " ;
                     STR (time_to_string fstarttime) ; STR ")" ; NL ] in
  let _ = translate_mips_assembly_function f in
  if mips_chif_system#has_mips_procedure faddr then
    let _ = record_loop_levels faddr in
    let loopcount = get_loop_count_from_table f in
    let loopdepth = get_loop_depth_from_table f in
    let fintervaltime = ref 0.0 in
    let dointervals = ref (loopdepth < 11) in
    let dorelational = ref true in
    let dovaluesets = ref true in
    let proc = mips_chif_system#get_mips_procedure faddr in
    begin
      bb_invariants#reset  ;
      (if !dointervals then
         analyze_procedure_with_intervals proc mips_chif_system#get_mips_system
       else
         pr_debug [ STR "skip all analyses for " ; faddr#toPretty ;
                    STR ". loopcount: " ; INT loopcount ;
                    STR "; loopdepth: " ; INT loopdepth ;
                    STR "; instrs: " ; INT f#get_instruction_count ; NL ]);
      fintervaltime := (Unix.gettimeofday ()) -. fstarttime;
      dorelational := !dointervals && (!fintervaltime < 50.0);
      dovaluesets := !dointervals && (!fintervaltime < 60.0);
      (if !dorelational then
         analyze_procedure_with_linear_equalities proc mips_chif_system#get_mips_system
       else
         pr_debug [ STR "skip LR analysis for " ; faddr#toPretty ;
                    STR " (size: " ; INT f#get_instruction_count ; STR " instrs)" ;
                    STR " (intervaltime: " ;
                    STR (Printf.sprintf "%.4f" !fintervaltime) ; STR " secs)" ]) ;
      (if !dovaluesets then
         analyze_procedure_with_valuesets proc mips_chif_system#get_mips_system
       else
         pr_debug [ STR " ... and valuesets" ]);
      (if !dointervals then extract_ranges finfo bb_invariants#get_invariants) ;
      (if !dorelational then extract_linear_equalities finfo bb_invariants#get_invariants) ;
      (if !dovaluesets then extract_valuesets finfo bb_invariants#get_invariants) ;
      (try
         resolve_indirect_mips_calls f
       with IO.No_more_input ->
         begin
           pr_debug [ STR "Error in resolve indirect calls: No more input" ; NL ];
           raise IO.No_more_input
         end);
      finfo#reset_invariants ;
      save_function_info finfo ;
      save_function_invariants finfo ;
      save_function_type_invariants finfo ;
      mips_analysis_results#record_results f ;
      save_function_variables finfo ;
      file_metrics#record_results
	~nonrel:(not !dorelational)
	~reset:finfo#were_invariants_reset
 	faddr
	((Unix.gettimeofday ()) -. fstarttime)
        (get_mips_memory_access_metrics f finfo)
        (get_mips_cfg_metrics f finfo#env) ;
      (if (not !dorelational) || (not !dovaluesets) then
         pr_debug [ STR " - done: " ;
                    STR (Printf.sprintf "%.4f" ((Unix.gettimeofday ()) -. fstarttime)) ;
                    STR " secs" ; STR " (" ; INT count ; STR ")" ; NL ])
    end
  else
    pr_debug [ STR "Translation failed" ; NL ]


let analyze_mips starttime =
  let fns_included = included_functions () in
  let count = ref 0 in
  let failedfunctions = ref [] in
  let functionfailure failuretype faddr p =
    begin
      ch_error_log#add "function failure"
	(LBLOCK [STR failuretype; STR ". "; faddr#toPretty; STR ": "; p]);
      failedfunctions := faddr :: !failedfunctions
    end in
  begin
    (if (List.length fns_included) > 0 then
       List.iter
         (fun faddr ->
           let faddr = TR.tget_ok (string_to_doubleword faddr) in
           let f = mips_assembly_functions#get_function_by_address faddr in
           let _ = count := !count + 1 in
           analyze_mips_function faddr f !count) fns_included
     else
       mips_assembly_functions#bottom_up_itera
         (fun faddr f ->
           if file_metrics#is_stable faddr#to_hex_string [] &&
	        (not !analyze_all) then
             mips_analysis_results#record_results ~save:false f
           else
             let _ = count := !count + 1 in
             try
               analyze_mips_function faddr f !count;
               pr_interval_timing [STR "functions analyzed: "; INT !count] 60.0
             with
             | Failure s -> functionfailure "Failure" faddr (STR s)
             | IO.No_more_input ->
                begin
                  pr_debug [
                      STR "Function failure for ";
                      faddr#toPretty;
                      STR ": No more input";
                      NL];
                  raise IO.No_more_input
                end
             | Invalid_argument s ->
                functionfailure "Invalid argument" faddr (STR s)
             | Internal_error s ->
                functionfailure "Internal error" faddr (STR s)
             | Invocation_error s ->
                functionfailure "Invocation error" faddr (STR s)
             | CHFailure p -> functionfailure "CHFailure" faddr p
             | BCH_failure p -> functionfailure "BCHFailure" faddr p ));

    file_metrics#record_runtime ((Unix.gettimeofday ()) -. starttime);
  end


let analyze_arm_function faddr f count =
  let _ =
    if system_settings#show_function_timing then
      pr_timing [
          STR "analyzing function (";
          INT count;
          STR "): ";
          faddr#toPretty;
          STR ": ";
          INT (List.length f#get_blocks);
          STR " blocks; ";
          INT f#get_instruction_count;
          STR " instructions"] in
  let _ =
    if system_settings#gc_compact_function_interval > 0 then
      (if (count mod system_settings#gc_compact_function_interval) = 0 then
         begin
           pr_timing [STR "Initiate Gc.compact"];
           Gc.compact ();
           pr_timing [STR "Finish Gc.compact"]
         end) in
  let fstarttime = Unix.gettimeofday () in
  let finfo = load_function_info faddr in
  let islarge =
    system_settings#is_lineq_restricted
      ~blocks:(List.length f#get_blocks)
      ~instrs:f#get_instruction_count in
  let _ = translate_arm_assembly_function f in
  if arm_chif_system#has_arm_procedure faddr then
    let _ = record_arm_loop_levels faddr in
    let proc = arm_chif_system#get_arm_procedure faddr in
    begin
      bb_invariants#reset;
      analyze_procedure_with_intervals proc arm_chif_system#get_arm_system;
      (if (List.mem faddr#to_hex_string !no_lineq) || islarge then
         chlog#add
           "skip linear equalities"
           (LBLOCK [
                faddr#toPretty;
                STR ": ";
                INT (List.length f#get_blocks);
                STR " blocks; ";
                INT f#get_instruction_count;
                STR " instructions"])
       else
         analyze_procedure_with_linear_equalities
           proc arm_chif_system#get_arm_system);
      analyze_procedure_with_valuesets proc arm_chif_system#get_arm_system;
      analyze_procedure_with_designations proc arm_chif_system#get_arm_system;
      analyze_procedure_with_reaching_defs proc arm_chif_system#get_arm_system;
      analyze_procedure_with_flag_reaching_defs proc arm_chif_system#get_arm_system;
      (if islarge then
         chlog#add "skip def-use" (faddr#toPretty)
       else
         analyze_procedure_with_def_use proc arm_chif_system#get_arm_system);
      (if islarge then
         chlog#add "skip def-use-high" (faddr#toPretty)
       else
         analyze_procedure_with_def_use_high proc arm_chif_system#get_arm_system);
      extract_ranges finfo bb_invariants#get_invariants;
      extract_linear_equalities finfo bb_invariants#get_invariants;
      extract_valuesets finfo bb_invariants#get_invariants;
      extract_designations finfo bb_invariants#get_invariants;
      extract_reaching_defs finfo bb_invariants#get_invariants;
      extract_flag_reaching_defs finfo bb_invariants#get_invariants;
      extract_def_use finfo bb_invariants#get_invariants;
      extract_def_use_high finfo bb_invariants#get_invariants;
      finfo#reset_invariants;
      save_function_info finfo;
      save_function_invariants finfo;
      save_function_var_invariants finfo;
      arm_analysis_results#record_results f;
      save_function_variables finfo;
      file_metrics#record_results
        faddr
        ((Unix.gettimeofday ()) -. fstarttime)
        (get_arm_memory_access_metrics f finfo)
        (get_arm_cfg_metrics f finfo#env)
    end
  else
    ch_error_log#add
      "translation failure"
      (LBLOCK [faddr#toPretty])


let analyze_arm starttime =
  let fns_included = included_functions () in
  let fns_excluded = excluded_functions () in
  let count = ref 0 in
  let failedfunctions = ref [] in
  let functionfailure (failuretype: string) (faddr: doubleword_int) (p: pretty_t) =
    begin
      ch_error_log#add
        "function failure"
        (LBLOCK [
             STR failuretype;
             STR ". ";
             faddr#toPretty;
             STR ": ";
             p]);
      failedfunctions := faddr :: !failedfunctions
    end in
  begin
    (if (List.length fns_included) > 0 then
       List.iter
         (fun faddr ->
           let faddr =
             fail_tvalue
               (trerror_record
                  (LBLOCK [STR "analyze_arm:faddr: "; STR faddr]))
               (string_to_doubleword faddr) in
           let f =  arm_assembly_functions#get_function_by_address faddr in
           let _ = count := !count + 1 in
           try
             analyze_arm_function faddr f !count;
             pr_interval_timing [STR "functions analyzed: "; INT !count] 60.0
           with
	    | Failure s -> functionfailure "Failure" faddr (STR s)
	    | Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
	    | Internal_error s -> functionfailure "Internal error" faddr (STR s)
	    | Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
	    | CHFailure p -> functionfailure "CHFailure" faddr p
	    | BCH_failure p -> functionfailure "BCHFailure" faddr p) fns_included

     else
       arm_assembly_functions#bottom_up_itera
         (fun faddr f ->
           if List.mem faddr#to_hex_string fns_excluded then
             ()
           else if file_metrics#is_stable faddr#to_hex_string []
                   && (not !analyze_all) then
             arm_analysis_results#record_results ~save:false f
           else
             let _ = count := !count + 1 in
             try
               analyze_arm_function faddr f !count;
               pr_interval_timing [STR "functions analyzed: "; INT !count] 60.0
             with
	       | Failure s -> functionfailure "Failure" faddr (STR s)
	       | Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
	       | Internal_error s -> functionfailure "Internal error" faddr (STR s)
	       | Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
	       | CHFailure p -> functionfailure "CHFailure" faddr p
	       | BCH_failure p -> functionfailure "BCHFailure" faddr p));
    file_metrics#record_runtime ((Unix.gettimeofday ()) -. starttime)
  end


let analyze_pwr_function
      (faddr: doubleword_int) (f: pwr_assembly_function_int) (count: int) =
  let fstarttime = Unix.gettimeofday () in
  let finfo = load_function_info faddr in
  let _ =
    pverbose [
        STR "Analyze ";
        faddr#toPretty;
        STR " (started: ";
        STR (time_to_string fstarttime);
        STR ")";
        NL] in
  let _ = translate_pwr_assembly_function f in
  if pwr_chif_system#has_pwr_procedure faddr then
    let proc = pwr_chif_system#get_pwr_procedure faddr in
    begin
      bb_invariants#reset;
      analyze_procedure_with_intervals proc pwr_chif_system#get_pwr_system;
      analyze_procedure_with_linear_equalities proc pwr_chif_system#get_pwr_system;
      analyze_procedure_with_valuesets proc pwr_chif_system#get_pwr_system;
      analyze_procedure_with_reaching_defs proc pwr_chif_system#get_pwr_system;
      extract_ranges finfo bb_invariants#get_invariants;
      extract_reaching_defs finfo bb_invariants#get_invariants;
      extract_linear_equalities finfo bb_invariants#get_invariants;
      extract_valuesets finfo bb_invariants#get_invariants;
      finfo#reset_invariants;
      save_function_info finfo;
      save_function_invariants finfo;
      save_function_var_invariants finfo;
      pwr_analysis_results#record_results f;
      save_function_variables finfo;
      file_metrics#record_results
        faddr
        ((Unix.gettimeofday ()) -. fstarttime)
        (get_pwr_memory_access_metrics f finfo)
        (get_pwr_cfg_metrics f finfo#env)
    end
  else
    pr_debug [STR "Translation failed for "; faddr#toPretty; NL]


let analyze_pwr (starttime: float) =
  let fns_included = included_functions () in
  let fns_excluded = excluded_functions () in
  let count = ref 0 in
  begin
    (if (List.length fns_included) > 0 then
       List.iter
         (fun faddr ->
           let faddr =
             fail_tvalue
               (trerror_record
                  (LBLOCK [STR "analyze_pwr:faddr: "; STR faddr]))
               (string_to_doubleword faddr) in
           let f = pwr_assembly_functions#get_function_by_address faddr in
           let _ = count := !count + 1 in
           analyze_pwr_function faddr f !count) fns_included
     else
       pwr_assembly_functions#bottom_up_itera
         (fun faddr f ->
           if List.mem faddr#to_hex_string fns_excluded then
             ()
           else if file_metrics#is_stable faddr#to_hex_string []
                   && (not !analyze_all) then
             pwr_analysis_results#record_results ~save:false f
           else
             let _ = count := !count + 1 in
             try
               analyze_pwr_function faddr f !count;
               pr_interval_timing [STR "functions analyzed: "; INT !count] 60.0
             with
             | BCH_failure p ->
                raise (BCH_failure p)));
    file_metrics#record_runtime ((Unix.gettimeofday ()) -. starttime);
  end

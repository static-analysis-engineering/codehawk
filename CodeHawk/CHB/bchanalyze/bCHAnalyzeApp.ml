(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHFunctionInfo
open BCHMetrics
open BCHPreFileIO
open BCHSystemInfo
open BCHSystemSettings

(* bchlibx86 *)
open BCHAssemblyFunctions
open BCHDisassemble
open BCHIFSystem
open BCHLoopStructure
open BCHTranslateToCHIF
open BCHX86AnalysisResults   
open BCHX86Metrics

(* bchlibmips32 *)
open BCHMIPSAnalysisResults
open BCHMIPSCHIFSystem
open BCHMIPSAssemblyFunctions
open BCHMIPSMetrics
open BCHTranslateMIPSToCHIF

(* bchanalyze *)
open BCHAnalysisTypes
open BCHAnalyzeProcedure
open BCHExtractInvariants
open BCHFileIO
open BCHTrace

let analyze_all = ref false
let maxrelationalvarcomplexity = ref 150000.0
let maxrelationalloopcomplexity = ref 2000

let analyze_x86_function faddr f =
  let fstarttime = Unix.gettimeofday () in
  let finfo =  load_function_info faddr in
  let _ = pverbose [ STR "Analyze " ; faddr#toPretty ; STR  " (started: " ;
                     STR (time_to_string fstarttime) ; STR ")" ; NL ] in
  let _ = translate_assembly_function f in
  if chif_system#has_procedure_by_address faddr then
    let loopcomplexity = get_cfg_loop_complexity f in
    let varcomplexity = get_vc_complexity f finfo#env in
    let relational = varcomplexity <= !maxrelationalvarcomplexity &&
	               loopcomplexity <= !maxrelationalloopcomplexity in
    let proc = chif_system#get_procedure_by_address faddr in
    begin
      bb_invariants#reset ;
      analyze_procedure_with_intervals proc chif_system#get_system ;
      (if relational then
	 analyze_procedure_with_linear_equalities proc chif_system#get_system 
       else
         begin
	   chlog#add "skip relational analysis" faddr#toPretty ;
           pr_debug [ STR "skip LR analysis of " ; faddr#toPretty ; NL ]
         end) ;
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
    pr_debug [ STR "Translation failed" ; NL ]
 
let analyze starttime =
  let count = ref 0 in
  let failedfunctions = ref [] in
  let functionfailure failuretype faddr p =
    begin
      ch_error_log#add "function failure"
	(LBLOCK [ STR failuretype ; STR ". " ; faddr#toPretty ; STR ": " ; p ]) ;
      failedfunctions := faddr :: !failedfunctions
    end in

  begin
    assembly_functions#bottom_up_itera (fun faddr f ->
      let callees = get_app_callees faddr in
      let _ = List.iter (fun callee ->
	let cfinfo = get_function_info callee in
	if cfinfo#sideeffects_changed then
	  begin
	    (get_function_info faddr)#reset_invariants ;
	    chlog#add "reset invariants"
	      (LBLOCK [ faddr#toPretty ; STR " due to callee " ; callee#toPretty ])
	  end) callees in
      let appCallees = List.map (fun a -> a#to_hex_string) callees in
      if file_metrics#is_stable faddr#to_hex_string appCallees &&
	   (not !analyze_all) then
        x86_analysis_results#record_results ~save:false f
      else
	let _ = count := !count + 1 in
        try
          analyze_x86_function faddr f        
	with
	| Failure s -> functionfailure "Failure" faddr (STR s)
	| Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
	| Internal_error s -> functionfailure "Internal error" faddr (STR s)
	| Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
	| CHFailure p -> functionfailure "CHFailure" faddr p
	| BCH_failure p -> functionfailure "BCHFailure" faddr p ) ;

    let propstarttime = Unix.gettimeofday () in
    begin
      assembly_functions#top_down_itera (fun faddr f ->
	try
	  begin
	    f#iter_calls (fun _ floc ->
	      if floc#has_application_target then
		let tgtaddr = floc#get_application_target in
		let tgtfinfo = get_function_info tgtaddr in
		begin
		  save_function_info tgtfinfo
		end ) ;
	    save_function_summary (get_function_info faddr)
	  end
	with
	| Failure s -> functionfailure "Failure" faddr (STR s)
	| Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
	| Internal_error s -> functionfailure "Internal error" faddr (STR s)
	| Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
	| CHFailure p -> functionfailure "CHFailure" faddr p
	| BCH_failure p ->
	  ch_error_log#add "pushing arguments" (LBLOCK [ faddr#toPretty ; STR ": " ; p ])) ;
      file_metrics#record_propagation_time ((Unix.gettimeofday ()) -. propstarttime) ;
      file_metrics#record_runtime ((Unix.gettimeofday ()) -. starttime) ;
      (match !failedfunctions with
      | [] -> ()
      | l ->
	chlog#add "failed functions"
	  (LBLOCK (List.map (fun faddr -> LBLOCK [ faddr#toPretty ; NL ]) l)))
    end
  end

let analyze_mips_function faddr f =
  let fstarttime = Unix.gettimeofday () in
  let finfo = load_function_info faddr in
  let _ = pverbose [ STR "Analyze " ; faddr#toPretty ; STR " (started: " ;
                     STR (time_to_string fstarttime) ; STR ")" ; NL ] in
  let _ = translate_mips_assembly_function f in
  if mips_chif_system#has_mips_procedure faddr then
    let proc = mips_chif_system#get_mips_procedure faddr in
    begin
      bb_invariants#reset  ;
      analyze_procedure_with_intervals proc mips_chif_system#get_mips_system ;
      (if faddr#to_hex_string = "0x40c2f0" then
         pr_debug [ STR "skip LR analysis for 0x40c2f0" ; NL ]
       else
         analyze_procedure_with_linear_equalities proc mips_chif_system#get_mips_system) ;
      analyze_procedure_with_valuesets proc mips_chif_system#get_mips_system ;
      extract_ranges finfo bb_invariants#get_invariants ;
      extract_linear_equalities finfo bb_invariants#get_invariants ;
      extract_valuesets finfo bb_invariants#get_invariants ;
      finfo#reset_invariants ;
      save_function_info finfo ;
      save_function_invariants finfo ;
      save_function_type_invariants finfo ;
      mips_analysis_results#record_results f ;             
      save_function_variables finfo ;
      file_metrics#record_results
	~nonrel:false
	~reset:finfo#were_invariants_reset
 	faddr
	((Unix.gettimeofday ()) -. fstarttime)
        (get_mips_memory_access_metrics f finfo)
        (get_mips_cfg_metrics f finfo#env) ;
    end
  else
    pr_debug [ STR "Translation failed" ; NL ]
  
let analyze_mips starttime =
  let count = ref 0 in
  let failedfunctions = ref [] in
  let functionfailure failuretype faddr p =
    begin
      ch_error_log#add "function failure"
	(LBLOCK [ STR failuretype ; STR ". " ; faddr#toPretty ; STR ": " ; p ]) ;
      failedfunctions := faddr :: !failedfunctions
    end in
  begin
    mips_assembly_functions#bottom_up_itera
      (fun faddr f ->
        if file_metrics#is_stable faddr#to_hex_string [] &&
	     (not !analyze_all) then
          mips_analysis_results#record_results ~save:false f
        else
        let _ = count := !count + 1 in
        try
          analyze_mips_function faddr f
        with
        | Failure s -> functionfailure "Failure" faddr (STR s)
        | Invalid_argument s -> functionfailure "Invalid argument" faddr (STR s)
        | Internal_error s -> functionfailure "Internal error" faddr (STR s)
        | Invocation_error s -> functionfailure "Invocation error" faddr (STR s)
        | CHFailure p -> functionfailure "CHFailure" faddr p
        | BCH_failure p -> functionfailure "BCHFailure" faddr p ) ;
                         
    file_metrics#record_runtime ((Unix.gettimeofday ()) -. starttime) ;      
  end
           

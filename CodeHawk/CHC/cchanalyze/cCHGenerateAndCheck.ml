(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023-2024 Aarno Labs LLC

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
open CHAtlas
open CHCommon
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHTiming
open CHTimingLog

(* cchlib *)
open CCHBasicTypes
open CCHFileContract
open CCHSettings
open CCHUtilities

(* cchpre *)
open CCHPreFileIO
open CCHPreTypes
open CCHProofScaffolding

(* cchanalyze *)
open CCHAnalyze
open CCHAnalysisTypes
open CCHEnvironment
open CCHExpTranslator
open CCHExtractInvariantFacts
open CCHFunctionTranslator
open CCHInvariantStore
open CCHOperationsProvider
open CCHOrakel
open CCHPOChecker
open CCHPostCondition

module H = Hashtbl


let fenv = CCHFileEnvironment.file_environment

let function_to_be_analyzed = ref ""

let max_callcount = 100


type invariant_generation_spec_t = {
  ig_domain: string;
  ig_get_exp_translator:
    c_environment_int
    -> orakel_int
    -> exp_translator_int;
  ig_variable_type : variable_type_t;
  ig_get_function_translator:
    c_environment_int
    -> orakel_int
    -> operations_provider_int
    -> function_translator_int;
  ig_analysis:
    c_environment_int
    -> system_int
    -> domain_opsemantics_t
    -> (string, (string, atlas_t) H.t) H.t;
  ig_invariant_extractor:
    c_environment_int
    -> invariant_io_int
    -> (string, (string,atlas_t) H.t) H.t
    -> unit
}


let make_invariant_generation_spec t =
  match t with
    "linear equalities" -> {
      ig_domain = t;
      ig_get_exp_translator = get_num_exp_translator;
      ig_variable_type = NUM_VAR_TYPE;
      ig_get_function_translator = get_num_translator;
      ig_analysis = analyze_linear_equalities;
      ig_invariant_extractor = extract_external_value_facts
    }
  | "intervals" -> {
      ig_domain = t;
      ig_get_exp_translator = get_num_exp_translator;
      ig_variable_type = NUM_VAR_TYPE;
      ig_get_function_translator = get_interval_translator;
      ig_analysis = analyze_intervals;
      ig_invariant_extractor = extract_ranges
    }
  | "pepr" -> {
      ig_domain = t;
      ig_get_exp_translator = get_num_exp_translator;
      ig_variable_type = NUM_VAR_TYPE;
      ig_get_function_translator = get_num_translator;
      ig_analysis = analyze_pepr;
      ig_invariant_extractor = extract_pepr
    }
  | "valuesets" -> {
      ig_domain = t;
      ig_get_exp_translator = get_num_exp_translator;
      ig_variable_type = NUM_VAR_TYPE;
      ig_get_function_translator = get_valueset_translator;
      ig_analysis = analyze_valuesets;
      ig_invariant_extractor = extract_valuesets
    }
  | "symbolic sets" -> {
      ig_domain = t;
      ig_get_exp_translator = get_sym_exp_translator;
      ig_variable_type = SYM_VAR_TYPE;
      ig_get_function_translator = get_symbolicsets_translator;
      ig_analysis = analyze_symbols;
      ig_invariant_extractor = extract_symbols
    }
  | "state sets" -> {
      ig_domain = t;
      ig_get_exp_translator = get_sym_exp_translator;
      ig_variable_type = SYM_VAR_TYPE;
      ig_get_function_translator = get_statesets_translator;
      ig_analysis = analyze_statesets;
      ig_invariant_extractor = extract_states
    }
  | "sym_pointersets" -> {
      ig_domain = t;
      ig_get_exp_translator = get_sym_pointersets_exp_translator;
      ig_variable_type = SYM_VAR_TYPE;
      ig_get_function_translator = get_sym_pointersets_translator;
      ig_analysis = analyze_sym_pointersets;
      ig_invariant_extractor = extract_sym_pointersets
    }
  | _ -> raise (CCHFailure
                  (LBLOCK [ STR "Analysis option "; STR t;
			    STR " not recognized"]))


let process_function gspecs fname =
  let cfilename = system_settings#get_cfilename in
  try
    if !function_to_be_analyzed = fname || !function_to_be_analyzed = "" then
      let _ = log_info "analyze function %s [%s:%d]" fname __FILE__ __LINE__ in
      let fundec = read_function_semantics fname in
      let fdecls = fundec.sdecls in
      let _ = read_proof_files fname fdecls in
      let _ = read_api fname fdecls in
      let varmgr = read_vars fname fdecls in
      let invio = read_invs fname varmgr#vard in
      let spomanager = proof_scaffolding#get_spo_manager fname in
      let _ = spomanager#create_contract_proof_obligations in
      let proofObligations = proof_scaffolding#get_proof_obligations fname in
      let openpos = List.filter (fun po -> not po#is_closed) proofObligations in
      let _ =
        log_info
          "Obtained %d proof obligation(s) of which %d open [%s:%d]"
          (List.length proofObligations)
          (List.length openpos)
          __FILE__ __LINE__ in
      if (List.length openpos) > 0 then
        let _ =
          pr_timing [
              STR cfilename; STR ": ===analyze function=== "; STR fname;
              STR " with "; INT (List.length openpos); STR " open pos"] in
        let callcount = proof_scaffolding#get_call_count fname in
        let _ =
          List.iter
            (fun gspec ->
              if gspec.ig_domain = "sym_pointersets"
                 && callcount > max_callcount
              then
                ()
              else
	        try
	          let env = mk_c_environment fundec varmgr in
	          let orakel = get_function_orakel env invio in
	          let expTranslator = gspec.ig_get_exp_translator env orakel in
	          let opsProvider =
                    get_operations_provider
                      env expTranslator
                      proofObligations
	              gspec.ig_variable_type in
	          let functionTranslator =
                    gspec.ig_get_function_translator env orakel opsProvider in
	          let (optSem, sys) = functionTranslator#translate fundec in
                  (* let _ = pr_debug [sys#toPretty] in *)
	          let semantics =
                    match optSem with
                    | Some sem -> sem | _ -> default_opsemantics in
	          let invariants = gspec.ig_analysis env sys semantics in
                  begin
	            gspec.ig_invariant_extractor env invio invariants;
                    record_postconditions fname env invio;
                    pr_timing [
                        STR cfilename; STR ":"; STR fname;
                        STR ": Finished analyzing with domain ";
                        STR gspec.ig_domain]
                  end
	        with
	        | CCHFailure p | CHFailure p ->
                   begin
	             ch_error_log#add
                       "failure"
	               (LBLOCK [
                            STR "function ";
                            STR fname;
			    STR " (";
                            STR gspec.ig_domain;
                            STR "): ";
                            p]);
                     raise
                       (CCHFailure
                          (LBLOCK [
                               STR "CCHFailure in function ";
                               STR fname;
			       STR " (";
                               STR gspec.ig_domain;
                               STR "):";
                               p]))
                   end
	        | Invalid_argument s ->
                   begin
	             ch_error_log#add
                       "invalid argument"
	               (LBLOCK [
                            STR "function ";
                            STR fname;
                            STR " (";
                            STR gspec.ig_domain;
                            STR "):";
                            STR s]);
                     raise
                       (CCHFailure
                          (LBLOCK [
                               STR "Invalid argument in function ";
                               STR fname;
			       STR " (";
                               STR gspec.ig_domain;
                               STR "):";
                               STR s ]))
                   end
            | Failure s ->
               begin
	         ch_error_log#add
                   "failure"
	           (LBLOCK [ STR "function "; STR fname;
			     STR " ("; STR gspec.ig_domain; STR "):"; STR s ]);
                 raise (CCHFailure
                          (LBLOCK [ STR "Failure in function "; STR fname;
			            STR " ("; STR gspec.ig_domain; STR "):"; STR s ]))
               end
            | Division_by_zero ->
               begin
                 ch_error_log#add
                   "division-by-zero"
                   (LBLOCK [ STR "function "; STR fname;
                             STR " ("; STR gspec.ig_domain; STR ")" ]);
                 raise (CCHFailure
                          (LBLOCK [ STR "Failure in function "; STR fname;
                                    STR " ("; STR gspec.ig_domain; STR ")" ]))
               end
	    | Not_found ->
               begin
	         ch_error_log#add
                   "not-found"
	           (LBLOCK [ STR "function "; STR fname;
			     STR " ("; STR gspec.ig_domain; STR ") "  ]);
                 raise (CCHFailure
                          (LBLOCK [ STR "Not found in function "; STR fname;
			            STR " ("; STR gspec.ig_domain; STR "):" ]))
               end) gspecs in
      let fnApi = proof_scaffolding#get_function_api fname in
      let env = mk_c_environment fundec varmgr in
      begin
        check_proof_obligations env fnApi invio proofObligations;
        log_info "checked proof obligations [%s:%d]" __FILE__ __LINE__;
        save_invs fname invio;
        save_vars fname varmgr;
        save_proof_files fname;
        save_api fname;
      end
    else
      ()
  with
  | CCHFailure p ->
     begin
       ch_error_log#add
         "failure" (LBLOCK [ STR "function "; STR fname; STR ": "; p ]);
       ()
     end
  | Invalid_argument s ->
     begin
       ch_error_log#add
         "invalid argument"
         (LBLOCK [ STR "function "; STR fname; STR ": "; STR s ]);
       ()
     end
  | Not_found ->
     begin
       ch_error_log#add
         "not-found" (LBLOCK [ STR "function "; STR fname ]);
       ()
     end
  | Failure s ->
     begin
       ch_error_log#add
         "failure" (LBLOCK [ STR "function "; STR fname; STR ": "; STR s ]);
       raise (CCHFailure
                (LBLOCK [ STR "function "; STR fname; STR ": "; STR s ]))
     end
  | CHXmlReader.XmlParseError(line,col,p)
    | CHXmlDocument.XmlDocumentError(line,col,p) ->
     begin
       pr_debug [ STR "Xml error while generating invariants for function ";
                  STR fname; STR " ("; INT line; STR ","; INT col;
                  STR "): "; p; NL ];
       ch_error_log#add
         "xml error"
         (LBLOCK [ STR fname; STR " (";
                   INT line; STR ", "; INT col; STR "): "; p ]);
       raise (CHXmlDocument.XmlDocumentError(
                  line,col,
                  LBLOCK [ STR "xml error in function ";
                           STR fname; STR ": "; p ]))
     end


let generate_and_check_process_file (domains: string list) =
  let gspecs = List.map make_invariant_generation_spec domains in
  try
    let cfilename = system_settings#get_cfilename in
    let _ = read_cfile_dictionary () in
    let cfile = read_cfile () in
    let _ = fenv#initialize cfile in
    let _ = read_cfile_context () in
    let _ = read_cfile_predicate_dictionary () in
    let _ = read_cfile_interface_dictionary () in
    let _ = read_cfile_assignment_dictionary () in
    let _ = read_cfile_contract () in
    let _ = file_contract#collect_file_attributes in
    let _ = log_info "Read file-level xml files [%s:%d]" __FILE__ __LINE__ in
    let _ = pr_timing [STR cfilename; STR ": finished loading files"] in
    let functions = fenv#get_application_functions in
    let _ =
      pr_timing [
          STR cfilename;
          STR ": Analyzing ";
          INT (List.length functions);
          STR " functions"] in
    let _ =
      log_info "Processing %d functions [%s:%d]"
        (List.length functions) __FILE__ __LINE__ in
    let _ = List.iter (fun f -> process_function gspecs f.vname) functions in
    let _ = save_cfile_assignment_dictionary () in
    let _ = save_cfile_dictionary () in
    let _ = save_cfile_context () in
    let _ = save_cfile_interface_dictionary () in
    let _ = save_cfile_predicate_dictionary () in
    let _ = log_info "Saved file-level xml files [%s:%d]" __FILE__ __LINE__ in
    let _ = pr_timing [STR cfilename; STR ": finished saving files"] in
    ()
  with
  | CHXmlReader.IllFormed ->
     ch_error_log#add
       "ill-formed xml content for " (STR system_settings#get_cfilename)
  | CHXmlReader.XmlParseError(line, col, p)
    | CHXmlDocument.XmlDocumentError(line,col,p) ->
     begin
       pr_debug [
           STR "Xml error while generating invariants in file ";
           STR system_settings#get_cfilename;
           STR " (";
           INT line;
           STR ",";
           INT col; STR "): ";
           p;
           NL];
       ch_error_log#add
         "xml error"
         (LBLOCK [
              STR system_settings#get_cfilename;
              STR " (";
              INT line;
              STR ",";
              INT col;
              STR "): ";
              p]);
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Xml error while generating invariants in file ";
                 STR system_settings#get_cfilename;
                 STR " (";
                 INT line;
                 STR ",";
                 INT col;
                 STR "): ";
                 p;
                 NL]))
     end
  | CCHFailure p ->
     begin
       pr_debug [STR "Failure: "; p; NL];
       ch_error_log#add "failure" p
     end

(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
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
open CHPretty

(* chutil *)
open CHGc
open CHLogger
open CHTiming
open CHTimingLog
open CHXmlDocument

(* cchlib *)
open CCHVersion
open CCHFunctionSummary
open CCHSettings
open CCHUtilities

(* cchpre *)
open CCHCreatePrimaryProofObligations
open CCHInvariantFact
open CCHPreFileIO

(* cchanalyze *)
open CCHCheckValidity
open CCHGenerateAndCheck
open CCHGenerateLocalInvariants


let _ = CHPretty.set_trace_level 0

let cmds = [
    "version";
    "gc";
    "undefined-behavior-primary";
    "outputparameters-primary";
    "localinvs";
    "globalinvs";
    "check";
    "generate_and_check"]


let cmdchoices = String.concat ", " cmds


let cmd = ref "version"
let setcmd s = if List.mem s cmds then
    cmd := s
  else
    begin
      pr_debug [
          STR "Command ";
          STR s;
          STR " not recognized. Valid choices are: ";
	  pretty_print_list cmds (fun s -> STR s) "[" ", " "]";
          NL];
      exit 1
    end


let domains = ref []

let add_domain d = domains := d :: !domains


let set_domains s =
  String.iter (fun c -> match c with
  | 'l' -> add_domain linear_equalities_domain
  | 'v' -> add_domain valueset_domain
  | 'i' -> add_domain intervals_domain
  | 's' -> add_domain symbolic_sets_domain
  | 'p' -> add_domain sym_pointersets_domain
  | 'r' -> add_domain pepr_domain
  (* | 'x' -> add_domain "state sets" *)
  | _ ->
    begin
      pr_debug [
          STR "Some characters were not recognized in the domain specification: ";
	  STR s;
          NL];
      exit 1
    end) s


let speclist = [
  ("-version", Arg.Unit (fun () -> ()), "show version information and exit");
  ("-gc", Arg.Unit (fun () -> cmd := "gc"),
   "show ocaml garbage collector settings and exit");
  ("-summaries", Arg.String function_summary_library#add_summary_jar,
   "location of jar with library function summaries");
  ("-command", Arg.String setcmd, "choose action to perform: " ^ cmdchoices);
  ("-domains", Arg.String set_domains,
   "domains to be used in invariant generation: " ^
     "[l:lineq; v:valuesets; i:intervals; s:symbolicsets]");
  ("-cfilename", Arg.String system_settings#set_cfilename,
   "base filename of c source code file without extension");
  ("-cfilepath", Arg.String system_settings#set_cfilepath,
   "path relative to project path");
  ("-diagnostics", Arg.Unit (fun () -> activate_diagnostics ()),
   "collect diagnostics messages and save in diagnostics log");
  ("-disable_timing", Arg.Unit (fun () -> CHTiming.disable_timing ()),
   "disable printing timing log messages");
  ("-verbose", Arg.Unit (fun () -> system_settings#set_verbose true),
   "print status on proof obligations and invariants");
  ("-projectname", Arg.String system_settings#set_projectname,
   "name of the project (determines name of results directory)");
  ("-keep_system_includes",
   Arg.Unit (fun () -> system_settings#set_keep_system_includes true),
   "do not filter out functions in files with absolute path names");
  ("-unreachability", Arg.Unit (fun () -> system_settings#set_use_unreachability),
   "use unreachability as a justification for discharging proof obligations");
  ("-wordsize", Arg.Int system_settings#set_wordsize,
   "set word size (e.g., 16, 32, or 64)");
  ("-contractpath", Arg.String system_settings#set_contractpath,
   "path to contract files")
]

let usage_msg = "chc_analyze <options> <path to analysis directory>"

let read_args () = Arg.parse speclist system_settings#set_targetpath usage_msg


let save_log_files (contenttype:string) =
  begin
    save_logfile ch_info_log contenttype "infolog";
    append_to_logfile ch_error_log contenttype "errorlog";
    save_logfile chlog contenttype "chlog";
    (if collect_diagnostics () then
       save_logfile ch_diagnostics_log contenttype "ch_diagnostics_log")
  end


let main () =
  try
    let _ = set_log_level "WARNING" in
    let _ = read_args () in
    let _ = chlog#set_max_entry_size 1000 in
    let _ = log_info "AIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAIAI" in
    let cfilename = system_settings#get_cfilename in
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

    else if !cmd = "undefined-behavior-primary" then
      begin
	primary_process_file ();
        log_info "primary proof obligations generated [%s:%d]" __FILE__ __LINE__;
	save_log_files "primary";
        log_info
          "primary proof obligations log files saved [%s:%d]" __FILE__ __LINE__
      end

    else if !cmd = "outputparameters-primary" then
      begin
        system_settings#set_output_parameter_analysis;
	let _ =
          CCHCreateOutputParameterPOs.output_parameter_po_process_file () in
        log_info "primary proof obligations generated [%s:%d]" __FILE__ __LINE__;
	save_log_files "primary";
        log_info
          "primary proof obligations log files saved [%s:%d]" __FILE__ __LINE__
      end

    else if !cmd = "localinvs" then
      begin
	invariants_process_file (List.rev !domains);
        log_info "Local invariants generated [%s:%d]" __FILE__ __LINE__;
	save_log_files "localinvs";
        log_info
          "Local invariant generation log files saved [%s:%d]" __FILE__ __LINE__
      end

    else if !cmd = "globalinvs" then ()

    else if !cmd = "check" then
      begin
	check_process_file ();
        log_info "Proof obligations checked [%s:%d" __FILE__ __LINE__;
	save_log_files "check";
        log_info
          "Proof obligation checking log files saved [%s:%d]" __FILE__ __LINE__
      end

    else if !cmd = "generate_and_check" then
      match generate_and_check_process_file (List.rev !domains) with
      | Error e ->
         let msg = STR (String.concat "; " e) in
         begin
           ch_error_log#add "generate-and-check-failure" msg;
           pr_debug [msg; NL];
           exit 1
         end
      | _ ->
         begin
           pr_timing [STR cfilename; STR ": finished generate_and_check"];
           log_info
             "Invariants generated and proof obligations checked [%s:%d]"
             __FILE__ __LINE__;
           save_log_files "gencheck";
           log_info
             ("Invariant generation and proof obligation check log files saved [%s:%d]")
             __FILE__ __LINE__;
           pr_timing [STR cfilename; STR ": finished saving log files"]
         end

    else
      begin
	pr_debug [STR "Command "; STR !cmd; STR " not recognized"; NL];
	exit 1
      end

  with
  | CHXmlReader.XmlParseError (line,col,p)
  | CCHFunctionSummary.XmlReaderError (line,col,p)
  | XmlDocumentError (line,col,p) ->
     let msg =
       LBLOCK [
           STR "Xml error: ("; INT line; STR ", "; INT col; STR "): "; p] in
     begin
       ch_error_log#add "final failure" msg;
       pr_debug [msg; NL];
       save_log_files "failure";
       exit 3
    end

  | CHCommon.CHFailure p
  | CCHFailure p ->
     begin
       ch_error_log#add "final failure" p;
       save_log_files "failure";
       pr_debug [STR "Failure: "; p; NL];
       exit 1
     end

  | Invalid_argument s ->
     begin
       ch_error_log#add
         "final failure" (LBLOCK [STR "Invalid argument: "; STR s]);
       save_log_files "failure";
       pr_debug [STR "Error: "; STR s; NL];
       exit 1
     end

  | _ ->
     begin
       save_log_files "failure";
       pr_debug [STR "Unknown error encountered"; NL];
       exit 1
     end


let _ = Printexc.print main ()

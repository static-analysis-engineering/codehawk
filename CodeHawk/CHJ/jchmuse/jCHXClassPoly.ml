(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny Sipma

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
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHFile
open JCHRawClass

(* jchpre *)
open JCHApplication
open JCHClassLoader
open JCHMethodAssumptions
open JCHIFSystem
open JCHPreFileIO
open JCHSystemSettings

(* jchsys *)
open JCHLoopUtils

let classname = ref ""
let methodname = ref ""
let printbytecode = ref false
let analysis_level = ref 1        (* complexity of analysis : so far there are 3 levels that are considered 0 for stac, 1 and 3 for muse *)
let use_overflow = ref true       (* if false, overflow is ignored *)
let joins = ref 2                 (* number of joins before widening *)
let maxcoeff = ref 100            (* maximum coefficient in constraint *)
let maxconstraints = ref 20       (* maximum number of constraints in polyhedron *)

let chanalyzer = "CodeHawk Java Class Analyzer (MUSE)" 
let versioninfo = "0.3 (April 29, 2016)"

let speclist = [
  ("-summaries", Arg.String system_settings#add_summary_classpath_unit,"summary jar file") ;
  ("-classpath", Arg.String system_settings#add_classpath_unit, "sets java classpath") ;
  ("-printbytecode", Arg.Set printbytecode, "prints the bytecode") ;
  ("-method", Arg.String (fun s -> methodname := s), "report invariants for this method only");
  ("-joins", Arg.Int (fun i -> joins := i), "number of joins before widening") ;
  ("-maxcoeff", Arg.Int (fun i -> maxcoeff := i),
   "maximum coefficient in constraint (default 100)") ;
  ("-maxconstraints", Arg.Int (fun i -> maxconstraints := i),
   "maximum number of constraints in polyhedron (default 20)"); 
  ("-analysislevel", Arg.Int (fun i -> analysis_level := i),
   "limit number of variables to be used in constraints (default 1: 2 variables/constraint), other option: 3 (3 variables/constraint)") ;
   ("-disable_overflow", Arg.Unit (fun () -> use_overflow := false),
    "assume unbounded integers rather than 32 bit integers")
]

let is_file f =
  try
    (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _,_) -> false

let usage_message = 
  "\n" ^ (string_repeat "-~" 40) ^
    "\n" ^ chanalyzer ^ " " ^ versioninfo ^ 
    "\n" ^ (string_repeat "-~" 40) ^
    "\n\nInvoke with" ^
    "\n   chj_invariants <class file>" ^
    "\n\nOptional arguments:" ^
    "\n   -joins: the number of joins before widening (default 8)" ^
    "\n   -maxcoeff: the maximum coefficient in a constraint (default 100)" ^
    "\n   -maxconstraints: the maximum number of constraints per polyhedron (default 10)" ^
    "\n"


let usage_msg = "chj_invariants classname"
let read_args () = Arg.parse speclist   (fun s -> classname := s) usage_msg

let has_invariants invs =
  List.exists (fun (_,l) -> match l with [] -> false | _ -> true) invs

let report_invariants starttime cInfo = 
  let results  = List.fold_left (fun acc ms ->
    if !methodname = "" || ms#name = !methodname then
      let cms = make_cms cInfo#get_class_name ms in
      let mInfo = app#get_method cms in
      let _ = if !printbytecode then pr_debug [ mInfo#bytecode_to_pretty ] in
      let jproc = JCHSystem.jsystem#get_jproc_info_seq_no mInfo#get_index in
      let pcresults = jproc#get_analysis_results#get_pc_analysis_results#listOfPairs in
      let invs = List.map (fun (pc,pca) -> (pc,pca#get_invariants)) pcresults in
      (cms, invs) :: acc
    else
      acc) [] cInfo#get_methods_defined in
  save_invariants_report_acl2 versioninfo cInfo#get_class_name starttime results
    
let load () =
  if Filename.check_suffix !classname "class" then
    if is_file !classname then
      let ch = IO.input_channel (open_in_bin !classname) in
      let md5 = Digest.file !classname in
      let origin = !classname in
      let c = JCHParse.parse_class_low_level ch origin md5 in
      let _ = IO.close_in ch in
      begin
	app#add_class (JCHRaw2IF.low2high_class c) ;
	c.rc_name
      end
    else
      raise (JCH_failure (LBLOCK [ STR "Error: " ; STR !classname ; STR " not found" ]))
  else
    let cname = make_cn !classname in
    begin
      load_class (get_class system_settings#get_classpath cname) ;
      cname
    end

let get_assumptions (cn:class_name_int) =
  let filename = get_assumptions_filename cn in
  if Sys.file_exists filename then
    read_xml_method_assumptions_file cn
  else
    begin save_xml_method_assumptions_file cn ; [] end


let main () =
  try
    let _ = read_args () in
    let starttime = Unix.gettimeofday () in
    let cn = load () in
    let _ = process_classes () in
    if app#has_class cn then
      let cInfo = app#get_class cn in
      let assumptions = get_assumptions cn in
      let _ = List.iter (fun (cms,l) ->
	let mInfo = app#get_method cms in
	List.iter mInfo#add_argument_assumption l) assumptions in
      begin
	let _ = translate_base_system  () in
	JCHAnalysis.analyze_system 
	  ~analysis_level:!analysis_level
	  ~use_intervals:false
	  ~number_joins:!joins 
	  ~max_poly_coeff:!maxcoeff
	  ~max_nb_constraints:!maxconstraints 
	  ~use_time_limits:false
	  ~poly_analysis_time_limit:100
	  ~num_analysis_time_limit:500
	  ~use_overflow:!use_overflow;
	report_invariants starttime cInfo ;
      end
    else
      pr_debug [STR "Class "; STR !classname; STR " could not be loaded"; NL]
  with
  | CHFailure p | JCH_failure p ->
    pr_debug [ STR "Error in processing class: " ; p ; NL ]
  | JCH_runtime_type_error p ->
    pr_debug [ STR "Runtime type error in byte code: " ; p ; NL ]
  | JCHFile.No_class_found s ->
    pr_debug [ STR "Error: Class " ; STR s ; STR " could not be found " ; NL ]

let _ = Printexc.print main ()

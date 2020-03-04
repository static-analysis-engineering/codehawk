(* =============================================================================
   CodeHawk Java Analyzer
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

(** ----------------------------------------------------------------------------- 
   Reads in all application jars, creates a dictionary of class names, field,
   and method signatures and saves this dictionary to an xml file, named
   <output_directory>/<project_name>_dictionary.xml .
   ----------------------------------------------------------------------------- *)

(* chlib *)
open CHCommon
open CHIntervals
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHCallgraphBase
open JCHClassUserTemplate
open JCHCHAUtil
open JCHClassLoader
open JCHIFSystem
open JCHLoops
open JCHMethodImplementations
open JCHPreAPI
open JCHPreFileIO
open JCHAnalysisResults
open JCHSystemSettings
open JCHUserData

(* jchpoly *)
open JCHNumericAnalysis

(* jchcost *)
open JCHCostBoundsModel

let versioninfo = "1.0 (March 3, 2020)"

(* --------   alternative analysis options ---------- *)              
let create_model = ref false
let scan_only = ref false
let translate_only = ref false
let analyze_taint = ref false
let analyze_taint_origins = ref false
(* --------------------------------------------------- *)
                          
let save_summaries = ref true
let analyze_loops = ref true
let save_loops = ref true
let print_version = ref false
let intervals_only = ref false
let joins = ref 2                 (* number of joins before widening *)
let maxcoeff = ref 100            (* maximum coefficient in constraint *)
let maxconstraints = ref 10       (* maximum number of constraints in polyhedron *)
let constraint_analysis_time_limit = ref 20
let numeric_analysis_time_limit = ref 200
let taint_origin_ind = ref (-1)
let use_symbolic_defaults = ref true
let dbg = ref false

let _ = chlog#set_max_entry_size 10000
let _ = ch_error_log#set_max_entry_size 1000

let speclist = [
  ("-scan_only", Arg.Set scan_only, "determine number of methods") ;
  ("-translate_only", Arg.Set translate_only, "only translate to chif") ;
  ("-trace_utf8_signatures",
   Arg.Unit (fun () -> JCHParseUTF8Signature.activate_tracing ()),
   "collect signature strings parsed") ;
  ("-taint",
   Arg.Set analyze_taint,
   "perform taint analysis (to be performed after numerical analysis)");
  ("-taintorigin",
   Arg.Int (fun i -> taint_origin_ind := i; analyze_taint_origins := true),
   "perform taint-origin analysis (to be performed after taint analysis). ");
  ("-costmodel", Arg.Set create_model, "create a cost model") ;  
  ("-summaries",
   Arg.String system_settings#add_summary_classpath_unit,
   "summary jar file") ;
  ("-classpath", Arg.String system_settings#add_classpath_unit, "sets java classpath") ;
  ("-jars", Arg.Rest app#add_application_jar, "jar files that make up the project") ;
  ("-intervals_only", Arg.Set intervals_only, "non-relational analysis only");
  ("-joins", Arg.Int (fun i -> joins := i), "number of joins before widening");
  ("-maxcoeff", Arg.Int (fun i -> maxcoeff := i),
   "maximum coefficient in constraint (default 100)") ;
  ("-maxconstraints", Arg.Int (fun i -> maxconstraints := i),
   "maximum number of constraints in polyhedron (default 10)") ;
  ("-constraint_time_limit", Arg.Int (fun i -> constraint_analysis_time_limit := i),
   "constraint analysis time limit (default 20)") ;
  ("-numeric_time_limit",
   Arg.Int (fun i ->
       pr_debug [STR "set_numeric_analysis_time_limit"; NL];
       numeric_analysis_time_limit := i),
   "numeric analysis time limit (default 200)") ;
  ("-distinguish_taint_top_targets",
   Arg.Unit (fun () -> JCHTaintOrigin.set_use_one_top_target false),
   "represent unknown method calls as separate taint top targets");
  ("-use_symbolic_defaults",
   Arg.Set use_symbolic_defaults,
   "use default symbolic constants rather than constants for method calls");  
  ("-cost_time_limit", Arg.Float (fun m -> JCHCostUtils.set_max_cost_analysis_time m),
   "cost analysis time limit for every method (float)");
  ("-version", Arg.Set print_version, "print version information and return");
  ("-dbg", Arg.Unit (fun () -> JCHPrintUtils.set_dbg_on ()), "print debugging info");
  ("-exclude_pkg_prefix", Arg.String system_settings#add_pkg_exclude,
   "skip classes with given package prefix") ;
  ("-verbose", Arg.Unit (fun () -> system_settings#set_verbose),"show intermediate results")
]

let usage_message = 
    "\nCodeHawk Java Analyzer for Complexity Analysis " ^ versioninfo ^
      "\n" ^ (string_repeat "-~" 40)
      ^ "\n\nInvoke with"
      ^ "\n   chj_initialize -summaries jdk.jar -jars <jar files>, or"
      ^ "\n   chj_initialize -scan_only -summaries jdk.jar -jars <jar files>, or"
      ^ "\n   chj_initialize -costmodel -summaries jdk.jar -jars <jar files>, or"
      ^ "\n   chj_initialize -taint -summaries jdk.jar -jars <jar files>, or"
      ^ "\n   chj_initialize -taintorigin <taint origin index> -summaries jdk.jar -jars <jar file>, or"
      ^ "\n   chj_initialize -version"
      ^ "\n\nOptional arguments (for the first case only):"
      ^ "\n   -intervals_only: only use intervals in the analysis"
      ^ "\n   -joins: the number of joins before widening (default 3)"
      ^ "\n   -maxcoeff: the maximum coefficient in a constraint (default 100)"
      ^ "\n   -maxconstraints: the maximum number of constraints per polyhedron (default 10)"
      ^ "\n   -constraint_time_limit: time limit for the polyhedra analysis (default 20 seconds)"
      ^ "\n   -numeric_time_limit: time limit for the numeric analysis (default 200 seconds)"
      ^ "\n"

let read_args () = Arg.parse speclist (fun s -> ()) usage_message

let trail_to_graph v trail =
  let result = ref [] in
  let l = trail#listOfPairs in
  let _ = List.iter (fun (torigin,ttable) ->
    let _ = pr_debug [ torigin#toPretty ; NL ] in
    let ll = ttable#listOfPairs in
    List.iter (fun (tnode, tnodeset) ->
      if tnode#is_var then
	tnodeset#iter (fun ttnode -> 
	  if ttnode#is_var then result := (tnode#get_var, ttnode#get_var) :: !result)) ll) l in
  !result
  
let save_numeric_analysis_results cInfo =
  let cInfoResults = init_class_analysis_results cInfo in
  begin
    List.iter (fun ms ->
      let cms = make_cms cInfo#get_class_name ms in
      let mInfo = app#get_method cms in
      if mInfo#has_bytecode then
	try
	  let jproc = JCHSystem.jsystem#get_jproc_info_seq_no cms#index in
	  let pcresults = jproc#get_analysis_results#get_pc_analysis_results#listOfPairs in
	  let invs = List.map (fun (pc,pca) -> (pc,pca#get_invariants)) pcresults in
	  let loops = List.map (fun wto -> wto#get_loop_info ()) jproc#get_wto_infos in
	  begin
	    cInfoResults#set_method_invariants cms#index invs ;
	    cInfoResults#set_method_loops cms#index loops 
	  end
	with
	  JCH_failure p -> 
	    pr_debug [ STR "Error in retrieving analysis results for " ; cms#toPretty ; 
		       STR ": " ; p ; NL ]) 
      cInfo#get_methods_defined ;
    cInfoResults#save_xml_class ;
    save_xml_class_cost_support cInfo ;
  end

let save_taint_analysis_results cInfo =
  let cInfoResults = init_class_analysis_results cInfo in
  let save_m_results ms =
    let cms = make_cms cInfo#get_class_name ms in
    let mInfo = app#get_method cms in
    if mInfo#has_bytecode then
      try
	let jproc = JCHSystem.jsystem#get_jproc_info_seq_no cms#index in
	let pcresults = jproc#get_analysis_results#get_pc_analysis_results#listOfPairs in
	let taints = List.map (fun (pc,pca) -> (pc,pca#get_taint_origins)) pcresults in
	let returnorigins = jproc#get_analysis_results#get_return_origins in
	begin
	  cInfoResults#set_method_taint_origins cms#index taints ;
	  cInfoResults#set_method_return_origins cms#index returnorigins ;
	end
      with
	JCH_failure p -> 
	  pr_debug [ STR "Error in retrieving analysis results for " ; cms#toPretty ; 
		     STR ": " ; p ; NL ] in
  List.iter save_m_results cInfo#get_methods_defined 

let collect_utf8_parsed_strings () =
  let results = JCHParseUTF8Signature.get_utf8_parsed_strings () in
  List.iter
    (fun (ty,l) ->
      begin
        pr_debug [ NL ; STR ty ; NL ] ;
        List.iter
          (fun (s,p) -> pr_debug [ INDENT(3, LBLOCK [ STR s ; STR ": " ; p ; NL ]) ]) l
      end) results
  
    
let main () =
  try
    let start = Unix.gettimeofday() in
    let _ = read_args () in

    (* -------------------------------------------------------------------- *
     * version info                                                         *
     * -------------------------------------------------------------------- *)
    if !print_version then
      begin
	pr_debug [ JCHVersion.version#toPretty ; NL ] ;
	exit 0
      end

    (* -------------------------------------------------------------------- *
     * scanning only                                                        *
     * -------------------------------------------------------------------- *)
    else if !scan_only then
      match app#get_application_jars with
      |[] -> pr_debug [ STR "=== Error: No jars were specified. === " ; NL ;
			STR "Please indicate the jars to be loaded with the " ;
                        STR "-jars command-line option" ; NL ]
      | l ->
         try
           let xcludes = system_settings#get_pkg_excludes in
	   let _ = set_permissive true in
	   let classnames = 
	     List.fold_left (fun acc jar ->
                 (load_classes_in_jar ~xcludes jar) @ acc) [] l in
	   let _ = process_classes () in
           let _ =
             List.iter (fun c ->
                 match c#get_bootstrap_methods with
                 | [] -> ()
                 | l ->
                    begin
                      List.iteri (fun i m ->
                          begin
                            pr_debug [ STR "  " ; INT i ; STR ": " ;  m#toPretty ; NL ] ;
                            (match m#get_lambda_function with
                             | Some (ot,ms) ->
                                pr_debug [ STR "   ---> Lambda function: " ;
                                           object_type_to_pretty ot ; STR ": " ;
                                           ms#toPretty ; NL ]
                             | _ -> ())
                          end) l
                    end) app#get_classes in
	   let bcmethods = List.filter (fun m -> m#has_bytecode) app#get_methods in
           let _ =
             if system_settings#is_verbose then
               pr_debug (List.map (fun cn -> LBLOCK [ cn#toPretty ; NL ]) classnames) in
	   begin
	     pr_debug [ STR "Methods with bytecode: " ;
                        INT (List.length bcmethods) ; NL ];
             pr_debug [ STR "Classes loaded       : " ;
                        INT (List.length classnames) ; NL ] ;
	     set_main_method () ;
	     method_signature_implementations#initialize ;          
	     set_method_targets () ;
	     callgraph_base#build_graph ;
	     save_classnames classnames ;
	     save_signature_file () ;
	     save_callgraph_file () ;
	     save_dictionary () ;           
	     save_missing_classes () ;
	     save_log_files "scanlog" 
	   end
        with
        | JCHParseUTF8Signature.UTF8ParseError p ->
           pr_debug [ STR "UTF8 Parse error: " ; p ; NL ]

    (* -------------------------------------------------------------------- *
     * translation to CHIF only                                             *
     * -------------------------------------------------------------------- *)
    else if !translate_only then
      match app#get_application_jars with
      |[] -> pr_debug [ STR "=== Error: No jars were specified. === " ; NL ;
			STR "Please indicate the jars to be loaded with the " ;
                        STR "-jars command-line option" ; NL ]
      | l ->
	let _ = JCHBasicTypes.set_permissive true in
	let classnames = 
	  List.fold_left (fun acc jar -> (load_classes_in_jar jar) @ acc) [] l in
	let _ = process_classes () in
	let bcmethods = List.filter (fun m -> m#has_bytecode) app#get_methods in
        try
	  begin
	    pr_debug [ STR "Methods with bytecode: " ; INT (List.length bcmethods) ; NL ];
	    set_main_method () ;
	    set_method_targets () ;
	    method_signature_implementations#initialize ;
	    callgraph_base#build_graph ;
	    save_classnames classnames ;
	    save_dictionary () ;
	    save_signature_file () ;
	    save_callgraph_file () ;
	    save_missing_classes () ;
	    save_log_files "translatelog"  ;
            ignore (translate_base_system ())
	  end
        with
        | JCHParseUTF8Signature.UTF8ParseError p ->
           pr_debug [ STR "UTF8 Parse error: " ; p ; NL ]

    (* -------------------------------------------------------------------- *
     * create cost model                                                    *
     * -------------------------------------------------------------------- *)
    else if !create_model then
      match app#get_application_jars with
      |[] -> pr_debug [ STR "=== Error: No jars were specified. === " ; NL ;
			STR "Please indicate the jars to be loaded with the " ;
                        STR "-jars command-line option" ; NL ]
      | l ->
         if not (has_stac_analysis_dir ()) then
           pr_debug [ STR "=== Error: Numerical analysis results not found. ===" ; NL ;
                      STR "Please run the numerical analysis first before " ;
                      STR "creating the cost model" ; NL ]
         else
	   let _ = JCHBasicTypes.set_permissive true in
           let xcludes = system_settings#get_pkg_excludes in
	   begin
	     JCHAnalysisUtils.numeric_params#set_create_model true;
	     read_dictionary () ;
             read_jt_dictionary () ;
             read_taint_origins () ;
	     List.iter (fun jar -> ignore(load_classes_in_jar ~xcludes jar)) l ;
	     pr_debug [ STR "Start processing classes ..." ; NL ] ;
	     process_classes () ;
	     pr_debug [ STR "Start loading default cost data files ..." ; NL ] ;
	     load_defaultcostdata_file () ;
	     pr_debug [ STR "Creating cost models ..." ; NL ] ;
	     pr_debug [ STR "Start initializing method signature implementation ..." ; NL ] ;
	     method_signature_implementations#initialize ;
             load_user_class_files () ;                          
             pr_debug [ STR "User-provided data: " ; NL ; userdata#toPretty ; NL ] ;
	     read_callgraph_file () ;
             JCHNumericAnalysis.load_xml_class_cost_support ();
	     pr_debug [ STR "Creating cost models ..." ; NL ] ;
	     JCHCostBoundsAnalysis.create_bounds_cost_model !use_symbolic_defaults ; 
	     save_log_files "costlog" ;
             save_jt_dictionary () ;
             save_timecost_diagnostics () ;
	   end

    (* -------------------------------------------------------------------- *
     * compute taint                                                        *
     * -------------------------------------------------------------------- *)
    else if !analyze_taint then
      match app#get_application_jars with
      |[] -> pr_debug [ STR "=== Error: No jars were specified. === " ; NL ;
			STR "Please indicate the jars to be loaded with the " ;
                        STR "-jars command-line option" ; NL ]
      | l ->
         if not (has_stac_analysis_dir ()) then
           pr_debug [ STR "=== Error: Numerical analysis results not found. ===" ; NL ;
                      STR "Please run the numerical analysis first before " ;
                      STR "doing taint analysis" ; NL ]
         else
	   let _ = JCHBasicTypes.set_permissive true in
           let xcludes = system_settings#get_pkg_excludes in
	   begin
	     JCHAnalysisUtils.numeric_params#set_create_model true;
	     read_dictionary () ;
             read_jt_dictionary () ;
             read_taint_origins () ;
	     List.iter (fun jar -> ignore(load_classes_in_jar ~xcludes jar)) l ;
	     pr_debug [ STR "Start processing classes ..." ; NL ] ;
	     process_classes () ;
             method_signature_implementations#initialize ;
             load_user_class_files () ;             
             read_callgraph_file () ;
             set_main_method () ;
             set_method_targets () ;
	     JCHSystemUtils.start_timing();
	     ignore (translate_base_system ()) ;
	     JCHSystemUtils.add_timing "translate base system";
             pr_debug [ STR "Start taint analysis ... " ; NL ] ;
	     JCHNumericAnalysis.load_xml_class_cost_support () ;
	     JCHAnalysis.analyze_taint ();
	     List.iter (fun cInfo -> 
	       if cInfo#is_stubbed || cInfo#is_missing then () 
	       else save_taint_analysis_results cInfo)
	       app#get_classes ;
             JCHSystemUtils.add_timing "save analysis results" ;
	     save_taint_origins () ;
             JCHSystemUtils.add_timing "save taint origins" ;
             save_log_files "taint"
           end

    (* -------------------------------------------------------------------- *
     * compute taint origins                                                *
     * -------------------------------------------------------------------- *)
    else if !analyze_taint_origins then
      match app#get_application_jars with
      |[] -> pr_debug [ STR "=== Error: No jars were specified. === " ; NL ;
			STR "Please indicate the jars to be loaded with the " ;
                        STR "-jars command-line option" ; NL ]
      | l ->
         if not (has_stac_analysis_dir ()) then
           pr_debug [ STR "=== Error: Numerical analysis results not found. ===" ; NL ;
                      STR "Please run the numerical analysis and taint analysis " ;
                      STR "before doing taint origin analysis" ; NL ]
         else
	   let _ = JCHBasicTypes.set_permissive true in
           let xcludes = system_settings#get_pkg_excludes in
	   begin
	     JCHAnalysisUtils.numeric_params#set_create_model true;
	     read_dictionary () ;
             read_jt_dictionary () ;
             read_taint_origins () ;
	     List.iter (fun jar -> ignore(load_classes_in_jar ~xcludes jar)) l ;
	     pr_debug [ STR "Start processing classes ..." ; NL ] ;
	     process_classes () ;
             method_signature_implementations#initialize ;
             load_user_class_files () ;             
             read_callgraph_file () ;
             set_main_method () ;
             set_method_targets () ;
	     JCHSystemUtils.start_timing();
	     ignore (translate_base_system ()) ;
	     JCHSystemUtils.add_timing "translate base system";
             pr_debug [ STR "Start taint analysis ... " ; NL ] ;
	     JCHNumericAnalysis.load_xml_class_cost_support () ;
	     let local_vars_only = true in
             JCHAnalysis.analyze_taint_origins !taint_origin_ind local_vars_only (*None None*) ;
             save_taint_origins () ;
             save_log_files "taint"
           end
    else

    (* -------------------------------------------------------------------- *
     * numeric analysis                                                     *
     * -------------------------------------------------------------------- *)
      match app#get_application_jars with
      |[] -> pr_debug [ STR "=== Error: No jars were specified. === " ; NL ;
			STR "Please indicate the jars to be loaded with " ;
                        STR "the -jars command-line option" ; NL ]
      | l ->
	 let _ = JCHBasicTypes.set_permissive true in
         let xcludes = system_settings#get_pkg_excludes in
	let classnames = 
	  List.fold_left (fun acc jar ->
              (load_classes_in_jar ~xcludes jar) @ acc) [] l in
	begin
	  JCHAnalysisUtils.numeric_params#set_create_model false;
	  process_classes () ;
	  set_main_method () ;
	  method_signature_implementations#initialize ;
          load_user_class_files () ;          
	  set_method_targets () ;          
	  callgraph_base#build_graph ;
	  save_classnames classnames ;
	  save_dictionary () ;
	  save_signature_file () ;
	  save_callgraph_file () ;
	  save_missing_classes () ;
	  save_log_files "loading" ;   (* save log files before analysis *)
	  JCHSystemUtils.start_timing();
	  ignore (translate_base_system ()) ;
	  JCHSystemUtils.add_timing "translate base system";
	  JCHAnalysis.analyze_system 
	    ~analysis_level:0
            ~use_intervals:!intervals_only 
	    ~number_joins:!joins 
	    ~max_poly_coeff:!maxcoeff 
	    ~max_nb_constraints:!maxconstraints 
	    ~use_time_limits:true 
	    ~poly_analysis_time_limit:!constraint_analysis_time_limit 
	    ~num_analysis_time_limit:!numeric_analysis_time_limit
            ~use_overflow:true ;
	  List.iter (fun cInfo -> 
	    if cInfo#is_stubbed || cInfo#is_missing then
	      () 
	    else save_numeric_analysis_results cInfo
	    ) app#get_classes ;
          JCHSystemUtils.add_timing "save analysis results" ;
          save_jt_dictionary () ;
          save_callgraph_file () ;
          save_dictionary () ;          
	  save_log_files "numerical" ;   (* save log files after analysis *)
          JCHSystemUtils.add_timing "save log files" ;
	  pr_debug [ STR "Time: " ; 
		     STR (Printf.sprintf "%.4f" ((Unix.gettimeofday()) -. start)) ; NL ]
	end
 with
  | JCH_failure p ->
    begin
      pr_debug [ STR "JCH_failure: " ; p ; NL ] ;
      save_log_files "failurelog" ;
      exit(1)
    end
  | JCH_class_structure_error p ->
     begin
       pr_debug [ STR "Error in class structure: " ; p ; NL ] ;
       save_log_files "failurelog" ;
       exit (1)
     end
  | CHFailure p ->
     begin
       pr_debug [ STR "CHFailure: " ; p ; NL ] ;
       save_log_files "failurelog" ;
       exit(1)
     end
  | Failure s ->
    begin
      pr_debug [ STR "Failure: " ; STR s ; NL ] ;
      save_log_files "failurelog" ;
      exit(1)
    end
  | XmlDocumentError (line,col,p)
    | CHXmlReader.XmlParseError (line,col,p) ->
     begin
       pr_debug [ STR "Xml error at (" ; INT line ; STR "," ; INT col ;
                  STR "): " ; p ; NL ] ;
       save_log_files "failurelog" ;
       exit(1)
     end

  | Exit ->
     begin
       save_log_files "costfailurelog" ;
       exit(1)
     end
      
let _ = Printexc.print main ()
  
  

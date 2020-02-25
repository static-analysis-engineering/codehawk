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

(* chlib *)
open CHPretty

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHFile
open JCHRawClass

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHCHAUtil
open JCHCallgraphBase
open JCHClassAnalysis
open JCHClassInfo
open JCHFunctionSummary
open JCHFunctionSummaryLibrary
open JCHFunctionSummaryXmlDecoder
open JCHInstructionInfo
open JCHMethodImplementations
open JCHPreAPI
open JCHPreFileIO
open JCHSystemSettings

module H = Hashtbl

module ClassNameCollections = CHCollections.Make (
  struct
    type t = class_name_int
    let compare n1 n2 = n1#compare n2
    let toPretty n = n#toPretty
  end)

let summary_classpath = ref None

let get_summary_classpath () =
  match !summary_classpath with
  | None ->
    let cp = system_settings#get_summary_classpath in
    begin summary_classpath := Some cp ; cp end	
  | Some cp -> cp
    
let rec add_class_dependency (cn:class_name_int) =
  if app#has_class cn then () else
    let summaryClasspath = get_summary_classpath () in
    if JCHFile.has_summary_class summaryClasspath cn then
      let summaryString = JCHFile.get_summary_class summaryClasspath cn in
      let summary = read_xml_class_file_from_string cn#name summaryString in
      let _ = function_summary_library#add_class_summary summary in
      let classSummary = function_summary_library#get_class_summary cn in
      let cInfo = make_class_stub_info classSummary in
      let _ = app#add_class_stub cInfo in
      let dependents = get_class_summary_codependents classSummary in
      let methoddependencies =
        List.fold_left (fun acc ms ->
            let cms = make_cms cn ms in
            if function_summary_library#has_method_summary cms then
              let methodsummary = function_summary_library#get_method_summary cms in
              let taintelements = methodsummary#get_taint_elements in
              let deps =
                List.concat (List.map get_taint_element_class_dependencies taintelements) in
              deps @ acc
            else
              acc) [] classSummary#get_methods in
      List.iter add_class_dependency (dependents @ methoddependencies)
    else
      begin
	app#add_missing_class cn ;
	(if system_settings#is_logging_missing_classes_enabled then
           chlog#add "missing class" cn#toPretty)
      end
	
let add_summary cms summary =
  if summary#is_inherited then
    if summary#has_defining_method then
      let dcms = summary#get_defining_method in
      if app#has_method dcms then
	app#add_method_link cms dcms
      else if function_summary_library#has_method_summary dcms then
	begin
	  app#add_stub (function_summary_library#get_method_summary dcms) ;
	  app#add_method_link cms dcms ;
          chlog#add "add summary method link"
                    (LBLOCK [ cms#toPretty ;  STR " -> " ; dcms#toPretty ])
	end
      else (* no defining method *)
	app#add_missing_method cms
    else (* no defining method *)
      app#add_missing_method cms
  else (* summary is not inherited *)
    app#add_stub (function_summary_library#get_method_summary cms)
  
let add_field_summary cfs summary =
  if summary#is_inherited then
    let dcfs = summary#get_defining_class_field_signature in
    if app#has_field dcfs then
      app#add_field_link cfs dcfs
    else if function_summary_library#has_field_summary dcfs then
      begin
        app#add_field_stub (function_summary_library#get_field_summary dcfs) ;
        app#add_field_link cfs dcfs
      end
    else
      app#add_missing_field cfs
  else
    app#add_field_stub (function_summary_library#get_field_summary cfs)

let get_inherited_method (cms:class_method_signature_int) =
  let cn = cms#class_name in
  let ms = cms#method_signature in
  try
    let rec aux cn =
      let _ = add_class_dependency cn in
      if app#has_class cn then
        let cInfo = app#get_class cn in
        if cInfo#has_super_class then
	  let scn = cInfo#get_super_class in
          let _ = add_class_dependency scn in
	  let scms = make_cms scn ms in
	  if app#has_method scms then
	    Some (app#get_method scms)#get_class_method_signature
	  else if function_summary_library#has_method_summary scms then
	    let summary = function_summary_library#get_method_summary scms in
	    let _ = add_summary scms summary in
	    Some scms
	  else
	    aux scn
        else
	  None
      else
        None in
    aux cn
  with
    JCH_failure p ->
    begin
      ch_error_log#add
        "get-inherited-method" (LBLOCK [ cms#toPretty ; STR ": " ; p ]) ;
      raise (JCH_failure (LBLOCK [ STR "get_inherited_method " ; cms#toPretty; STR ": " ; p ]))
    end

let get_inherited_field (cfs:class_field_signature_int) =
  let cn = cfs#class_name in
  let fs = cfs#field_signature in
  try
    let rec aux cn =
      let _ = add_class_dependency cn in
      if app#has_class cn then
        let cInfo = app#get_class cn in
        if cInfo#has_super_class then
          let scn = cInfo#get_super_class in
          let _ = add_class_dependency scn in
          let scfs = make_cfs scn fs in
          if app#has_field scfs then
            Some (app#get_field scfs)#get_class_signature
          else if function_summary_library#has_field_summary scfs then
            let summary = function_summary_library#get_field_summary scfs in
            let _ = add_field_summary scfs summary in
            Some scfs
          else
            aux scn
        else
          None
      else
        None in
    aux cn
  with
    JCH_failure p ->
    begin
      ch_error_log#add
        "get-inherited-field" (LBLOCK [ cfs#toPretty ; STR ": " ; p ]) ;
      raise (JCH_failure (LBLOCK [ STR "get_inherited_field " ; cfs#toPretty ; STR ": " ; p ]))
    end
	
let add_method_dependency (cms:class_method_signature_int) =
  let cn = cms#class_name in 
  let _ = add_class_dependency cn in
  if app#has_method cms then () else
    if function_summary_library#has_method_summary cms then
      let summary = function_summary_library#get_method_summary cms in
      add_summary cms summary
    else
      match get_inherited_method cms with
      | Some dcms ->
         let _ = chlog#add "add method link"
                           (LBLOCK [ cms#toPretty ; STR " -> " ; dcms#toPretty ]) in
         app#add_method_link cms dcms
      | _ ->
         begin
	   app#add_missing_method cms ;
           (if system_settings#is_logging_missing_classes_enabled then
              chlog#add "missing method" cms#toPretty)
         end
	
let add_field_dependency (cfs:class_field_signature_int) =
  if app#has_field cfs then () else
    if function_summary_library#has_field_summary cfs then
      let fieldstub = function_summary_library#get_field_summary cfs in
      app#add_field_stub fieldstub
    else match get_inherited_field cfs with
         | Some dcfs -> app#add_field_link cfs dcfs
         | _ ->
            begin
              app#add_missing_field cfs ;
              chlog#add "missing field" cfs#toPretty
            end
	
let scan_method (mInfo:method_info_int) =
  let cms = mInfo#get_class_method_signature in
  let startupClasses = List.map make_cn startup_classes in
  let classesReferenced = get_classes_referenced mInfo in
  let methodsReferenced = get_methods_referenced mInfo in
  let fieldsReferenced = get_fields_referenced mInfo in
  let _ = List.iter add_class_dependency startupClasses in
  let _ = List.iter add_class_dependency classesReferenced in
  let _ = List.iter add_method_dependency methodsReferenced in
  let _ = List.iter add_field_dependency fieldsReferenced in
  let add_field_link i opc cn fs =
    let loc = get_bytecode_location mInfo#get_index i in
    let iInfo = make_instruction_info loc opc in
    let _ = app#add_instruction iInfo in
    let cfs = make_cfs cn fs in
    let finfo = app#get_field cfs in
    begin
      iInfo#set_field_target finfo ;
      match opc with
      | OpGetStatic _ | OpGetField _ -> finfo#add_reading_method cms
      | OpPutStatic _ | OpPutField _ -> finfo#add_writing_method cms
      | _ -> ()
    end in
  mInfo#bytecode_iteri (fun i opc ->
    match opc with
    | OpGetStatic (cn,fs)
    | OpPutStatic (cn,fs)
    | OpGetField (cn,fs)
    | OpPutField (cn,fs) -> add_field_link i opc cn fs
    | _ -> () )

let get_virtual_targets cn ms =
  try
  if app#has_class cn then
    let cInfo = app#get_class cn in
    if cInfo#is_final && cInfo#defines_method ms then
      [ cn ]
    else
      let implementations = method_signature_implementations#get_implementations ms in
      try
      let result = new ClassNameCollections.set_t in
      let _ = List.iter (fun cntgt ->
	let _ = add_class_dependency cntgt in
	if (cntgt#equal cn && cInfo#defines_method ms)|| app#is_descendant cntgt cn
           || app#is_descendant cn cntgt
           || app#implements_interface cInfo cntgt then
	  let tgtcms = make_cms cntgt ms in
	  let _ = add_method_dependency tgtcms in
	  let tgtmInfo = app#get_method tgtcms in
	  result#add tgtmInfo#get_class_name 
	else
	  ()
      ) (cn :: implementations) in
      let result = result#toList in
      let _ = match result with
	| [] -> chlog#add "virtual targets" 
	  (LBLOCK [ STR "No targets for " ; ms#toPretty ; STR " on " ;
		    cn#toPretty ; NL ;
                    STR "  candidates: " ;
                    pretty_print_list implementations (fun cn -> cn#toPretty) "" "," "" ])
	| _ -> () in
      result
      with
      | JCH_failure p ->
         raise (JCH_failure (LBLOCK [ STR "Error in get_virtual_targets with " ;
                                      cn#toPretty ; STR "." ; ms#toPretty ; STR ": " ; p ; NL ;
                                      STR "  candidates: " ;
                                      pretty_print_list implementations (fun cn -> cn#toPretty) "" "," "" ]))
                                      
  else
    []
  with
  | JCH_failure p ->
     raise (JCH_failure (LBLOCK [ STR "Error in get_virtual_targets with " ;
                                  cn#toPretty ; STR "." ; ms#toPretty ;
                                  STR ": " ; p ]))

let get_interface_targets cn ms =
  if app#has_class cn then
    let implementations = 
      try
	app#get_implementing_classes cn 
      with
	JCH_failure p ->
	  begin
	    ch_error_log#add "interface error" p ;
	    []
	  end in
    let result = new ClassNameCollections.set_t in
    let _ = List.iter (fun tgtcInfo ->
                if tgtcInfo#defines_method ms then
                  let cntgt = tgtcInfo#get_class_name in
                  let tgtcms = make_cms cntgt ms in
                  let _ = add_method_dependency tgtcms in
                  let tgtmInfo = app#get_method tgtcms in
                  result#add tgtmInfo#get_class_name) implementations in
    let result = result#toList in
    match result with
      | [] -> 
	let _ = 
	  chlog#add "interface targets" 
	    (LBLOCK [ STR "No targets for " ; ms#toPretty ; STR " on " ; 
		      cn#toPretty ]) in
	let defaults = 
	  let cInfo = app#get_class cn in
	  cInfo#get_default_implementations in
	begin
	  match defaults with
	  | [] ->
	    let cms = make_cms cn ms in
	    if function_summary_library#has_method_summary cms then
	      let _ = chlog#add "use interface summary" cms#toPretty in
	      [ cn ]
	    else
	      []
	  | l ->
	    let cms = make_cms cn ms in
	    let _ = List.iter add_class_dependency l in
	    let _ = chlog#add "use default implementations"
	      (LBLOCK [ STR "use " ;
			pretty_print_list l (fun cn -> cn#toPretty) "[" ", " "]" ;
			STR " for " ; cms#toPretty ]) in
	    l
	end
      | l -> l
  else
    []

let get_dynamic_targets _ _ = []

let set_method_method_targets (mInfo:method_info_int) =
  let (_,class_result,type_result) = analyze_method_for_classes_and_types mInfo in
  let get_static_target cn ms =
    let _ = method_signature_implementations#register_signature ms in
    let tgtcms = make_cms cn ms in
    let _ = if app#has_method tgtcms then () else add_method_dependency tgtcms in
    (app#get_method tgtcms)#get_class_name in
  let create_targets i opc ms targets =
    let _ = method_signature_implementations#register_signature ms in
    let _ = match targets with
      | [] -> ch_error_log#add "no targets"
	(LBLOCK [ STR "No targets found for " ; ms#toPretty ; STR " in " ;
		  mInfo#get_class_method_signature#toPretty ; STR " at pc = " ; INT i ] )
      | _ -> () in
    let targets =
      if H.mem class_result i then
        match H.find class_result i with
        | [] ->
           begin
             if H.mem type_result i then
               match H.find type_result i with
               | [] -> targets
               | tgts -> tgts
             else
               targets
           end
        | tgts -> tgts
      else
        targets in
    let loc = get_bytecode_location mInfo#get_index i in
    let iInfo = make_instruction_info loc opc in
    let _ = app#add_instruction iInfo in
    List.iter (fun tgt ->
      let tgtcms = make_cms tgt ms in
      let _ = if  app#has_method tgtcms then () else add_method_dependency tgtcms in	  
      let callee = app#get_method tgtcms in
      begin 
	mInfo#add_callee callee#get_class_method_signature ;
	iInfo#add_method_target callee ;
	callee#add_caller mInfo#get_class_method_signature
      end) targets in
  mInfo#bytecode_iteri (fun i opc ->
    match opc with
    | OpInvokeStatic (cn,ms) -> create_targets i opc ms [(get_static_target cn ms)]
    | OpInvokeSpecial (cn,ms) -> create_targets i opc ms [ (get_static_target cn ms) ]
    | OpInvokeVirtual (TClass cn,ms) -> create_targets i opc ms (get_virtual_targets cn ms)
    | OpInvokeInterface (cn,ms) -> create_targets i opc ms (get_interface_targets cn ms)
    | OpInvokeVirtual (_,ms) ->
       create_targets i opc ms [ (get_static_target (make_cn "java.lang.Object") ms) ]
    | OpInvokeDynamic (mindex,ms) ->
       let loc = get_bytecode_location mInfo#get_index i in
       let iInfo = make_instruction_info loc opc in
       app#add_instruction iInfo
    | _ -> ())

let set_method_targets () =
  app#iter_classes (fun cInfo ->
    if cInfo#is_stubbed then () else
      List.iter (fun ms ->
	let cms = make_cms cInfo#get_class_name ms in
	if app#has_method cms then
	  let mInfo = app#get_method cms in
	  set_method_method_targets mInfo) cInfo#get_methods_defined)			
    
let load_class (c:java_class_or_interface_int) =
  let coDependents = get_class_codependents c in
  let methods = List.filter (fun m -> m#is_concrete) c#get_methods in
  let fields = c#get_fields in
  begin
    List.iter (fun d -> if app#has_class d then () else app#add_missing_class d) coDependents ;
    app#add_class c ;
    List.iter app#add_method methods ;
    List.iter app#add_field fields ;
    List.iter scan_method app#get_methods ;
  end

let rec load_class_and_dependents (cn:class_name_int) =
  if app#has_class cn then () else
    let cp = system_settings#get_classpath in
    let c = get_class cp cn in
    let classes = c :: (List.map (get_class cp) c#get_interfaces) in
    let load_super c = 
      match c#get_super_class with Some sc -> load_class_and_dependents sc | _ -> () in
    begin
      List.iter app#add_class classes ;
      List.iter load_super classes ;
      List.iter load_class_and_dependents c#get_interfaces 
    end


let process_classes () =
  begin
    app#iter_classes (fun cInfo ->
        begin
          List.iter (fun ms ->
	      app#add_method (cInfo#get_method ms)) cInfo#get_methods_defined ;
          List.iter (fun fs ->
	      app#add_field (cInfo#get_field fs)) cInfo#get_fields_defined
        end) ;
    app#iter_classes (fun cInfo ->
        begin
          (if cInfo#has_super_class then add_class_dependency cInfo#get_super_class) ;
          List.iter add_class_dependency cInfo#get_interfaces ;
          (if cInfo#is_stubbed then () else
	     begin
	       List.iter (fun ms ->
	           let cms = make_cms cInfo#get_class_name ms in
	           if app#has_method cms then
		     let mInfo = app#get_method cms in
		     begin
		       List.iter add_class_dependency (get_classes_referenced mInfo) ;
		       scan_method mInfo
		     end) cInfo#get_methods_defined ;
	     end )
        end)
  end
(* ---------------------------------------------------------------------------------------
   Loads and parses all class files in the jar and adds them to app
   --------------------------------------------------------------------------------------- *)
let load_classes_in_jar ?(xcludes=[]) (jar:string) =
  let classesLoaded = ref [] in
  try
    let classpath = JCHFile.class_path jar in
    begin
      (try
	begin
	  JCHFile.apply_to_jar
            ~xcludes
	    (fun c ->
              try
	        let javaclass = JCHRaw2IF.low2high_class c in
	        begin
		  app#add_class javaclass ;
		  classesLoaded := javaclass#get_name :: !classesLoaded ;
	        end
              with
              | IO.No_more_input ->
                 ch_error_log#add "no more input" c.rc_name#toPretty
              | JCH_failure p ->
                 ch_error_log#add "error in class file"
                                  (LBLOCK [ c.rc_name#toPretty ; STR ": " ; p ]))
	    (fun _ _ -> ()) jar ;
	  JCHFile.close_class_path classpath
	end
      with
      | JCH_failure p -> 
	begin
	  ch_error_log#add "failure" (LBLOCK [ STR "Failure. " ; STR jar ; STR ": " ; p ]) ;
	  JCHFile.close_class_path classpath ;
	end) ;
      !classesLoaded
    end
  with
  | Zip.Error (name, a, s) ->
    begin
      system_settings#log_error (LBLOCK [ STR "Zip.Error. " ;
					  STR jar ; STR ": " ; STR name ; 
					  STR "; " ; STR a ; STR "; " ; STR s ]) ;
      []
    end
  | Sys_error s ->
    begin
      system_settings#log_error (LBLOCK [ STR "Sys_error. " ; STR jar ; STR ": " ; STR s ]) ;
      []
    end
  | IO.No_more_input ->
     begin
       pr_debug [ STR "No more input in load_classes_in_jar " ; STR jar ; NL ] ;
       ch_error_log#add "no more input" (STR jar) ;
       !classesLoaded
     end
    


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
open CHFileIO
open CHLogger
open CHUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBcDictionary
open JCHDictionary
open JCHFile
open JCHJTDictionary
open JCHSystemSettings

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHCallgraphBase
open JCHClassUserTemplate
open JCHInstructionInfo
open JCHMethodImplementations
open JCHPreAPI
open JCHTaintOrigin
open JCHUserData

module ClassNameCollections = CHCollections.Make (
  struct
    type t = class_name_int
    let compare n1 n2 = n1#compare n2
    let toPretty n = n#toPretty
  end)

module ClassMethodSignatureCollections = CHCollections.Make (
  struct
    type t = class_method_signature_int
    let compare cms1 cms2 = cms1#compare cms2
    let toPretty cms = cms#toPretty
  end)

let replace_lst = [ ('_',"_1") ; (';',"_2") ; ('[',"_3") ;
		    ('(',"_4") ; (')',"_5") ; ('/',"_6") ]

let replace = string_replace

let get_jch_root (info:string):xml_element_int =
  let root = xmlElement "codehawk-java-analyzer" in
  let hNode = xmlElement "header" in
  begin
    hNode#setAttribute "info" info ;
    hNode#setAttribute "time" (current_time_to_string ()) ;
    root#appendChildren [ hNode ] ;
    root
  end

let check_directory dir =
  if dir = "" then () else
    let sys_command s = ignore (Sys.command s) in
    if Sys.file_exists dir then () else sys_command ("mkdir " ^ dir)

let get_assumptions_filename (cn:class_name_int) =
  cn#simple_name ^ "_assumptions.xml"

let get_invariants_results_filename (cn:class_name_int) =
  cn#simple_name ^ "_invariants.txt"

let rec get_class_name_from_value_type vt =
  match vt with
  | TBasic _ -> None
  | TObject (TClass cn) -> Some cn
  | TObject (TArray vts) -> get_class_name_from_value_type vts

and get_class_name_from_object_type ot =
  match ot with
  | TClass cn -> Some cn
  | TArray vt -> get_class_name_from_value_type vt

let make_class_file_name (dir:string) (name:string) (md5:string) =
  dir ^ name ^ "_md5_" ^ md5

let summary_classpath = ref None
let get_summary_classpath () =
  match !summary_classpath with
  | None ->
    let cp = system_settings#get_summary_classpath in
    begin summary_classpath := Some cp ; cp end	
  | Some cp -> cp

let get_projectname_prefix_name s =
  system_settings#get_output_directory ^ "/" ^ system_settings#get_project_name ^ s

let has_stac_analysis_dir () =
  let resultsdir = system_settings#get_results_directory in
  Sys.file_exists (resultsdir ^ "/chanalysis")

let save_log_files name =
  let resultsdir = system_settings#get_results_directory  in
  let dir = resultsdir ^ "/chanalysis/" in
  let _ = check_directory dir in
  let filename = dir ^ name in
  begin
    CHFileIO.file_output#saveFile (filename ^ ".chlog") chlog#toPretty ;
    CHFileIO.file_output#saveFile (filename ^ ".ch_error_log") ch_error_log#toPretty
  end
  

let get_stac_analysis_data_prefix_name s =
  let resultsdir = system_settings#get_results_directory in
  let _ = check_directory (resultsdir ^ "/chanalysis") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chdata") in
  (resultsdir ^ "/chanalysis/chdata/" ^ s)

let get_stac_analysis_app_dir () =
  let resultsdir = system_settings#get_results_directory in
  let _ = check_directory (resultsdir ^ "/chanalysis") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chapp") in
  (resultsdir ^ "/chanalysis/chapp")

let get_stac_analysis_app_prefix_name s = (get_stac_analysis_app_dir ()) ^ "/" ^ s

let get_stac_cost_analysis_results_dir () =
  let resultsdir = system_settings#get_results_directory in
  let _ = check_directory (resultsdir ^ "/chanalysis") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chcost") in
  resultsdir ^ "/chanalysis/chcost"

let get_stac_atlas_cost_analysis_results_dir () =
  let resultsdir = system_settings#get_results_directory in
  let _ = check_directory (resultsdir ^ "/chanalysis") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chcost_atlas") in
  resultsdir ^ "/chanalysis/chcost_atlas"

let get_stac_analysis_userdata_directory_name () =
  let resultsdir = system_settings#get_results_directory in
  let _ = check_directory (resultsdir ^ "/chuserdata") in
  (resultsdir ^ "/chuserdata")

let get_stac_analysis_costsupport_directory_name () =
  let resultsdir = system_settings#get_results_directory in
  let _ = check_directory (resultsdir ^ "/chanalysis") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chcost") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chcost/support") in
  (resultsdir ^ "/chanalysis/chcost/support")

let get_stac_analysis_taintsupport_directory_name () =
  let resultsdir = system_settings#get_results_directory in
  let _ = check_directory (resultsdir ^ "/chanalysis") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chtaint") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chtaint/support") in
  (resultsdir ^ "/chanalysis/chtaint/support")

let get_defaultcostdata_filename () =
  let resultsdir = system_settings#get_results_directory in
  let _ = check_directory (resultsdir ^ "/chanalysis") in
  let _ = check_directory (resultsdir ^ "/chanalysis/chcost") in
  (resultsdir ^ "/chanalysis/chcost/defaultcostmodel.xml")

let get_dictionary_filename () = 
  get_stac_analysis_data_prefix_name "dictionary.xml"

let get_jt_dictionary_filename () =
  get_stac_analysis_data_prefix_name "jt_dictionary.xml"

let get_bc_dictionary_filename () =
  get_stac_analysis_data_prefix_name "bc_dictionary.xml"

let get_excluded_methods_filename () = 
  get_stac_analysis_data_prefix_name "excluded_methods.xml"

let get_excluded_classes_filename () = 
  get_stac_analysis_data_prefix_name "excluded_classes.xml"

let get_signature_filename () = 
  get_stac_analysis_data_prefix_name "signatures.xml"

let get_callgraph_filename () = 
  get_stac_analysis_data_prefix_name "callgraph.xml"

let get_missing_classes_filename () = 
  get_stac_analysis_data_prefix_name "missing_classes.xml"

let get_classnames_filename () = 
  get_stac_analysis_data_prefix_name "classnames.xml"

let get_taint_origins_filename () = 
  get_stac_analysis_data_prefix_name "taintorigins.xml"

let get_taint_trails_filename (index:int) =
  get_stac_analysis_data_prefix_name "tainttrails_" ^ (string_of_int index) ^ ".xml"

let get_timecost_diagnostics_filename () =
  get_stac_analysis_data_prefix_name "timecost_diagnostics.xml"

let save_xml_file (filename:string) (node:xml_element_int) (roottag:string) =
  let doc = xmlDocument () in
  let root = get_jch_root roottag in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_timecost_diagnostics (node:xml_element_int) =
  let filename = get_timecost_diagnostics_filename () in
  let doc = xmlDocument () in
  let root = get_jch_root "time-cost-diagnostics" in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end
    

let save_classnames (l:class_name_int list) =
  let doc = xmlDocument () in
  let root = get_jch_root "appclasses" in
  let filename = get_classnames_filename () in
  let node = xmlElement "classnames" in
  begin
    doc#setNode root ;
    node#appendChildren (List.map (fun cn ->
      let cNode = xmlElement "cn" in
      begin 
	cNode#setAttribute "name" cn#simple_name ;
        cNode#setAttribute "package" cn#package_name ;
	cNode#setIntAttribute "ix" cn#index ;
	cNode
      end) l) ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_dictionary () =
  let doc = xmlDocument () in
  let root = get_jch_root "dictionary" in
  let filename = get_dictionary_filename () in
  let node = xmlElement "dictionary" in
  begin
    doc#setNode root ;
    common_dictionary#write_xml node ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let save_jt_dictionary () =
  let doc = xmlDocument () in
  let root = get_jch_root "dictionary" in
  let filename = get_jt_dictionary_filename () in
  let node = xmlElement "dictionary" in
  let dnode = xmlElement "jterm-dictionary" in
  begin
    jtdictionary#write_xml dnode ;
    doc#setNode root ;
    root#appendChildren [ node ] ;
    node#appendChildren [ dnode ] ;
    file_output#saveFile filename doc#toPretty
  end
  
let read_dictionary () =
  let filename = get_dictionary_filename () in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let node = doc#getRoot#getTaggedChild "dictionary" in
      common_dictionary#read_xml node
    with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
    let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		       STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
    begin
      pr_debug [ msg ; NL ] ;
      raise (JCH_failure msg)
    end
  else
    pr_debug [ STR "Warning: No dictionary file found" ; NL ]

let read_jt_dictionary () =
  let filename = get_jt_dictionary_filename () in
  if Sys.file_exists filename then
    try
      let jdoc = readXmlDocument filename in
      let jroot = jdoc#getRoot in
      let jNode = jroot#getTaggedChild "dictionary" in
      let dNode = jNode#getTaggedChild "jterm-dictionary" in
      jtdictionary#read_xml dNode
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		          STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
       begin
         pr_debug [ msg ; NL ] ;
         raise (JCH_failure msg)
       end
  else
    ()


let read_excluded_methods () =
  let filename = get_excluded_methods_filename () in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let node = doc#getRoot#getTaggedChild "excluded-methods" in
      List.map (fun n -> n#getIntAttribute "cmsix") (node#getTaggedChildren "x")
    with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
    let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		       STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
    begin
      pr_debug [ msg ; NL ] ;
      raise (JCH_failure msg)
    end
  else
    []

let read_excluded_classes () =
  let filename = get_excluded_classes_filename () in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let node = doc#getRoot#getTaggedChild "excluded-classes" in
      let xcls = List.map (fun n -> 
	n#getIntAttribute "cnix") (node#getTaggedChildren "x") in
      system_settings#set_excluded_classes xcls
    with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
    let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		       STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
    begin
      pr_debug [ msg ; NL ] ;
      raise (JCH_failure msg)
    end
  else
    ()


let save_taint_origins () =
  let doc = xmlDocument () in
  let root = get_jch_root "taint-origins" in
  let filename = get_taint_origins_filename () in
  let dnode = xmlElement "taint-dictionary" in
  let node = xmlElement "taint-origins" in
  begin
    doc#setNode root ;
    taint_dictionary#write_xml dnode ;
    node#appendChildren [ dnode ] ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let read_taint_origins () =
  let filename = get_taint_origins_filename () in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let node = doc#getRoot#getTaggedChild "taint-origins" in
      taint_dictionary#read_xml (node#getTaggedChild "taint-dictionary") 
    with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
    let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		       STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
    begin
      pr_debug [ msg ; NL ] ;
      raise (JCH_failure msg)
    end
  else
    pr_debug [ STR "Warning: No taint origins file found" ; NL ]

let save_signature_file () = 
  let doc = xmlDocument () in
  let root = get_jch_root "signatures" in
  let filename = get_signature_filename () in
  let node = xmlElement "signatures" in
  begin
    doc#setNode root ;
    method_signature_implementations#write_xml node ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end


let save_callgraph_file () =
  let doc = xmlDocument () in
  let root = get_jch_root "callgraph" in
  let filename = get_callgraph_filename () in
  let node = xmlElement "callgraph" in
  begin
    doc#setNode root ;
    callgraph_base#write_xml node ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let read_callgraph_file () =
  let filename = get_callgraph_filename () in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let node = doc#getRoot#getTaggedChild "callgraph" in
      callgraph_base#read_xml node
    with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
    let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		       STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
    begin
      pr_debug [ msg ; NL ] ;
      raise (JCH_failure msg)
    end
  else
    pr_debug [ STR "Warning: No callgraphh file found" ; NL ]

let save_missing_classes () =
  let doc = xmlDocument () in
  let root = get_jch_root "missing-classes" in
  let filename = get_missing_classes_filename () in
  let node = xmlElement "missing-classes" in
  begin
    doc#setNode root ;
    app#write_xml_missing_classes node ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end
  

let get_class_dir (dir:string) (cn:class_name_int) =
  let _ = check_directory dir in
  let pdirs =
    List.map (fun p ->
        List.fold_left (fun sa (c,r) -> replace c r sa) p [ ('$',"__dollarsign__") ])
             cn#package in
  let packageDirs =
    List.fold_left (fun acc u -> match acc with
    | [] -> u::acc
    | h::_ -> (h ^ "/" ^ u) :: acc) [] pdirs in
  let classDir = match packageDirs with
    | [] -> ""
    | h::_ -> h ^ "/" in
  let _ = List.iter (fun d -> 
    check_directory (dir ^ "/" ^ d)) (List.rev packageDirs) in
  dir ^ "/" ^ classDir


let create_method_filename (dir:string) (cms:class_method_signature_int) contents =
  let cn = cms#class_name in
  let classDir = get_class_dir dir cn in
  let methodname = 
    if cms#name = "<init>" then "__init__"
    else if cms#name = "<clinit>" then "__clinit__"
    else if String.length cms#name > 6 && String.sub cms#name 0 6 = "lambda" then
      replace '$' "__" cms#name
     else if (String.length cms#name) > 20 && String.sub cms#name 0 19 = "$deserializeLambda$" then
              replace '$' "__" cms#name
    else cms#name in
  let methodname = methodname ^ "_" ^ (string_of_int cms#index) in
  let methoddir = classDir ^ cn#simple_name ^ "/" in
  let methoddir = List.fold_left (fun sa (c,r) -> 
    replace c r sa) methoddir [ ('$',"__dollarsign__") ] in
  let _ = check_directory methoddir in
  methoddir ^ methodname ^ "_" ^ contents ^ ".xml"
  

let create_filename (dir:string) (cn:class_name_int) (md5:string) (timestamp:string) =
  let classDir = get_class_dir dir cn in
  let md5 = if md5 = "" then "" else "_md5_" ^ md5 in
  let timestamp = if timestamp = "" then "" else "_time_" ^ timestamp in 
  classDir ^ cn#simple_name ^ md5 ^ timestamp ^ ".xml"


let save_method_xml_file (cms:class_method_signature_int) (node:xml_element_int) 
    (contents:string) =
  let doc = xmlDocument () in
  let root = get_jch_root contents in
  let appdir = get_stac_analysis_app_dir () in 
  let filename = create_method_filename appdir cms contents in
  begin
     doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let load_method_xml_file (cms:class_method_signature_int) (contents:string) =
  let appdir = get_stac_analysis_app_dir () in
  let filename = create_method_filename appdir cms contents in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      Some (doc#getRoot#getTaggedChild "method")
    with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
    let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		       STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
    begin
      pr_debug [ msg ; NL ] ;
      raise (JCH_failure msg)
    end
  else
    begin
      pr_debug [ STR "Warning: No method file found for " ; cms#toPretty ; NL ] ;
      None
    end
    

let save_class_xml_file 
    (dir:string) 
    (cn:class_name_int) 
    ?(md5="") 
    ?(timestamp="") 
    (node:xml_element_int) 
    (contents:string) = 
  let doc = xmlDocument () in
  let root = get_jch_root contents in
  let filename = create_filename dir cn md5 timestamp in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    file_output#saveFile filename doc#toPretty
  end

let load_class_xml_file
    (dir:string)
    (cn:class_name_int)
    ?(md5="")
    ?(timestamp="") () =
  let filename = create_filename dir cn md5 timestamp in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      Some (doc#getRoot#getTaggedChild "class")
    with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
    let msg = LBLOCK [ STR "Xml error in " ; STR filename ; STR " at " ;
		       STR "(" ; INT line ; STR "," ; INT col ; STR "):" ; p ] in
    begin
      pr_debug [ msg ; NL ] ;
      raise (JCH_failure msg)
    end
  else
    begin
      pr_debug [ STR "Warning: No class file found for " ; cn#toPretty ; NL ] ;
      None
    end
      
let load_xml_cost_analysis_results 
    (cn:class_name_int) =  
  let dir = get_stac_cost_analysis_results_dir () in
  load_class_xml_file dir cn ()

let save_xml_cost_analysis_results 
    (cn:class_name_int) (node:xml_element_int) (contents:string) =
  let dir = get_stac_cost_analysis_results_dir () in
  save_class_xml_file dir cn node contents

let save_xml_atlas_cost_analysis_results
      (cn:class_name_int) (node:xml_element_int) (contents:string) =
  let dir = get_stac_atlas_cost_analysis_results_dir () in
  save_class_xml_file dir cn node contents

let save_xml_cost_support_data
      (cn:class_name_int) (node:xml_element_int) (contents:string) =
  let dir = get_stac_analysis_costsupport_directory_name () in
  save_class_xml_file dir cn node contents

let save_xml_taint_support_data
      (cn:class_name_int) (node:xml_element_int) (contents:string) =
  let dir = get_stac_analysis_taintsupport_directory_name () in
  save_class_xml_file dir cn node contents

let apply_to_xml_jar (filter:string -> bool) (f:string -> string -> unit) =
  JCHFile.apply_to_xml_jar 
    (fun name s -> if filter name then f name s else ())
    (fun _ _ -> ())


let save_xml_user_class_template_file (cn:class_name_int) =
  let cInfo = app#get_class cn in
  let tag = if cInfo#is_interface then "interface" else "class" in
  let node = xmlElement tag in
  let doc = xmlDocument () in
  let root = get_jch_root tag in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    write_xml_user_class_template node cn;
    file_output#saveFile (cn#simple_name ^ ".xml") doc#toPretty
  end

let load_defaultcostdata_file () =
  let xfile = get_defaultcostdata_filename () in
  if Sys.file_exists xfile then
    try
      let doc = readXmlDocument xfile in
      let node = doc#getRoot#getTaggedChild "methods" in
      userdata#add_default_costdata node
    with
    | XmlDocumentError (line,col,p)
    | XmlParseError (line,col,p) ->
      let msg = LBLOCK [ STR "Xml error in " ; STR xfile ; STR " at " ;
			 STR "(" ; INT line ; STR "," ; INT col ; STR "): " ; p ] in
      begin
	pr_debug [ msg ; NL ] ;
	raise (JCH_failure msg)
      end

let read_user_constants_file xfile =
  if Sys.file_exists xfile then
    try
      let doc = readXmlDocument xfile in
      let node = doc#getRoot#getTaggedChild "constants" in
      userdata#register_constants node
    with
    | XmlDocumentError (line,col,p)
    | XmlParseError (line,col,p) ->
      let msg = LBLOCK [ STR "Xml error in " ; STR xfile ; STR " at " ;
			 STR "(" ; INT line ; STR "," ; INT col ; STR "): " ; p ] in
      begin
	pr_debug [ msg ; NL ] ;
	raise (JCH_failure msg)
      end

let load_xml_user_data () =
  let dir = get_stac_analysis_userdata_directory_name () in
  let filename = dir ^ "/userdata.xml" in
  if Sys.file_exists filename then
    let doc = readXmlDocument filename in
    let node = doc#getRoot#getTaggedChild "userdata" in
    userdata#add_userdata node
  else
    ()
  
let load_user_class_files () =
  let dir = get_stac_analysis_userdata_directory_name () in
  if Sys.file_exists dir then
    let constantsfile = dir ^ "/constants.xml" in
    let _ = if Sys.file_exists constantsfile then 
	read_user_constants_file constantsfile in
    let uxfiles = ref [] in
    let rec collect_xml_files d =
      if Sys.is_directory d then
	let dirItems = Array.to_list (Sys.readdir d) in
	let xmlfiles = List.filter (fun f -> Filename.check_suffix f ".xml") dirItems in
	let xmlfiles = List.filter (fun f -> 
	  match f with "constants.xml" -> false | _ -> true) xmlfiles in
	let dirs = List.filter (fun f -> Sys.is_directory (d ^ "/" ^ f)) dirItems in
	begin
	  uxfiles := (List.map (fun x -> d ^ "/" ^ x) xmlfiles) @ !uxfiles ;
	  List.iter (fun f -> collect_xml_files (d ^ "/" ^ f)) dirs
	end in
    begin
      collect_xml_files dir ;
      List.iter (fun xfile -> 
	try
	  let doc = readXmlDocument xfile in
	  let node = doc#getRoot#getTaggedChild "class" in
	  userdata#add_class_data node
	with
	| XmlDocumentError (line,col,p)
	| XmlParseError (line,col,p) ->
	  let msg = LBLOCK [ STR "Xml error in " ; STR xfile ; STR " at " ;
			     STR "(" ; INT line ; STR "," ; INT col ; STR "): " ; p ] in
	  begin
	    pr_debug [ msg ; NL ] ;
	    raise (JCH_failure msg)
	  end) !uxfiles
    end
  else
    pr_debug [ STR "No user data found" ; NL ]

let load_xml_cost_support_files () =
  let dir = get_stac_analysis_costsupport_directory_name () in
  let xnodes = ref [] in
  let uxfiles = ref [] in
  if Sys.file_exists dir then
    let rec collect_xml_files d =
      if Sys.is_directory d then
	let dirItems = Array.to_list (Sys.readdir d) in
	let xmlfiles = List.filter (fun f -> Filename.check_suffix f ".xml") dirItems in
	let dirs = List.filter (fun f -> Sys.is_directory (d ^ "/" ^ f)) dirItems in
	begin
	  uxfiles := (List.map (fun x -> d ^ "/" ^ x) xmlfiles) @ !uxfiles ;
	  List.iter (fun f -> collect_xml_files (d ^ "/" ^ f)) dirs
	end in
    begin
      collect_xml_files dir ;
      List.iter (fun xfile -> 
	  try
	    let doc = readXmlDocument xfile in
	    let node = doc#getRoot#getTaggedChild "class" in
            xnodes := node :: !xnodes
          with
	  | XmlDocumentError (line,col,p)
	    | XmlParseError (line,col,p) ->
	     let msg = LBLOCK [ STR "Xml error in " ; STR xfile ; STR " at " ;
			        STR "(" ; INT line ; STR "," ; INT col ; STR "): " ; p ] in
	     begin
	       pr_debug [ msg ; NL ] ;
	       raise (JCH_failure msg)
	     end) !uxfiles ;
      !xnodes
    end
  else
    []

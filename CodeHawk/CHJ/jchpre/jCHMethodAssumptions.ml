(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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
open CHNumerical
open CHPretty

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil
open CHReportUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm
open JCHXmlUtil

(* jchpre *)
open JCHApplication
open JCHFunctionSummary
open JCHFunctionSummaryXmlDecoder
open JCHPreAPI
open JCHPreFileIO


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end


let write_xml_method_spec_signature 
    (node:xml_element_int) (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let mInfo = app#get_method cms in
  let varname = mInfo#get_varname_mapping 0 in
  let descriptor = cms#method_signature#descriptor in
  begin
    append (List.mapi (fun i a ->
      let aNode = xmlElement "arg" in
      let set = aNode#setAttribute in
      let seti = aNode#setIntAttribute in
      begin
	write_xmlx_value_type aNode a ;
	set "asmtype" (value_type_to_asm_string a) ;
	set "name" (varname i) ;
	seti "nr" (if mInfo#is_static then (i+1) else i) ;
	aNode 
      end) descriptor#arguments) ;
    match descriptor#return_value with
    | Some v ->
      let rNode = xmlElement "return" in
      begin
	write_xmlx_value_type rNode v ;
	rNode#setAttribute "asmtype" (value_type_to_asm_string v) ;
	append [ rNode ]
      end
    | _ -> ()
  end

let write_xml_method_spec_template (node:xml_element_int) (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sNode = xmlElement "signature" in
  let aNode = xmlElement "assumptions" in
  let mInfo = app#get_method cms in
  begin
    write_xml_method_spec_signature sNode cms ;
    append [ sNode ; aNode ] ;
    set "name" cms#method_name_string ;
    (if mInfo#is_static then set "static" "yes")
  end

let write_xml_class_spec_template (node:xml_element_int) ?(methods=[]) (cn:class_name_int) =
  let set = node#setAttribute in
  let sety t v = if v then set t "yes" else set t "no" in
  let cInfo = app#get_class cn in
  let mss = List.filter (fun ms -> 
    match ms#descriptor#arguments with [] -> false | _ -> true) cInfo#get_methods_defined in
  let cmss = List.map (fun ms -> make_cms cn ms) mss in
  let cmss = match methods with
    | [] -> cmss
    | l ->
       List.filter (fun cms ->
           List.exists (fun m -> cms#index = m#index) l) cmss in
  let cmss =
    List.sort (fun cms1 cms2 -> Stdlib.compare cms1#name cms2#name) cmss in
  let mmNode = xmlElement "methods" in
  begin
    mmNode#appendChildren (List.map (fun cms ->
      let mNode = xmlElement "method" in
      begin write_xml_method_spec_template mNode cms ; mNode end) cmss) ;
    node#appendChildren [ mmNode ] ;
    set "name" cn#simple_name ;
    (if cn#package_name = "" then () else set "package" cn#package_name) ;
    sety "final" cInfo#is_final ;
    sety "abstract" cInfo#is_abstract ;
  end

let save_xml_method_assumptions_file ?(methods=[]) (cn:class_name_int) =
  let node = xmlElement "class" in
  let doc = xmlDocument () in
  let root = get_jch_root "spec template" in
  let filename = cn#simple_name ^ "_assumptions.xml" in
  if Sys.file_exists filename then 
    pr_debug [ STR "File " ; STR filename ; 
	       STR " already exists; spec file is not saved " ; NL ]
  else
    begin
      doc#setNode root ;
      root#appendChildren  [ node ] ;
      write_xml_class_spec_template node ~methods cn ;
      file_output#saveFile filename doc#toPretty
    end

let read_xml_method_signature (node:xml_element_int) =
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let getcc = node#getTaggedChildren in
  let argTypes = List.map read_xml_type (getcc "arg") in
  let argNames = List.fold_left (fun acc n -> 
    if n#hasNamedAttribute "name" then
      (n#getIntAttribute "nr",n#getAttribute "name") :: acc else acc) [] (getcc "arg") in
  let returnType = if hasc "return" then Some (read_xml_type (getc "return")) else None in
  (argTypes,argNames,returnType)
   
let read_xml_method_assumptions 
    (node:xml_element_int) 
    (cn:class_name_int):(class_method_signature_int * relational_expr_t list) = 
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let name = get "name" in
  let is_static = if has "static" then (get "static") = "yes" else false in
  let (arguments,argumentnames,rt) = 
    read_xml_method_signature (node#getTaggedChild "signature") in
  let desc = match rt with
    | Some return_value -> make_method_descriptor ~arguments ~return_value ()
    | _ -> make_method_descriptor ~arguments () in
  let ms = make_ms is_static name desc in
  let cms = make_cms cn ms in
  let assumptions = List.map (fun n ->
    read_xmlx_relational_expr n ~argumentnames cms) 
    ((node#getTaggedChild "assumptions")#getTaggedChildren "assumption") in
  (cms, assumptions)
  

let read_xml_method_assumptions_file 
    (cn:class_name_int):(class_method_signature_int * relational_expr_t list) list = 
  let filename = get_assumptions_filename cn in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let node = doc#getRoot#getTaggedChild "class" in
      let mNodes = (node#getTaggedChild "methods")#getTaggedChildren "method" in
      List.map (fun n -> read_xml_method_assumptions n cn) mNodes
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

let save_invariants_report_acl2
    (versioninfo:string)
    (cn:class_name_int)
    (starttime:float)
    (l:(class_method_signature_int * (int * relational_expr_t list) list) list) =
  let has_invariants pcLst =
    List.exists (fun (_,l) -> match l with [] -> false | _ -> true) pcLst in
  let analysistime = (Unix.gettimeofday ()) -. starttime in
  let reportHeader = 
    get_report_header ~analysistime ~prefix:";; " "CodeHawk Class Analyzer"
      versioninfo "Invariants report" 
    (cn#simple_name ^ ".class") in
  let pCmsResult 
      (cms:class_method_signature_int) 
      (results:(int * relational_expr_t list) list):pretty_t =
    let mInfo = app#get_method cms in
    let varname = mInfo#get_argname_mapping in
    let pline pc = 
      if mInfo#has_line_number pc then INT (mInfo#get_line_number pc) else STR "" in
    let pMs ms = LBLOCK [ STR ms#name ; STR ms#to_signature_string ] in
    let pCms cms = 
      let cn = cms#class_name in 
      let ms = cms#method_signature in
      LBLOCK [ cn#toPretty ; STR "." ; pMs ms ] in
    let pAssumptions = 
      match mInfo#get_argument_assumptions with
      | [] -> STR ""
      | l -> 
	let pr x = relational_expr_to_pretty ~varname x in
	let plst = List.map pr l in
	LBLOCK [ NL ; STR ";; Argument assumptions: " ; NL ;
		      INDENT (3, pretty_print_list plst 
			(fun p -> LBLOCK [ STR ";; " ; p ; NL]) "" "" "") ; NL ]  in
    let pInvsResult (results:(int * relational_expr_t list) list) =
      LBLOCK (List.map (fun (pc,invs) ->
	let varname = mInfo#get_varname_mapping pc in
	let pInv (inv:relational_expr_t) =
	  LBLOCK [ relational_expr_to_sexpr_pretty ~varname inv ; NL ] in
	match invs with
	| [] -> STR ""
	| _ ->
	  LBLOCK [ 
	    INDENT (2, LBLOCK [ STR "(" ; INT pc ; STR "  " ; pline pc ; STR "  " ; NL ;
				INDENT (10, LBLOCK [ STR "(" ; NL ]) ;
				INDENT (11, LBLOCK (List.map pInv invs)) ;
				INDENT (10, STR ")") ; NL ]) ;
	    INDENT (2, STR ")") ; NL ]) results) in
    if has_invariants results then
      LBLOCK [ pAssumptions ; STR "(\"" ; pCms cms ; STR "\"" ; NL ;
	       INDENT (3, LBLOCK [ STR "(" ; NL ; 
				   pInvsResult results ; STR ")" ; NL ]) ;
	       STR ")" ; NL ] 
    else
      LBLOCK [ STR "(\"" ; pCms cms ; STR "\" ()) ;; no invariants found" ; NL ] in
  let p = LBLOCK (List.map (fun (cms,results) -> pCmsResult cms results) l) in
  let filename = get_invariants_results_filename cn in
  file_output#saveFile filename (LBLOCK [ reportHeader ; NL ; p ])
      
let save_invariants_report 
    (versioninfo:string)
    (cn:class_name_int)
    (starttime:float)
    (l:(class_method_signature_int * (int * relational_expr_t list) list) list) =
  let has_invariants pcLst =
    List.exists (fun (_,l) -> match l with [] -> false | _ -> true) pcLst in
  let analysistime = (Unix.gettimeofday ()) -. starttime in
  let reportHeader = 
    get_report_header ~analysistime "CodeHawk Class Analyzer " versioninfo "Invariants report" 
    (cn#simple_name ^ ".class") in
  let p = LBLOCK (List.map (fun (cms, invs) ->
    let mInfo = app#get_method cms in
    let varname = mInfo#get_argname_mapping in
    let ms = cms#method_signature in
    let pAssumptions = 
      match mInfo#get_argument_assumptions with
      | [] -> STR ""
      | l -> 
	let pr x = relational_expr_to_pretty ~varname x in
	let plst = List.map pr l in
	LBLOCK [ NL ; STR "Argument assumptions: " ; NL ;
		      INDENT (3, pretty_print_list plst 
			(fun p -> LBLOCK [ p ; NL]) "" "" "") ; NL ]  in
    let pMs = 
      let pArgs = 
	STR (String.concat ","
	       (List.mapi (fun i a ->
		 let index = if mInfo#is_static then i else i+1 in
		 (varname index) ^ ":" ^ (value_type_to_string a)) 
		  ms#descriptor#arguments)) in
      let pRet = match ms#descriptor#return_value with
	| Some v -> LBLOCK [ value_type_to_pretty v ; STR " " ] | _ -> STR "" in
      LBLOCK [ pRet ; STR ms#name ; STR "(" ; pArgs ; STR ")" ] in
    let pCms = LBLOCK [ cn#toPretty ; STR "." ; pMs ] in
    LBLOCK [ pCms ; NL ; pAssumptions ; 
	     (if has_invariants invs then
	       LBLOCK (List.map (fun (pc, xprs) ->
		 match xprs with
		 | [] -> STR ""
		 | _ ->
		   let varname = mInfo#get_varname_mapping pc in
		   let pr x = relational_expr_to_sexpr_pretty ~varname x in
		   let pinvs = List.map pr xprs in
		   let pline = if mInfo#has_line_number pc then
		       LBLOCK [ fixed_length_pretty ~alignment:StrRight
				  (INT (mInfo#get_line_number pc)) 5 ; STR "  " ]
		     else STR "" in
		   let indent = string_repeat " " 
		     (if mInfo#has_line_number pc then 14 else 7) in 
		   LBLOCK [ fixed_length_pretty ~alignment:StrRight (INT pc) 5 ; STR "  " ;
			    pline ;
			    pretty_print_list pinvs (fun p -> LBLOCK [ INDENT (3,p) ; NL ])
			      "" indent "" ; NL ]) invs)
	      else
	     LBLOCK [ STR "  --- No invariants generated --- " ; NL ]) ; NL ]) l) in
  let filename = get_invariants_results_filename cn in
  file_output#saveFile filename (LBLOCK [ reportHeader ; NL ; p ])
  
  
			      

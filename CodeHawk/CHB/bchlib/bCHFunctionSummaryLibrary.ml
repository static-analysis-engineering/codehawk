(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHUtil
open CHXmlReader
open CHXmlDocument

(* bchlib *)
open BCHSystemSettings
open BCHBasicTypes
open BCHConstantDefinitions
open BCHDemangler
open BCHFunctionSummary
open BCHLibTypes
open BCHSystemInfo
open BCHTypeDefinitions
open BCHUtilities
open BCHVariableType
open BCHXmlUtil

module H = Hashtbl

let summary_directories = [
  "advapi32_dll" ;
  "comctl32_dll" ;
  "comdlg32_dll" ;
  "crypt32_dll"  ;
  "dwmapi_dll"   ;
  "gdi32_dll"    ;
  "imm32_dll"    ;
  "iphlpapi_dll" ;
  "kernel32_dll" ;
  "mscoree_dll"  ;
  "msvcrt_dll"   ;
  "msvfw32_dll"  ; 
  "mswsock_dll"  ;
  "netapi32_dll" ;
  "netdll_dll"   ;
  "odbc32_dll"   ;
  "ole32_dll"    ;
  "oleaut32_dll" ;
  "oledlg_dll"   ;
  "opengl32_dll" ;
  "psapi_dll"    ;
  "rpcrt4_dll"   ;
  "secur32_dll"  ;
  "shell32_dll"  ;
  "shlwapi_dll"  ;
  "spoolss_dll"  ;
  "urlmon_dll"   ;
  "user32_dll"   ;
  "userenv_dll"  ;
  "version_dll"  ;
  "wininet_dll"  ;
  "winmm_dll"    ;
  "winspool_dll" ;
  "winspool_drv" ;
  "ws2_32_dll"   ; 
  "wsock32_dll"  
]

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


class function_summary_library_t:function_summary_library_int =
object (self)

  val libsummaries = H.create 3   (* indexed by concatenated pkg names,fname *)
  val nolibsummaries = H.create 3 (* indexed by concatenated pkg names,fname *)
  val dllsummaries = H.create 3   (* indexed by (dllname,fname) *)
  val sosummaries = H.create 3    (* ELF shared-object summaries, indexed by fname *)
  val jnisummaries = H.create 3   (* indexed by jni index *)
  val jnitemplates = H.create 3   (* indexed by templated name *)
  val nosummaries = H.create 3
  val missing_summaries = new StringCollections.table_t     (* indexed by dll *)
  val requested_summaries = new StringCollections.table_t   (* indexed by dll *)
  val requested_so_summaries = new StringCollections.set_t
  val missing_so_summaries = new StringCollections.set_t
  val missingjnisummaries = new IntCollections.set_t
  val requestedjnisummaries = new IntCollections.set_t
  val dllnames = Hashtbl.create 3  (* records where summaries were taken from *)
  val dlls = new StringCollections.set_t                   (* dlls being used *)

  method has_function_dll (fname:string) = H.mem dllnames fname 
    
  method get_function_dll (fname:string) =
    if H.mem dllnames fname then
      H.find dllnames fname
    else
      raise (BCH_failure (LBLOCK [ STR "Function " ; STR fname ; 
				   STR " does not have an associated dll" ]))

  method has_dllname (dllname:string) = dlls#has dllname

  method get_jni_function (index:int) =
    if H.mem jnisummaries index then
      H.find jnisummaries index
    else
      raise (BCH_failure (LBLOCK [ STR "No summary found for jni index " ; INT index ]))

  method get_dll_function (dll:string) (fname:string) =
    let dll = self#get_internal_dll_name dll in
    if H.mem dllsummaries (dll,fname) then
      H.find dllsummaries (dll,fname)
    else
      raise (BCH_failure 
	       (LBLOCK [ STR "Function " ; STR fname ; STR " not found in dll " ;
			 STR dll ]))

  method get_so_function (fname:string) =
    if H.mem sosummaries fname then
      H.find sosummaries fname
    else
      raise (BCH_failure
               (LBLOCK [ STR "SO Function " ; STR fname ; STR " not found" ]))

  method get_lib_function (pkgs:string list) (fname:string) =
    let pkgs = List.map String.lowercase_ascii pkgs in
    let pkgs = String.concat "::" pkgs in
    if H.mem libsummaries (pkgs,fname) then
      H.find libsummaries (pkgs,fname)
    else
      raise (BCH_failure
	       (LBLOCK [ STR "Function " ; STR fname ; STR " not found in library " ;
			 STR pkgs ]))

  method private add_requested_summary (dll:string) (fname:string) =
    let entry = match requested_summaries#get dll with
      | Some entry -> entry
      | _ ->
	let entry = new StringCollections.set_t in
	begin requested_summaries#set dll entry ; entry end in
    entry#add fname

  method private add_missing_summary (dll:string) (fname:string) =
    let entry = match missing_summaries#get dll with
    | Some entry -> entry
    | _ -> let entry = new StringCollections.set_t in
	   begin missing_summaries#set dll entry ; entry end in
    entry#add fname

  method load_dll_library_function (dll:string) (fname:string) =
    let dll = self#get_internal_dll_name dll in
    let _ = self#add_requested_summary dll fname in
    if H.mem dllsummaries (dll,fname) || H.mem nosummaries (dll,fname) then
      ()
    else
      let path = system_settings#get_summary_paths in
      let filename = dll ^ "/" ^ fname in
      if has_summary_file path filename then
	let _ = dlls#add dll in
	let xstring = get_summary_file path filename in
	self#read_dll_function_summary_string dll fname xstring
      else
	begin
	  chlog#add "no summary"
	    (LBLOCK [ STR fname ; STR " (" ; STR dll ; STR ")" ; 
		      STR (self#get_demangled_name fname) ]) ;
	  self#add_missing_summary dll fname ;
	  H.add nosummaries (dll,fname) true
	end

  method load_so_function (fname:string) =
    let _ = requested_so_summaries#add fname in
    if H.mem sosummaries fname || missing_so_summaries#has fname then
      ()
    else
      let path = system_settings#get_summary_paths in
      let filename = "so_functions/" ^ fname in
      if has_summary_file path filename then
        let xstring = get_summary_file path filename in
        self#read_so_function_summary_string fname xstring
      else
        begin
          chlog#add "no so summary" (LBLOCK [ STR fname ]) ;
          missing_so_summaries#add fname
        end

  method private load_template_jni_summary (templatename:string) =
    if H.mem jnitemplates templatename then () else
      let path = system_settings#get_summary_paths in
      let filename = "jni/" ^ templatename in
      if has_summary_file path filename then
	let xstring = get_summary_file path filename in
	let doc = readXmlDocumentString xstring in
	let root = doc#getRoot in
	if root#hasOneTaggedChild "jnifun" then
	  let node = root#getTaggedChild "jnifun" in
	  let summary = read_xml_function_summary node in
	  begin
	    H.add jnitemplates templatename summary ;
	    chlog#add "jni template" (LBLOCK [ STR templatename ])
	  end
	else
	  raise_xml_error root (LBLOCK [ STR "Error in " ; STR templatename ])
      else
	raise (BCH_failure (LBLOCK [ STR "No jni template found for " ; STR templatename ]))

  method private load_jni_function (index:int) =
    if H.mem jnisummaries index || missingjnisummaries#has index then () else
      let path = system_settings#get_summary_paths in
      let filename = "jni/jni_" ^ (string_of_int index) in
      if has_summary_file path filename then
	let xstring = get_summary_file path filename in
	self#read_jni_function_summary_string index xstring
      else
	begin
	  chlog#add "no jni summary" (LBLOCK [ STR "Jni index: " ; INT index ]) ;
	  missingjnisummaries#add index 
	end
	  

  method private load_summary_dependencies (summary:function_summary_int) =
    let enums = summary#get_enums_referenced in
    List.iter system_info#read_xml_constant_file enums

  method private check_name (node:xml_element_int) (fname:string) =
    let name = node#getAttribute "name" in
    if name = fname then () else
      raise_xml_error node 
	(LBLOCK [ STR "Name in file " ; STR fname  ; 
		  STR " does not correspond with name listed: " ; STR name ])

  method private check_dll (node:xml_element_int) (dll:string) =
    let lib = String.lowercase_ascii(node#getAttribute "lib") in
    let dll = String.lowercase_ascii(dll) in
    let lib = if String.contains lib '.' then
	string_replace '.' "_" lib else lib in
    if dll = lib
       || dll = lib ^ "_dll"
       || dll = "so_functions"
    then
      ()
    else
      raise_xml_error node
	(LBLOCK [ STR "Dll in file " ; STR (node#getAttribute "name") ; 
		  STR " does not correspond with lib listed: " ; STR lib ])

  method private check_summary_name (summary:function_summary_int) (fname:string) =
    if fname = summary#get_name then () else
      raise (BCH_failure (LBLOCK [ STR "File name " ; STR fname ; 
				   STR " is not the same as summary name : " ;
				   STR summary#get_name ]))

  method private check_aw_referred_name (node:xml_element_int) (name:string) (fname:string) =
    if name = fname then
      raise_xml_error node
	(LBLOCK [ STR "Name and referred name are the same in " ; STR fname ])

  method private get_demangled_name (name:string) =
    let dname = demangle name in if dname = name then "" else " (" ^ dname ^ ")"

  method private read_jni_function_summary_string (index:int) (xstring:string) =
    let doc = readXmlDocumentString xstring in
    let root = doc#getRoot in
    if root#hasOneTaggedChild "jnifun" then
      let node = root#getTaggedChild "jnifun" in
      if node#hasNamedAttribute "name" then
	let summary = read_xml_function_summary node in
	begin
	  H.add jnisummaries summary#get_jni_index summary ;
	  chlog#add "jni summary" 
	    (LBLOCK [ STR "Jni index " ; INT index ; STR ": " ; STR summary#get_name ])
	end
      else if node#hasOneTaggedChild "refer-to" then
	self#read_template_jni_summary node index
      else
	raise_xml_error node
	  (LBLOCK [ STR "Invalid jni summary for index " ; INT index ])

  method private read_template_jni_summary (node:xml_element_int) (index:int) =
    let rNode = node#getTaggedChild "refer-to" in
    let get = rNode#getAttribute in
    let prefix = get "prefix" in
    let suffix = get "suffix" in
    let templatename = prefix ^ suffix in
    let typename = get "typename" in
    let jniname = prefix ^ typename ^ suffix in
    let _ = self#load_template_jni_summary templatename in
    if H.mem jnitemplates templatename then
      let base = H.find jnitemplates templatename in
      let transformer = read_xml_type_transformer rNode in
      let jnisummary = base#modify_types jniname transformer in
      begin
	chlog#add "jni typed summary" 
	  (LBLOCK [ STR jniname ; STR " for type " ; STR typename ]) ;
	chlog#add "jni summary" 
	  (LBLOCK [ STR "Jni index " ; INT index ; STR ": " ; STR jniname ]) ;
	H.add jnisummaries index jnisummary
      end
    else
      raise_xml_error node
	(LBLOCK [ STR "Templated summary for " ; STR prefix ; STR suffix ;
		  STR " not found" ])
      
  method private read_dll_function_summary_string 
    (dll:string) (fname:string) (xstring:string) =
    try
      let doc = readXmlDocumentString xstring in
      let root = doc#getRoot in
      if root#hasOneTaggedChild "libfun" then
	let node = root#getTaggedChild "libfun" in
	let _ = self#check_name node fname in
	let _ = self#check_dll node dll in
	if node#hasOneTaggedChild "refer-to" then
	  let rNode = node#getTaggedChild "refer-to" in
	  if rNode#hasNamedAttribute "char-type" then
	    self#read_aw_summary node dll fname
	  else if rNode#hasNamedAttribute "lib" then
	    self#read_alternate_summary node dll fname
	  else
	    raise_xml_error node
	      (LBLOCK [ STR "Reference in file " ; STR fname ; STR " not recognized" ])
	  else
	    let summary = read_xml_function_summary node in
	    let _ = self#check_summary_name summary fname in
	    begin
	      chlog#add "function summary"
		(LBLOCK [ STR fname ; STR " (" ; STR dll ; STR ")" ; 
			  STR (self#get_demangled_name fname) ]) ;
	      H.add dllsummaries (dll,fname) summary ;
	      H.add dllnames dll fname ;
	      self#load_summary_dependencies summary
	    end
	else if root#hasOneTaggedChild "jnifun" then
	  let node = root#getTaggedChild "jnifun" in
	  if node#hasNamedAttribute "index" then
	    let index = node#getIntAttribute "index" in
	      self#read_jni_function_summary_string index xstring ;
	  else ()
    with
    | XmlParseError (line,col,p)
    | XmlReaderError (line,col,p)
    | XmlDocumentError (line,col,p) ->
      let msg = LBLOCK [ STR "Error in file " ; STR fname ; STR ": " ; p ] in
      raise (XmlDocumentError (line,col,msg))

  method private read_so_function_summary_string (fname:string) (xstring:string) =
    try
      let doc = readXmlDocumentString xstring in
      let root = doc#getRoot in
      if root#hasOneTaggedChild "libfun" then
        let node = root#getTaggedChild "libfun" in
        let _ = self#check_name node fname in
        let summary = read_xml_function_summary node in
        let _ = self#check_summary_name summary fname in
        begin
          chlog#add "function summary" (LBLOCK [ STR fname ]) ;
          H.add sosummaries fname summary ;
        end
      else
        ()
    with
    | XmlParseError (line,col,p)
    | XmlReaderError (line,col,p)
    | XmlDocumentError (line,col,p) ->
      let msg = LBLOCK [ STR "Error in file " ; STR fname ; STR ": " ; p ] in
      raise (XmlDocumentError (line,col,msg))
      
			      
  method private read_aw_summary (node:xml_element_int) (dll:string) (fname:string) =
    let rNode = node#getTaggedChild "refer-to" in
    let rName = rNode#getAttribute "name" in
    let _ = self#check_aw_referred_name node rName fname in
    let _ = self#load_dll_library_function dll rName in
    if H.mem dllsummaries (dll,rName) then
      let base = self#get_dll_function dll rName in
      let transformer = read_xml_type_transformer rNode in
      let awsummary = base#modify_types fname transformer in
      begin
	chlog#add "aw function summary"
	  (LBLOCK [ STR fname ; STR " from " ; STR rName ]) ;
	H.add dllsummaries (dll,fname) awsummary ;
	H.add dllnames dll fname 
      end
    else
      raise_xml_error node
	(LBLOCK [ STR "Base summary for " ; STR fname ; STR " in " ; STR dll ;
		  STR " not found" ])

  method private check_alternate_name 
    (dll:string) (fname:string) (newdll:string) (newname:string) =
    if dll = newdll && fname = newname then
      raise (BCH_failure (LBLOCK [ STR "Alternate summary and original are the same: " ;
				   STR dll ; STR ", " ; STR fname ]))

  method private get_alternate_summary (rNode:xml_element_int) (rLib:string) (rName:string) =
    let has = rNode#hasNamedAttribute in
    let get = rNode#getAttribute in
    let geti = rNode#getIntAttribute in
    let alternate = self#get_dll_function rLib rName in
    if has "cc" then
      let cc = get "cc" in
      let adj = if has "adj" then Some (geti "adj") else Some 0 in
      let rApi = alternate#get_function_api in
      let rSem = alternate#get_function_semantics in
      let rDoc = alternate#get_function_documentation in
      let padj adj  = match adj with Some n -> INT n | _ -> STR "none" in
      let _ =
        chlog#add
          "modify calling convention"
          (LBLOCK [ STR "From: " ; STR rApi.fapi_calling_convention ;
                    STR " and adj: " ; padj rApi.fapi_stack_adjustment ;
                    STR " to: " ; STR cc ;
                    STR " and adj: " ; padj adj ]) in
      let newApi =
        { rApi with
          fapi_calling_convention = cc ;
          fapi_stack_adjustment = adj } in
      make_function_summary ~api:newApi ~sem:rSem ~doc:rDoc
    else
      alternate

  method private read_alternate_summary (node:xml_element_int) (dll:string) (fname:string) =
    let rNode = node#getTaggedChild "refer-to" in
    let rName = rNode#getAttribute "name" in
    let dll = self#get_internal_dll_name dll in
    let rLib = rNode#getAttribute "lib" in
    let rLib = self#get_internal_dll_name rLib in
    let _ = self#check_alternate_name dll fname rLib rName in
    let _ = self#load_dll_library_function rLib rName in
    if H.mem dllsummaries (rLib, rName) then
      let alternate = self#get_alternate_summary rNode rLib rName in
      begin
	H.add dllsummaries (dll,fname) alternate ;
	chlog#add "referred summary"
	  (LBLOCK [ STR "Retrieved summary for " ; STR dll ; STR ", " ; STR fname ;
		    STR " from " ; STR rLib ; STR ", " ; STR rName ]) ;
	H.add dllnames rLib fname
      end
    else
      raise_xml_error node
	(LBLOCK [ STR "Alternate summary for " ; STR fname ; STR " in " ; STR dll ;
		  STR " not found in " ; STR rLib ])

  method private get_internal_dll_name (dll:string) =
    let dll = String.lowercase_ascii dll in
    if String.contains dll '.' then
      string_replace '.' "_" dll
    else if dll = "ws2_32" then
      "ws2_32_dll"
    else if dll = "pe-vs-static" then
      dll
    else if String.contains dll '_' then
      dll
    else
      dll ^ "_dll"

  method has_dll_function (dll:string) (fname:string) =
    let dll = self#get_internal_dll_name dll in
    begin
      self#load_dll_library_function dll fname ;
      H.mem dllsummaries (dll,fname)
    end

  method has_so_function (fname:string) =
    begin
      self#load_so_function fname ;
      H.mem sosummaries fname
    end

  method has_lib_function (pkgs:string list) (fname:string) =
    let pkgs = List.map String.lowercase_ascii pkgs in
    let index = (String.concat "::" pkgs,fname) in
    if H.mem libsummaries index then true else
      if H.mem nolibsummaries index then false else
	let path = system_settings#get_summary_paths in
	let pkgname = String.concat "/" pkgs in    
	let filename = "rtl_lib/" ^ pkgname ^ "/" ^ fname in
	if has_summary_file path filename then
	  let xstring = get_summary_file path filename in
	  begin
	    self#read_lib_function_summary_string fname pkgname xstring  ;
	    H.mem libsummaries (String.concat "::" pkgs,fname)
	  end
	else
	  begin
	    H.add nolibsummaries index true ;
	    chlog#add "no lib function summary" (LBLOCK [ STR filename ]) ;
	    false
	  end
    

  method has_jni_function (index:int) = 
    if H.mem jnisummaries index then
      true
    else if missingjnisummaries#has index then
      false
    else
      begin
	requestedjnisummaries#add index ;
	self#load_jni_function index ;
	H.mem jnisummaries index
      end

  method private read_lib_function_summary_string 
    (fname:string) (dir:string) (xstring:string) =
    let doc = readXmlDocumentString xstring in
    let root = doc#getRoot in
    if root#hasOneTaggedChild "libfun" then
      let node = root#getTaggedChild "libfun" in
      let pkgs = String.lowercase_ascii (node#getAttribute "package") in
      let summary = read_xml_function_summary node in
      begin
	chlog#add "lib function summary"
	  (LBLOCK [ STR fname ; STR " (" ; STR dir ; STR ")" ]) ;
	H.add libsummaries (pkgs,fname) summary
      end
    else
      ch_error_log#add "error in library function"
	(LBLOCK [ STR fname ; STR " (" ; STR dir ; STR ")" ])
	  
  (* reads all summary files from the jars provided *)	
  method read_summary_files =
    let path = system_settings#get_summary_paths in
    let f fname entry =
      let basename = Filename.basename (Filename.chop_extension fname) in
      let dirname = Filename.dirname fname in
      if String.contains dirname '/' then
	self#read_lib_function_summary_string basename dirname entry
      else
	self#read_dll_function_summary_string dirname basename entry in
    List.iter (fun (_,jar) -> apply_to_xml_jar f (fun _ _ -> ()) jar) path
      
  method get_library_functions = 
    let result = ref [] in
    let _ = H.iter (fun _ v -> result := v :: !result) dllsummaries in
    let _ = H.iter (fun _ v -> result := v :: !result) jnisummaries in
    let _ = H.iter (fun _ v -> result := v :: !result) libsummaries in
    !result

  method write_xml_missing_summaries (node:xml_element_int) = 
    self#write_xml_summary_table node missing_summaries

  method write_xml_requested_summaries (node:xml_element_int) =
    self#write_xml_summary_table node requested_summaries

  method private write_xml_summary_table 
    (node:xml_element_int) (t:StringCollections.set_t StringCollections.table_t)=
    node#appendChildren
      (List.map (fun (dll,nameset) ->
           let safedll = if has_control_characters dll then "__xx__" ^ (hex_string dll) else dll in
                 let dNode = xmlElement "dll" in
                 let names = nameset#toList in
                 begin
	           dNode#appendChildren
                     (List.map (fun name ->
                          let safename  = if has_control_characters name then
                                            "__xx__"  ^ (hex_string name) else name in
	                  let nNode = xmlElement "fn" in
	                  begin nNode#setAttribute "fname" safename ; nNode end) names) ;
	           dNode#setAttribute "dllname" safedll ;
	           dNode#setIntAttribute "count" (List.length names) ;
	           dNode
                 end) t#listOfPairs)

  method search_for_library_function (name:string) =
    let path = system_settings#get_summary_paths in
    let result = List.fold_left (fun a dir ->
      match a with Some _ -> a | _ ->
	let filename = dir ^ "/" ^ name in
	if has_summary_file path filename then
	  Some dir
	else
	  None) None summary_directories in
    result

end

let function_summary_library = new function_summary_library_t

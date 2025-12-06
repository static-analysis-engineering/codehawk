(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny B. Sipma
   Copyright (c) 2023-2025 Aarno Labs LLC

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
open CHPrettyUtil
open CHTimingLog
open CHTraceResult
open CHXmlDocument
open CHXmlReader

(* cchlib *)
open CCHBasicTypes
open CCHBasicTypesXml
open CCHContext
open CCHDeclarations
open CCHDictionary
open CCHFileContract
open CCHFunctionSummary
open CCHInterfaceDictionary
open CCHSettings
open CCHUtilities

(* cchpre *)
open CCHAssignDictionary
open CCHInvariantFact
open CCHPredicateDictionary
open CCHPreTypes
open CCHProofScaffolding
open CCHVariable

module H = Hashtbl

let p2s = CHPrettyUtil.pretty_to_string
let (let*) x f = CHTraceResult.tbind f x

let _ =
  set_attribute_format
    "proof-obligation-statistics"
    [FAttr "size"; FANL; FAttr "context-complexity"; FANL;
     FAttr "predicate-complexity"; FANL;
     FAttr "avg-context-complexity"; FANL;
     FAttr "avg-predicate-complexity"]


let xml_error filename line column p =
  LBLOCK [
      STR "Xml error in ";
      STR filename;
      STR " (";
      INT line;
      STR ", ";
      INT column;
      STR "): ";
      p]


let create_directory dir =
  let sys_command s =
    let e = Sys.command s in
    log_info
      "System command: %s (result: %d) [%s:%d]" s e __FILE__ __LINE__ in
  let subs = nsplit '/' dir in
  let directories = List.fold_left (fun a s ->
    match (s,a) with
    | ("",[]) -> ["/"]
    | ("",_) -> a
    | (d,[]) -> [d]
    | (d,["/"]) -> ["/" ^ d]
    | (d,h::_) -> (h ^ "/" ^ d) :: a) [] subs in
  List.iter
    (fun d ->
      if Sys.file_exists d then
        ()
      else
        sys_command (Filename.quote_command "mkdir" [d]))
    (List.rev directories)


let get_cchpath () =
  let tgtpath = system_settings#get_targetpath in
  Filename.concat tgtpath (system_settings#get_projectname ^ ".cch")


let get_analysisresults_path () =
  Filename.concat (get_cchpath ()) "a"


let get_savedsource_path () =
  Filename.concat (get_cchpath ()) "s"


let get_cfile_path () =
  let resultspath = get_analysisresults_path () in
  let cfilename = system_settings#get_cfilename in
  if system_settings#has_cfilepath then
    let cfilepath = system_settings#get_cfilepath in
    let path = Filename.concat cfilepath cfilename in
    Filename.concat resultspath path
  else
    Filename.concat resultspath cfilename


let get_cfile_stem () =
  let filepath = get_cfile_path() in
  let filename = system_settings#get_cfilename in
  Filename.concat filepath filename


let get_logfiles_directory () =
  let cfilepath = get_cfile_path () in
  let logdir = Filename.concat cfilepath "logfiles" in
  let _ = create_directory logdir in
  logdir


let get_xml_cfile_name () =
  (get_cfile_stem ()) ^ "_cfile.xml"


let _get_xml_gxrefs_name () =
  (get_cfile_stem ()) ^ "_gxrefs.xml"


let _get_xml_tables_name () =
  (get_cfile_stem ()) ^ "_tables.xml"


let get_xml_dictionary_name () =
  (get_cfile_stem ()) ^ "_cdict.xml"


let get_xml_assignment_dictionary_name () =
  (get_cfile_stem ()) ^ "_cgl.xml"


let get_xml_predicate_dictionary_name () =
  (get_cfile_stem ()) ^ "_prd.xml"

let get_xml_contexts_name () =
  (get_cfile_stem ()) ^ "_ctxt.xml"


let get_xml_interface_dictionary_name () =
  (get_cfile_stem ()) ^ "_ixf.xml"


let _get_xml_user_assumptions_name () =
  (get_cfile_stem ()) ^ "_usr.xml"


let get_cfilelog_filename (contenttype:string) (logtype:string) =
  Filename.concat (get_logfiles_directory ()) (contenttype ^ "." ^ logtype)


let save_logfile (log:logger_int) (contenttype:string) (logtype:string) =
  let filename = get_cfilelog_filename contenttype logtype in
  file_output#saveFile filename log#toPretty


let append_to_logfile (log:logger_int) (contenttype:string) (logtype:string) =
  let filename = get_cfilelog_filename contenttype logtype in
  file_output#appendToFile filename log#toPretty


let get_cch_root ():xml_element_int =
  let appname = system_settings#get_projectname in
  let root = xmlElement "c-analysis" in
  let hNode = xmlElement "header" in
  let vNode = xmlElement "ocaml-chc-version" in
  let aNode = xmlElement "application" in
  begin
    aNode#setAttribute "file" system_settings#get_cfilename;
    (if (String.length appname) > 0 then aNode#setAttribute "app" appname);
    hNode#setAttribute "time" (current_time_to_string ());
    hNode#setAttribute "origin" "c-analyzer";
    vNode#setAttribute "chc-version" (CCHVersion.version#get_version);
    vNode#setAttribute "chc-date" (CCHVersion.version#get_date);
    root#appendChildren [hNode];
    hNode#appendChildren [vNode; aNode];
    root
  end


let read_cfile ():file =
  let filename = get_xml_cfile_name () in
  try
    let cdoc = readXmlDocument filename in
    let croot = cdoc#getRoot in
    let cNode = croot#getTaggedChild "c-file" in
    read_xml_cfile cNode
  with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
     raise (CCHFailure (xml_error filename line col p))


let save_cfile_dictionary () =
  let filename = get_xml_dictionary_name () in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let cNode = xmlElement "cfile" in
  let dNode = xmlElement "c-dictionary" in
  let declsNode = xmlElement "c-declarations" in
  begin
    cdictionary#write_xml dNode;
    cdeclarations#write_xml declsNode;
    doc#setNode root;
    cNode#appendChildren [dNode; declsNode];
    root#appendChildren [cNode];
    file_output#saveFile filename doc#toPretty
  end


let read_cfile_dictionary () =
  let filename = get_xml_dictionary_name () in
  if Sys.file_exists filename then
    try
      let cdoc = readXmlDocument filename in
      let croot = cdoc#getRoot in
      let cNode = croot#getTaggedChild "cfile" in
      let dNode = cNode#getTaggedChild "c-dictionary" in
      let declsNode = cNode#getTaggedChild "c-declarations" in
      begin
        cdictionary#reset;
        cdeclarations#reset;
        cdictionary#read_xml dNode;
        cdeclarations#read_xml declsNode
      end
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       raise (CCHFailure (xml_error filename line col p))
  else
    pr_debug [STR "Dictionary file "; STR filename; STR " not found"; NL]


let save_cfile_assignment_dictionary () =
  let filename = get_xml_assignment_dictionary_name () in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let dNode = xmlElement "assignment-dictionary" in
  begin
    assigndictionary#write_xml dNode;
    doc#setNode root;
    root#appendChildren [dNode];
    file_output#saveFile filename doc#toPretty
  end


let read_cfile_assignment_dictionary () =
  let filename = get_xml_assignment_dictionary_name () in
  if Sys.file_exists filename then
    try
      let cdoc = readXmlDocument filename in
      let croot = cdoc#getRoot in
      let cNode = croot#getTaggedChild "assignment-dictionary" in
      begin
        assigndictionary#reset;
        assigndictionary#read_xml cNode
      end
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       raise (CCHFailure (xml_error filename line col p))


let save_cfile_predicate_dictionary () =
  let filename = get_xml_predicate_dictionary_name () in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let dNode = xmlElement "po-dictionary" in
  begin
    predicate_dictionary#write_xml dNode;
    doc#setNode root;
    root#appendChildren [dNode];
    file_output#saveFile filename doc#toPretty
  end


let read_cfile_predicate_dictionary () =
  let filename = get_xml_predicate_dictionary_name () in
  if Sys.file_exists filename then
    try
      let cdoc = readXmlDocument filename in
      let croot = cdoc#getRoot in
      let cNode = croot#getTaggedChild "po-dictionary" in
      begin
        predicate_dictionary#reset;
        predicate_dictionary#read_xml cNode
      end
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       raise (CCHFailure (xml_error filename line col p))


let save_cfile_interface_dictionary () =
  let filename = get_xml_interface_dictionary_name () in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let dNode = xmlElement "interface-dictionary" in
  begin
    interface_dictionary#write_xml dNode;
    doc#setNode root;
    root#appendChildren [dNode];
    file_output#saveFile filename doc#toPretty
  end


let read_cfile_interface_dictionary () =
  let filename = get_xml_interface_dictionary_name () in
  if Sys.file_exists filename then
    try
      let cdoc = readXmlDocument filename in
      let croot = cdoc#getRoot in
      let cNode = croot#getTaggedChild "interface-dictionary" in
      begin
        interface_dictionary#reset;
        interface_dictionary#read_xml cNode
      end
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       raise (CCHFailure (xml_error filename line col p))


let save_cfile_context () =
  let filename = get_xml_contexts_name () in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let cNode = xmlElement "c-contexts" in
  begin
    ccontexts#write_xml cNode;
    doc#setNode root;
    root#appendChildren [cNode];
    file_output#saveFile filename doc#toPretty
  end


let read_cfile_context () =
  let filename = get_xml_contexts_name () in
  if Sys.file_exists filename then
    try
      let cdoc = readXmlDocument filename in
      let croot = cdoc#getRoot in
      let cNode = croot#getTaggedChild "c-contexts" in
      begin
        ccontexts#reset;
        ccontexts#read_xml cNode
      end
    with
    | XmlDocumentError (line, col, p)
      | XmlParseError (line, col, p) ->
       raise (CCHFailure (xml_error filename line col p))


let get_function_filename (fname:string) (ext:string) =
  let cfilename = system_settings#get_cfilename in
  let cfnspath = Filename.concat (get_cfile_path ()) "functions" in
  let _ = create_directory cfnspath in
  let cfnpath = Filename.concat cfnspath fname in
  let _ = create_directory cfnpath in
  let name = cfilename ^ "_" ^ fname ^ "_" ^ ext ^ ".xml" in
  Filename.concat cfnpath name


let get_semantics_filename (fname:string) =
  get_function_filename fname "cfun"


let get_chif_filename (fname:string) =
  get_function_filename fname "chif"


let _get_invs_filename (fname:string) =
  get_function_filename fname "invs"


let get_ppo_filename (fname:string) =
  get_function_filename fname "ppo"


let get_spo_filename (fname:string) =
  get_function_filename fname "spo"


let get_api_filename (fname:string) =
  get_function_filename fname "api"


let get_analysis_digest_filename (fname: string) =
  get_function_filename fname "adg"


let get_pod_filename (fname:string) =
  get_function_filename fname "pod"


let get_invs_filename (fname:string) =
  get_function_filename fname "invs"


let get_vars_filename (fname:string) =
  get_function_filename fname "vars"


let save_chif (fname:string) (chif:pretty_t) =
  let filename = get_chif_filename fname in
  file_output#saveFile filename chif


let read_function_semantics (fname:string):fundec =
  let filename = get_semantics_filename fname in
  try
    let doc = readXmlDocument  filename in
    let fNode = doc#getRoot#getTaggedChild "function" in
    read_xml_function_definition fNode
  with
  | XmlDocumentError (line,col,p)
    | XmlParseError (line,col,p) ->
     let name = system_settings#get_cfilename ^ ":" ^ fname in
     raise (CCHFailure (xml_error name line col p))


let save_ppos (fname:string) =
  let filename = get_ppo_filename fname in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let fnode = xmlElement "function" in
  begin
    proof_scaffolding#write_xml_ppos fnode fname;
    fnode#setAttribute "fname" fname;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end


let read_ppos (fname:string) =
  let filename = get_ppo_filename fname in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let root = doc#getRoot in
      let fnode = root#getTaggedChild "function" in
      proof_scaffolding#read_xml_ppos fnode fname
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       raise (CCHFailure (xml_error filename line col p))
  else
    ()


let save_spos (fname:string) =
  let filename = get_spo_filename fname in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let fnode = xmlElement "function" in
  begin
    proof_scaffolding#write_xml_spos fnode fname;
    fnode#setAttribute "fname" fname;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end


let read_spos (fname:string) =
  let filename = get_spo_filename fname in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let root = doc#getRoot in
      let fnode = root#getTaggedChild "function" in
      proof_scaffolding#read_xml_spos fnode fname
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       raise (CCHFailure (xml_error filename line col p))
    | Failure s ->
       raise
         (CCHFailure
            (LBLOCK [
                 STR "Failure: ";
                 STR s;
                 STR " in read spos in file ";
                 STR filename;
                 STR ", in function ";
                 STR fname]))
  else
    ()


let save_podictionary (fname:string) =
  let filename = get_pod_filename fname in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let fnode = xmlElement "function" in
  try
    begin
      proof_scaffolding#write_xml_pod fnode fname;
      fnode#setAttribute "fname" fname;
      doc#setNode root;
      root#appendChildren [fnode];
      file_output#saveFile filename doc#toPretty
    end
  with
  | Failure s ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "Failure: "; STR s;
               STR " in save podictionary for ";
               STR fname]))


let read_podictionary (fname:string) (fdecls:cfundeclarations_int) =
  let filename = get_pod_filename fname in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let root = doc#getRoot in
      let fnode = root#getTaggedChild "function" in
      proof_scaffolding#read_xml_pod fnode fname fdecls
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       begin
         ch_error_log#add
           "podictionary: xml error"
           (LBLOCK [
                STR filename;
                STR ": (";
                INT line;
                STR ",";
                INT col;
                STR "): ";
                p]);
         raise (CCHFailure (xml_error filename line col p))
       end
    | CCHFailure p ->
       begin
         ch_error_log#add
           "podictionary: read failure"
           (LBLOCK [STR filename; STR ": "; p]);
         raise (CCHFailure p)
       end
    | Failure s ->
       begin
         ch_error_log#add
           "podictionary: read failure"
           (LBLOCK [STR filename; STR ": "; STR s]);
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Failure: ";
                   STR s;
                   STR " in read podictionary for ";
                   STR fname]))
       end
  else
    proof_scaffolding#initialize_pod fname fdecls


let save_analysis_digests (fname: string) =
  let filename = get_analysis_digest_filename fname in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let fnode = xmlElement "function" in
  begin
    proof_scaffolding#write_xml_analysis_digests fnode fname;
    fnode#setAttribute "fname" fname;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end


let read_analysis_digests (fname: string): unit traceresult =
  let filename = get_analysis_digest_filename fname in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let root  = doc#getRoot in
      let fnode = root#getTaggedChild "function" in
      let* _ = proof_scaffolding#read_xml_analysis_digests fnode fname in
      Ok ()
    with
    | XmlDocumentError (line, col, p)
      | XmlParseError (line, col, p) ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__);
              "Xml parse error in " ^ filename ^ ": ("
              ^ (string_of_int line) ^ ", "
              ^ (string_of_int col) ^ "): "
              ^ (p2s p)]
    | Failure s ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__);
              "Failure in reading analysis digest file for "
              ^ fname
              ^ " with filename "
              ^ filename ^ ": " ^ s]
  else
    Ok ()


let read_proof_files (fname:string) (fdecls:cfundeclarations_int) =
  begin
    read_podictionary fname fdecls;
    read_ppos fname;
    read_spos fname
  end


let save_proof_files (fname:string) =
  begin
    save_ppos fname;
    save_spos fname;
    save_podictionary fname
  end


let save_api (fname:string) =
  let filename = get_api_filename fname in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let fnode = xmlElement "function" in
  try
    begin
      proof_scaffolding#write_xml_api fnode fname;
      fnode#setAttribute "fname" fname;
      doc#setNode root;
      root#appendChildren [fnode];
      file_output#saveFile filename doc#toPretty
    end
  with
  | Failure s ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "Failure: ";
               STR s;
               STR " in save api for ";
               STR fname]))


let read_api (fname:string) (fdecls:cfundeclarations_int) =
  let filename = get_api_filename fname in
  let _ =
    if Sys.file_exists filename then
      try
        let doc = readXmlDocument filename in
        let root = doc#getRoot in
        let fnode = root#getTaggedChild "function" in
        proof_scaffolding#read_xml_api fnode fname
      with
      | XmlDocumentError (line,col,p)
        | XmlParseError (line,col,p) ->
         raise (CCHFailure (xml_error filename line col p))
      | Failure s ->
         raise
           (CCHFailure
              (LBLOCK [
                   STR "Failure: ";
                   STR s;
                   STR " in read api for ";
                   STR fname]))
    else
      () in
  proof_scaffolding#retrieve_contract_preconditions fdecls fname


let save_vars (fname:string) (varmgr:variable_manager_int) =
  let filename = get_vars_filename fname in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let fnode = xmlElement "function" in
  try
    begin
      varmgr#write_xml fnode;
      fnode#setAttribute "fname" fname;
      doc#setNode root;
      root#appendChildren [fnode];
      file_output#saveFile filename doc#toPretty
    end
  with
  | Failure s ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "Failure ";
               STR s;
               STR " in save vars for ";
               STR fname]))


let read_vars
      (fname:string) (fdecls:cfundeclarations_int):variable_manager_int =
  let filename = get_vars_filename fname in
  try
    let optnode =
      if Sys.file_exists filename then
        let doc = readXmlDocument filename in
        let root = doc#getRoot in
        Some (root#getTaggedChild "function")
      else
        None in
    mk_variable_manager optnode fdecls
  with
  | Failure s ->
     raise
       (CCHFailure
          (LBLOCK [
               STR "Failure ";
               STR s;
               STR " in read vars for ";
               STR fname]))


let save_invs (fname:string) (invio:invariant_io_int) =
  let filename = get_invs_filename fname in
  let doc = xmlDocument () in
  let root = get_cch_root () in
  let fnode = xmlElement "function" in
  begin
    invio#write_xml fnode;
    fnode#setAttribute "fname" fname;
    doc#setNode root;
    root#appendChildren [fnode];
    file_output#saveFile filename doc#toPretty
  end


let read_invs (fname:string) (vard:vardictionary_int) :invariant_io_int =
  let filename = get_invs_filename fname in
  let optnode =
    if Sys.file_exists filename then
      let doc = readXmlDocument filename in
      let root = doc#getRoot in
      Some (root#getTaggedChild "function")
    else
      None in
  mk_invariant_io optnode vard


(* --- Currently not used --- *)

let get_target_files_name ():string = ""
  (* Currently not used
  Filename.concat system_settings#get_path "target_files.xml" *)

let read_target_files () =
  let filename = get_target_files_name () in
  if Sys.file_exists filename then
    let doc = readXmlDocument filename in
    let root = doc#getRoot in
    let xfiles = root#getTaggedChild "c-files" in
    List.map
      (fun n -> (n#getIntAttribute "id", n#getAttribute "name"))
      (xfiles#getTaggedChildren "c-file")
  else
    raise
      (CCHFailure
         (LBLOCK [STR "File "; STR filename; STR " not found"]))


let get_cfile_basename ():string = ""


let get_contractfile_basename ():string =
  try
    Filename.concat
      system_settings#get_contractpath system_settings#get_cfilename
  with
  | _ ->
    begin
      ch_error_log#add
        "chop extension"
        (LBLOCK [
             STR " Failed to find file : ";
             STR system_settings#get_cfilename]);
      raise (CCHFailure (STR (system_settings#get_cfilename)))
    end


let  get_global_contract_filename ():string =
  Filename.concat system_settings#get_contractpath "globaldefs.xml"


let get_src_directory ():string = ""


let save_cfile_logfile
      (log:logger_int) (contenttype:string) (logtype:string) =
  if log#size > 0 then
    let filename = get_cfilelog_filename contenttype logtype in
    file_output#saveFile filename log#toPretty
  else
    ()


let get_xml_summaryresults_name () = ""


let get_xml_file_contract_name () =
  (get_contractfile_basename ()) ^ "_c.xml"


let read_global_contract () =
  if system_settings#has_contractpath then
    let filename = get_global_contract_filename () in
    if Sys.file_exists filename then
      try
        let doc = readXmlDocument filename in
        let root = doc#getRoot in
        let node = root#getTaggedChild "global-definitions" in
        let _ =
          if node#hasOneTaggedChild "global-assumptions" then
            let gasnode = node#getTaggedChild "global-assumptions" in
            global_contract#read_xml gasnode in
        if node#hasOneTaggedChild "library-function-summaries" then
          let libnode = node#getTaggedChild "library-function-summaries" in
          List.iter (fun n ->
              let name = n#getAttribute "name" in
              function_summary_library#read_xml_substitute_summary n name)
            (libnode#getTaggedChildren "function-summary")
        else
          ()
      with
      | XmlDocumentError (line, col, p)
        | XmlParseError (line, col, p) ->
         raise (CCHFailure (xml_error filename line col p))


let read_cfile_contract () =
  let _ = log_info "read_cfile_contract [%s:%d]" __FILE__ __LINE__ in
  if system_settings#has_contractpath then
    let _ =
      log_info "Trying to get the contract filename [%s:%d]" __FILE__ __LINE__ in
    let filename = get_xml_file_contract_name () in
    let _ =
      log_info
        "Checking xml contract file %s [%s:%d]" filename __FILE__ __LINE__ in
    let _ = read_global_contract () in
    if Sys.file_exists filename then
      let _ =
        log_info
          "Retrieving contract file %s [%s:%d]"
          filename __FILE__ __LINE__ in
      try
        let doc = readXmlDocument filename in
        let root = doc#getRoot in
        let node = root#getTaggedChild "cfile" in
        begin
          file_contract#reset;
          file_contract#read_xml node
        end
      with
      | XmlDocumentError (line, col, p)
        | XmlParseError (line, col, p) ->
         raise (CCHFailure (xml_error filename line col p))
    else
      log_info "No contract found [%s:%d]" __FILE__ __LINE__


let save_cfile_contract () = ()
                               (*
  if system_settings#has_contractpath then
    let filename = get_xml_file_contract_name () in
    let filename = filename  in
    let doc = xmlDocument () in
    let root = get_cch_root () in
    let cNode = xmlElement "cfile" in
    begin
      file_contract#write_xmlx cNode;
      doc#setNode root;
      root#appendChildren [cNode];
      file_output#saveFile filename doc#toPretty
    end
                                *)

                               (*
let get_cfilename_basename (s:string):string = ""
  try
    Filename.concat system_settings#get_path (Filename.chop_extension s)
  with
  | _ ->
     begin
       ch_error_log#add
         "chop extension"
         (LBLOCK [STR system_settings#get_cfilename]);
       raise (CCHFailure (STR (system_settings#get_cfilename)))
     end


let read_named_cfile_dictionary (s:string) = ()
  let _ = cdictionary#reset in
  let _ = cdeclarations#reset in
  let filename = (get_cfilename_basename s) ^ "_cdict.xml" in
  if Sys.file_exists filename then
    try
      let cdoc = readXmlDocument filename in
      let croot = cdoc#getRoot in
      let cNode = croot#getTaggedChild "cfile" in
      let dNode = cNode#getTaggedChild "c-dictionary" in
      let declsNode = cNode#getTaggedChild "c-declarations" in
      begin
        cdictionary#read_xml dNode;
        cdeclarations#read_xml declsNode
      end
    with
    | XmlDocumentError (line,col,p)
      | XmlParseError (line,col,p) ->
       raise (CCHFailure (xml_error filename line col p))
  else
    pr_debug [STR "Dictionary file "; STR filename; STR " not found"; NL]


let get_xml_cfile (s:string):file = ()
  let _ = read_named_cfile_dictionary s in
  let filename = (get_cfilename_basename s) ^ "_cfile.xml" in
  try
    let cdoc = readXmlDocument filename in
    let croot = cdoc#getRoot in
    let cNode = croot#getTaggedChild "c-file" in
    read_xml_cfile cNode
  with
  | XmlDocumentError (line,col,p)
  | XmlParseError (line,col,p) ->
     raise (CCHFailure (xml_error filename line col p))
                            *)

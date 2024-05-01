(* =============================================================================
   CodeHawk C Analyzer Parser using CIL
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny B. Sipma
   Copyright (c) 2022-2024 Aarno Labs LLC

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

(* cil *)
open GoblintCil
open Frontc

(* chlib *)
open CHCommon
open CHPretty

(* chutil *)
open CHFileIO
open CHPrettyUtil
open CHTiming
open CHTimingLog
open CHUtil
open CHXmlDocument

(* cchcil *)
open CHCilDeclarations
open CHCilDictionary
open CHCilFileUtil
open CHCilWriteXml


let projectpath = ref ""
let targetdirectory = ref ""
let filename = ref ""
let filterfiles = ref true
let keepUnused = ref false

let version = "CP1.1"

let set_targetdirectory s =  targetdirectory := s

let set_projectpath s =
  begin
    projectpath := s;
    CHCilFileUtil.project_path_prefix := s
  end

let speclist = [
    ("-projectpath", Arg.String set_projectpath,
     "path to the project base directory");
    ("-targetdirectory", Arg.String set_targetdirectory,
     "directory to store the generated xml files");
    ("-nofilter", Arg.Unit (fun () -> filterfiles := false),
     "don't filter out functions in files starting with slash");
    ("-keepUnused",
     Arg.Set keepUnused, "keep unused type and function definitions")]


let usage_msg =
  "parseFile  -projectpath <..> -targetdirectory <..> <absolute filename of preprocessed source file>"

let read_args () = Arg.parse speclist (fun s -> filename := s) usage_msg


let check_targetdirectory () =
  if !targetdirectory = "" then
    begin
      log_warning
        "Target directory not set: using current directory as target directory";
      targetdirectory := Sys.getcwd ()
    end


let get_cch_root (filename:string):xml_element_int =
  let root = xmlElement "c-analysis" in
  let hNode = xmlElement "header" in
  let cNode = xmlElement "created" in
  begin
    cNode#setAttribute "project-directory" !project_path_prefix;
    cNode#setAttribute "file" filename;
    cNode#setAttribute "version" version;
    cNode#setAttribute "time" (current_time_to_string ());
    root#appendChildren [hNode];
    hNode#appendChildren [cNode];
    root
  end


let sanitize_targetfilename name =
  try
    let pos = String.rindex name '.' in
    let spos1 = String.rindex_from name pos '/' in
    let spos2 = String.rindex_from name (spos1-1) '/' in
    let newname =
      (String.sub name 0 (spos2+1))
      ^ (String.sub name (pos+2) ((String.length name) - (pos+2))) in
    let _ = log_info "Change name from %s into %s" name newname in
    newname
  with
    Not_found -> name


(* Assume '/' directory separator; to be adapted for Windows *)
let create_directory dir =
  let sys_command s =
    let e = Sys.command s in
    log_info "System command %s (result: %d) [%s:%d]" s e __FILE__ __LINE__ in
  let subs = string_nsplit '/' dir in
  let directories = List.fold_left (fun a s ->
    match (s,a) with
    | ("",[]) -> ["/"]
    | ("",_) -> a
    | (d,[]) -> [d]
    | (d,["/"]) -> ["/" ^ d]
    | (d,h::_) -> (h ^ "/" ^ d) :: a) [] subs in
  List.iter (fun d ->
      if Sys.file_exists d then
        ()
      else
        sys_command (Filename.quote_command "mkdir" [d]))
    (List.rev directories)


let get_target_name () =
  let _ = check_targetdirectory () in
  let suffix = string_suffix !filename (String.length !projectpath) in
  let target = Filename.chop_extension suffix in
  let target = sanitize_targetfilename target in
  let absoluteTarget = !targetdirectory ^ target in
  let _ = create_directory (Filename.dirname absoluteTarget) in
  let target =
    if target.[0] = '/' then
      String.sub target 1 ((String.length target) - 1)
    else
      target in
  (target, absoluteTarget)


let get_target_file_name () =
  let (target, absoluteTarget) = get_target_name () in
  let filename = Filename.chop_extension (Filename.basename !filename) in
  let target = Filename.concat target filename in
  let absoluteTarget = Filename.concat absoluteTarget filename in
  let _ = create_directory absoluteTarget in
  (target, absoluteTarget)


let save_cil_xml_file target (f: GoblintCil.file) (xfilename: string) =
  let doc = xmlDocument () in
  let root = get_cch_root target in
  let fileNode = xmlElement "c-file" in
  begin
    doc#setNode root;
    root#appendChildren [fileNode];
    write_xml_cfile fileNode f target;
    log_info "Saving cfile %s [%s:%d]" xfilename __FILE__ __LINE__;
    file_output#saveFile xfilename doc#toPretty
  end


let save_dictionary_xml_file target (xfilename: string) =
  let doc = xmlDocument () in
  let root = get_cch_root target in
  let dnode = xmlElement "cfile" in
  let fileNode = xmlElement "c-dictionary" in
  let declsNode = xmlElement "c-declarations" in
  begin
    doc#setNode root;
    dnode#appendChildren [fileNode; declsNode];
    root#appendChildren [dnode];
    cildictionary#write_xml fileNode;
    cildeclarations#write_xml declsNode;
    log_info "Saving dictionary file %s [%s:%d]" xfilename __FILE__ __LINE__;
    file_output#saveFile xfilename doc#toPretty
  end


let cil_function_to_file target (f: fundec) (dir: string) =
  let doc = xmlDocument () in
  let root = get_cch_root target in
  let functionNode = xmlElement "function" in
  let sys_command s =
    let e = Sys.command s in
    log_info "System command %s (result: %d) [%s:%d]" s e __FILE__ __LINE__ in
  let _ =
    if Sys.file_exists dir then
      ()
    else
      sys_command (Filename.quote_command "mkdir" [dir]) in
  let fndir = Filename.concat dir f.svar.vname in
  let _ =
    if Sys.file_exists fndir then
      ()
    else
      sys_command (Filename.quote_command "mkdir" [fndir]) in
  let basename = Filename.chop_extension (Filename.basename !filename) in
  let ffilename =
    Filename.concat
      fndir (String.concat "_" [basename; f.svar.vname ; "cfun.xml"]) in
  begin
    doc#setNode root;
    write_xml_function_definition functionNode f target;
    root#appendChildren [functionNode];
    file_output#saveFile ffilename doc#toPretty;
    log_info "Saved function file %s" ffilename
  end


let save_xml_file f =
    let (target, absoluteTarget) = get_target_file_name () in
    let xmlfilename = absoluteTarget ^ "_cfile.xml"  in
    let dictionaryfilename = absoluteTarget ^ "_cdict.xml" in
    let _ = (if !keepUnused then () else RmUnused.removeUnused f) in
    let _ = Cfg.computeFileCFG f in
    let fns =
      List.fold_left (fun a g ->
          match g with
          | GFun (fdec, _loc) -> fdec :: a | _ -> a) [] f.globals in
    let fns =
      if !filterfiles then
        List.filter (fun fdec ->
            not ((String.get fdec.svar.vdecl.file 0) = '/')) fns
      else
        fns in
    let fnsTarget = Filename.concat (Filename.dirname absoluteTarget) "functions" in
    begin
      List.iter (fun f -> cil_function_to_file target f fnsTarget) fns;
      log_info "Saved %d function(s) [%s:%d]" (List.length fns) __FILE__ __LINE__;
      save_cil_xml_file (Filename.dirname target) f xmlfilename;
      save_dictionary_xml_file target dictionaryfilename;
    end


let main () =
  try
    let _ = read_args () in
    let _ = set_log_level "DEBUG" in
    let cilfile = Frontc.parse !filename () in
    let _ = log_info "Parsed %s [%s:%d]" !filename __FILE__ __LINE__ in
    save_xml_file cilfile
  with
  | ParseError s ->
     begin
       pr_debug [
           STR "Error when parsing (CIL) ";
           STR !filename;
           STR ": ";
           STR s;
           NL];
       exit 1
     end
  | CHFailure p ->
     begin
       pr_debug [STR "Error when parsing "; STR !filename; STR ": "; p; NL];
       exit 1
     end
  | e ->
     begin
       pr_debug [
           STR "Error when parsing (other exception): "; STR !filename; NL];
       pr_debug [STR (Printexc.to_string e); NL];
       exit 1
     end


let _ = Printexc.print main ()

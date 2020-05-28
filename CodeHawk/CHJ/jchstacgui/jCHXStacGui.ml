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

open Gc
   
(* chlib *)
open CHPretty

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHDictionary
open JCHFile
open JCHRawClass

(* jchpre *)
open JCHApplication
open JCHCallgraphBase
open JCHCHAUtil
open JCHClassLoader
open JCHIFSystem
open JCHMethodImplementations
open JCHPreFileIO
open JCHSystemSettings

(* jchstacgui *)
open JCHCostValues

let classnames = ref []

let version_info = "CodeHawk Java Analyzer (STAC): version 0.7 (Feb 6, 2018)"

let speclist = [
  ("-summaries", Arg.String system_settings#add_summary_classpath_unit,"summary jar file") ;
  ("-classpath", Arg.String system_settings#add_classpath_unit, "sets java classpath") ;
  ("-classes", Arg.Rest (fun s -> classnames := s:: !classnames), "classes to view") ;
  ("-jars", Arg.Rest app#add_application_jar, "jars with classes to view") ;
  ("-resultsdir", Arg.String system_settings#set_results_directory, 
   "directory with analysis results (default current directory)") ;
  ("-exclude_pkg_prefix", Arg.String system_settings#add_pkg_exclude,
   "skip classes with given package prefix")
]

let is_file f =
  try
    (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _,_) -> false


let usage_message = 
  "\n" ^ (string_repeat "-~" 40) ^
    "\n" ^ version_info ^ 
    "\n" ^ (string_repeat "-~" 40) ^
    "\n\n === Requires graphviz (dot) to be installed === " ^
    "\n\nInvoke with" ^
    "\n   chj_gui -summaries <path>/jdk.jar  <class file> or" ^
    "\n   chj_gui -summaries <path>/jdk.jar -classes <class files> or" ^
    "\n   chj_gui -summaries <path>/jdk.jar -jars <jar-files>" ^
    "\n\nOptional arguments:" ^
    "\n   -resultsdir: the directory that holds the analysis results (defauld cwd)" ^
    "\n"

let read_args () = 
  Arg.parse speclist (fun s -> classnames := s :: !classnames) usage_message

let is_included filename xcludes =
  not (List.exists (fun s ->
           let slen = String.length s in
           (String.length filename) > slen && (String.sub filename 0 slen) = s) xcludes)
    

let load classname =
  if Filename.check_suffix classname "class" then
    if is_file classname then
      let ch = IO.input_channel (open_in_bin classname) in
      let md5 = Digest.file classname in
      let origin = classname in
      let c = JCHParse.parse_class_low_level ch origin md5 in
      let _ = IO.close_in ch in
      app#add_class (JCHRaw2IF.low2high_class c) 
    else
      raise (JCH_failure (LBLOCK [ STR "Error: " ; STR classname ; STR " not found" ]))
  else
    let cname = make_cn classname in
    load_class (get_class system_settings#get_classpath cname)

let main () =
  let _ = pr_debug [ STR usage_message ] in
  try
    let _ = read_args () in
    let xcludes = system_settings#get_pkg_excludes in
    begin
      read_dictionary () ;
      read_jt_dictionary () ;
      Gc.major () ;
      read_excluded_classes () ;
      List.iter load !classnames ;
      (let classnames =
         List.fold_left (fun acc jar ->
             (load_classes_in_jar ~xcludes jar) @ acc) [] app#get_application_jars in
       let _ = process_classes () in
       let bcmethods = List.filter (fun m -> m#has_bytecode) app#get_methods in
       pr_debug [ STR "Loaded " ; INT (List.length bcmethods) ; STR " methods with bytecode" ;
                  STR " in " ; INT (List.length classnames) ; STR " classes" ; NL ]) ;
      method_signature_implementations#initialize ;
      load_user_class_files () ;
      costvalues#load ;
      read_taint_origins () ;
      set_main_method () ;
      set_method_targets () ;
      JCHGui.run_gui () 
    end
  with
  | CHCommon.CHFailure p
    | JCHBasicTypes.JCH_failure p ->
     begin pr_debug [ STR "Failure " ; p ; NL ] ; exit 0 end
    
let _ = Printexc.print main ()

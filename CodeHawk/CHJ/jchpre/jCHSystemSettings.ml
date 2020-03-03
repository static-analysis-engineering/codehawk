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

open Unix

(* chlib *)
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil
open CHUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHFile

(* jchpre *)
open JCHPreAPI

(* Convert standard Unix time representation to a string *)
let time_to_string (f:float):string = 
  let tm = Unix.localtime f in
  let sp ip = if ip < 10 then LBLOCK [ STR "0" ; INT ip ] else INT ip in
  let p = LBLOCK [ sp (tm.tm_mon + 1) ; STR "/" ; sp tm.tm_mday ; 
		   STR "/" ; sp (tm.tm_year + 1900) ;
		   STR " " ; sp tm.tm_hour ; 
		   STR ":" ; sp tm.tm_min ; 
		   STR ":" ; sp tm.tm_sec ] in
    string_printer#print p

let jdk_jar_version = ref "unknown"
let get_jdk_jar_version () = !jdk_jar_version

let codehawk_version = ref "3.03"
let codehawk_build_time = time_to_string (Unix.gettimeofday ())

let get_codehawk_version () = !codehawk_version
let get_codehawk_build_time () = codehawk_build_time

let verbose = ref false
let set_verbose () = verbose := true
let get_verbose () = !verbose

let record_jdk_jar_version s =
  let class_path = class_path s in
  match class_path with
    [ JarFile (_, jar) ] -> 
      begin
	try
	  let versionDoc = Zip.read_entry jar (Zip.find_entry jar "jdk_jar_version.xml") in
	  let doc = readXmlDocumentString versionDoc in
	  let root = doc#getRoot in
	  if root#hasOneTaggedChild "header" then
	    let xheader = root#getTaggedChild "header" in
	    let version = xheader#getAttribute "version" in
	    let numFiles = xheader#getIntAttribute "files" in
	    let jdkJarDate = xheader#getAttribute "date" in
	    begin
	      jdk_jar_version := version ;
	      chlog#add
                "jdk summaries"
                (LBLOCK [ STR "Jdk summaries: " ; INT numFiles ; STR " files. " ; 
			  STR "Created: " ; STR jdkJarDate ])
	    end
	  else
	    ch_error_log#add
              "jdk summaries"
              (LBLOCK [ STR "Invalid jdk_jar_version.xml file "])
	with _ ->
	  begin
	    ch_error_log#add
              "jdk summaries"
              (LBLOCK [ STR "jdk.jar does not contain jdk_jar_version.xml" ]) ;
	  end
      end
  | _ -> 
     ch_error_log#add
       "jdk summaries"
       (LBLOCK [ STR "Invalid class path to function summaries" ])
      
      
let jdk_jars = [ 
  "alt-rt.jar" ;
  "charsets.jar" ;
  "deploy.jar" ;
  "dnsns.jar" ;
  "dt.jar" ;
  "javafx-doclet.jar" ;
  "javafx-mx.jar" ;
  "javaws.jar" ;
  "jce.jar" ;
  "jconsole.jar" ;
  "jfr.jar" ;
  "jfxrt.jar" ;
  "jsse.jar" ;
  "localedata.jar" ;
  "management-agent.jar" ;
  "plugin.jar" ;
  "resources.jar" ;
  "rt.jar" ;
  "sa-jdi.jar" ;
  "sunec.jar" ;
  "sunjce_provider.jar" ;
  "sunpkcs11.jar" ;
  "tools.jar" ;
  "zipfs.jar" ]
  
class system_settings_t:system_settings_int =
object (self)

  val mutable classpath = None
  val mutable classpath_units = []
  val mutable summary_classpath_units = []
  val mutable preanalyzed_classpath_units = []
  val mutable preanalyzed_dir = ""
  val mutable start_time = 0.0
  val mutable verbose = false
  val mutable log_missing_classes = true
  val mutable logfile = Some "system-logfile"
  val mutable output_directory = "."
  val mutable project_name = "ch_analysis"
  val mutable print_chif = false
  val mutable results_dir = "."
  val excludedclasses = new IntCollections.set_t
  val mutable max_instructions = -1
  val mutable package_excludes = []   (* classes with this package prefix are not loaded *)

  method set_logfile (name:string) = logfile <- Some name

  method disable_logging_missing_classes = log_missing_classes <- false

  method is_logging_missing_classes_enabled = log_missing_classes
                                   
  method add_pkg_exclude s =
    package_excludes <- (string_replace '.' "/" s) :: package_excludes

  method get_pkg_excludes = package_excludes

  method set_output_directory (name:string) =
    let _ = if not (Sys.file_exists name) then Unix.mkdir name 0o750 in
    output_directory <- name

  method set_results_directory (name:string) =
    let _ = if not (Sys.file_exists name) then
	raise (JCH_failure 
		 (LBLOCK [ STR "Results directory " ; STR name ; STR " not found" ])) in
    results_dir <- name

  method set_excluded_classes (cnixs:int list) = excludedclasses#addList cnixs

  method set_max_instructions (i:int) = max_instructions <- i

  method get_max_instructions = max_instructions

  method has_instruction_limit = max_instructions > 0

  method get_output_directory = output_directory

  method get_results_directory = results_dir

  method set_project_name (name:string) =  project_name <- name

  method get_project_name = project_name

  method set_print_chif = print_chif <- true

  method print_chif = print_chif

  method log_error (p:pretty_t) =
    match logfile with
    | Some name ->
       (try
         let msg = LBLOCK [ STR (current_time_to_string ()) ; NL ; INDENT (2, p) ; NL ] in
         file_output#appendToFile name msg
       with
         _ ->
         ch_error_log#add "error in log_error" p)
    | _ -> ()

  method set_verbose = verbose <- true

  method is_verbose = verbose

  method record_start_time = start_time <- Unix.gettimeofday ()

  method get_time_since_start = ((Unix.gettimeofday ()) -. start_time)

  method add_classpath_unit s = 
    if s = "" || s = " " then () else
      if not (Sys.file_exists s) then
	begin
	  pr_debug [ STR " ****** Warning: " ; STR s ; 
		     STR " not found ******************************* " ; NL ]  ;
	  ch_error_log#add "classpath" (LBLOCK [ STR "Classpath unit " ; STR s ;
						 STR " not found" ])
	end
      else
	classpath_units <- s :: classpath_units

  method add_summary_classpath_unit s = 
    if s = "" || s = " " then () else 
      if not (Sys.file_exists s) then
	pr_debug [ STR " ****** Warning: " ; STR s ; 
		   STR " not found ******************************* " ; NL ] 
      else
	let _ = record_jdk_jar_version s in
	summary_classpath_units <- s :: summary_classpath_units

  method add_preanalyzed_classpath_unit s = 
    if s = "" || s = " " then () else 
      if not (Sys.file_exists s) then
	begin
	  pr_debug [ STR " ****** Warning: " ; STR s ; 
		     STR " not found ******************************* " ; NL ] ;
	  preanalyzed_dir <- Filename.dirname s
	end
      else
	begin
	  preanalyzed_classpath_units <- s :: preanalyzed_classpath_units ;
	  preanalyzed_dir <- Filename.dirname s
	end

  method get_classpath_units = (List.rev classpath_units)

  method get_preanalyzed_directory = preanalyzed_dir

  method get_classpath_string =
    match self#get_classpath_units with
      [] -> ""
    | l -> String.concat ":" l

  method get_classpath = 
    match classpath with
    | Some cp -> cp
    | _ ->
      let sys_classpath = try Sys.getenv "CLASSPATH" with Not_found -> "" in
      let _ = pr_debug [ STR "classpath: " ; STR self#get_classpath_string ; NL ] in
      let cp = JCHFile.class_path (self#get_classpath_string ^ ":" ^ sys_classpath) in
      begin classpath <- Some cp ; cp  end
	

  method get_summary_classpath =
    let summaryString = match summary_classpath_units with [] -> "" | l -> String.concat ":" l in
    JCHFile.class_path summaryString

  method get_preanalyzed_classpath =
    let preanalyzedString = match preanalyzed_classpath_units with
      | [] -> ""
      | l -> String.concat ":" l in
    JCHFile.class_path preanalyzedString

  method is_excluded_class (cnix:int) = excludedclasses#has cnix

  method is_jdk_jar (name:string) = List.mem (Filename.basename name) jdk_jars

  method to_pretty =
    let classpath_p = pretty_print_list classpath_units (fun s -> LBLOCK [ STR s ; NL ]) "" "" "" in
    LBLOCK [  STR "Classpath" ; NL ; INDENT (5, classpath_p) ; NL ]

end

let system_settings = new system_settings_t
let pverbose l = if system_settings#is_verbose then pr_debug l else ()


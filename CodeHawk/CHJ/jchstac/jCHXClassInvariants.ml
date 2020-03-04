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
open CHCommon
open CHPretty

(* chutil *)
open CHFileIO
open CHPrettyUtil
open CHUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHFile
open JCHJTerm
open JCHRawClass

(* jchpre *)
open JCHApplication
open JCHClassLoader
open JCHIFSystem
open JCHFunctionSummary
open JCHPreFileIO
open JCHSystemSettings

(* jchsys *)
open JCHLoopUtils

module H = Hashtbl

let classname = ref ""
let methodname = ref ""

let speclist = [
  ("-summaries", Arg.String system_settings#add_summary_classpath_unit,"summary jar file") ;
  ("-classpath", Arg.String system_settings#add_classpath_unit, "sets java classpath") ;
  ("-method", Arg.String (fun s -> methodname := s), "report invariants for this method only")
]

let is_file f =
  try
    (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _,_) -> false


let usage_msg = 
  "-----------------------------------------------------------------------\n" ^
  "CodeHawk Java Analyzer: Invariant generator for individual classes\n\n" ^
  "Invoke with: \n" ^
  "  chj_class_invariants -summaries jdk.jar <class-file>\nor with\n" ^
  "  chj_class_invariants -summaries jdk.jar " ^
  "-classpath <app.jar> <fully-qualified-classname>\n\n" ^
  "Examples:\n" ^
  "  chj_class_invariants -summaries jdk.jar MyClass.class\n" ^
  "  chj_class_invariants -summaries jdk.jar -classpath myjar.jar org.mydomain.MyClass\n" ^
  "-----------------------------------------------------------------------\n"
  
let read_args () = Arg.parse speclist   (fun s -> classname := s) usage_msg

let has_invariants invs =
  List.exists (fun (_,l) -> match l with [] -> false | _ -> true) invs

let report_invariants cInfo =
  let replace_lst = [ ('(', "") ; (')', "") ; ('[', "a") ; (']',"a") ;
		      ('/', "_") ; (';', "_") ; ('<',"xx") ; ('>', "xx") ] in
  let replace = string_replace in
  let sanitize s = List.fold_left (fun sa (c,r) -> replace c r sa) s replace_lst in
  let cname = cInfo#get_class_name#simple_name in
  let mnames = H.create 3 in
  List.iter (fun ms ->
    if !methodname = "" || ms#name = !methodname then
      let msig = sanitize ms#to_signature_string in
      let msname = sanitize ms#name in
      let fname = 
	if H.mem mnames msname then
	  cname ^ "_" ^ msname ^ "_" ^ msig 
	else
	  begin H.add mnames msname true ; cname ^ "_" ^ msname end in
      let fInvs = fname ^ "_invs.txt" in
      let fBc = fname ^ "_bc.txt" in
      
      let cms = make_cms cInfo#get_class_name ms in
      let mInfo = app#get_method cms in
(*      let jproc = JCHSystem.jsystem#get_jproc_info_seq_no mInfo#get_index in *)
      let invs = [] in
      let ppInvs = ref [] in
      begin
	ppInvs := (LBLOCK [ NL ; cms#toPretty ; NL ]) :: !ppInvs ;
	(if has_invariants invs then
	    List.iter (fun (pc,invs) ->
	      match invs with
	      | [] -> ()
	      | _ -> 
		let pinvs = List.map relational_expr_to_pretty invs in
		ppInvs := 
		  LBLOCK ([ fixed_length_pretty ~alignment:StrRight (INT pc) 5 ; STR "  " ; 
			    pretty_print_list pinvs (fun p -> LBLOCK [ INDENT (3,p) ; NL ]) 
			      "" "       " "" ; NL ]) :: !ppInvs)
	      invs
	 else
	    ppInvs := LBLOCK ([ STR "  --- No invariants generated --- " ; NL ]) :: !ppInvs) ;
	pr_debug [ STR "Saving invariants and bytecode for " ; cms#toPretty ; 
		   STR " in " ; STR fInvs ; STR " and " ; STR fBc ; NL ] ;
	file_output#saveFile fInvs (LBLOCK (List.rev !ppInvs)) ;
	file_output#saveFile fBc mInfo#bytecode_to_pretty 
      end)
    cInfo#get_methods_defined
    
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

let main () =
  try
    let _ = read_args () in
    let cn = load () in
    let _ = process_classes () in
    if app#has_class cn then
      let cInfo = app#get_class cn in
      begin
	let _ = translate_base_system () in
	JCHAnalysis.analyze_system 0 false 3 100 10 true 100 500 true;
	report_invariants cInfo
      end
    else
      pr_debug [ STR "Class " ; STR !classname ; STR " could not be loaded" ; NL ]
  with
  | CHFailure p | JCH_failure p ->
    pr_debug [ STR "Error in processing class: " ; p ; NL ]
  | JCH_runtime_type_error p ->
    pr_debug [ STR "Runtime type error in byte code: " ; p ; NL ]
  | JCHFile.No_class_found s ->
    pr_debug [ STR "Error: Class " ; STR s ; STR " could not be found " ; NL ]

let _ = Printexc.print main ()

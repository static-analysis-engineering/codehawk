(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2025  Henny B. Sipma

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

(* jchlib *)
open JCHBasicTypes
open JCHDictionary
open JCHFile
open JCHRawClass

(* jchpre *)
open JCHApplication
open JCHCallgraphBase
open JCHClassLoader
open JCHIFSystem
open JCHMethodImplementations
open JCHPreFileIO
open JCHSystemSettings

module H = Hashtbl

let classname = ref ""
let methodname = ref ""

let speclist = [
    ("-summaries",
     Arg.String system_settings#add_summary_classpath_unit,"summary jar file");
    ("-classpath",
     Arg.String system_settings#add_classpath_unit, "sets java classpath");
    ("-method",
     Arg.String (fun s -> methodname := s), "report invariants for this method only")
 ]


let is_file f =
  try
    (Unix.stat f).Unix.st_kind = Unix.S_REG
  with Unix.Unix_error (Unix.ENOENT, _, _) -> false


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


let load () =
  if Filename.check_suffix !classname "class" then
    if is_file !classname then
      let ch = IO.input_channel (open_in_bin !classname) in
      let md5 = Digest.file !classname in
      let origin = !classname in
      let c = JCHParse.parse_class_low_level ch origin md5 in
      let _ = IO.close_in ch in
      begin
	app#add_class (JCHRaw2IF.low2high_class c);
	c.rc_name
      end
    else
      raise (JCH_failure (LBLOCK [STR "Error: "; STR !classname; STR " not found"]))
  else
    let cname = make_cn !classname in
    begin
      load_class (get_class system_settings#get_classpath cname);
      cname
    end

let main () =
  try
    let _ = read_args () in
    let cn = load () in
    let _ = process_classes () in
    if app#has_class cn then
      begin
        ignore(translate_base_system ());
        app#iter_methods (fun mInfo ->
            if mInfo#has_bytecode then
              pr_debug [mInfo#bytecode_to_pretty; NL; NL]
            else
              pr_debug [
                  STR "No bytecode found for "; STR mInfo#get_method_name; NL]);
	  method_signature_implementations#initialize;
	  callgraph_base#build_graph;
	  save_classnames [cn];
	  save_dictionary ();
	  save_signature_file ();
	  save_callgraph_file ();
	  save_missing_items ();
      end
    else
      pr_debug [STR "Class "; STR !classname; STR " could not be loaded"; NL]
  with
  | CHFailure p | JCH_failure p ->
     pr_debug [STR "Error in processing class: "; p; NL]
  | JCH_runtime_type_error p ->
     pr_debug [STR "Runtime type error in byte code: "; p; NL]
  | JCHFile.No_class_found s ->
     pr_debug [STR "Error: Class "; STR s; STR " could not be found "; NL]

let _ = Printexc.print main ()

(* =============================================================================
   CodeHawk C Analyzer 
   Author: A. Cody Schuffelen and Henny Sipma and Andrew McGraw
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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
open CCHFunctionSummary
open CHPretty

(* chutil *)
open CHPrettyUtil

(* cchlib *)
open CCHSettings

(* cchgui *)
open CCHPpoDialog
open CCHSystemDisplay

let source_directory = ref ""
let single_file = ref ""

let set_analysisdir s = 
    let filename = s ^ "/semantics/ktadvance" in
    if Sys.file_exists filename then
      system_settings#set_path filename
    else
      let _ = pr_debug [ STR "Could not find " ; STR filename ; STR " . Exiting. " ; NL ] in
      exit 0

let set_contractpath s =
  if Sys.file_exists s then
    system_settings#set_contractpath s
  else
    ()

let speclist = [
    ("-xpm", Arg.String set_xpm_path,"path to icon pixmaps") ;
    ("-summaries", Arg.String function_summary_library#add_summary_jar,
     "location of summary jar") ;
    ("-analysisdir", Arg.String set_analysisdir, "path to analysis directory") ;
    ("-contractpath",  Arg.String set_contractpath,"path to contracts") ;
    ("-output", Arg.String set_output_path,"directory to save system displays") ;
    ("-name", Arg.String set_application_name,"name of the application") ;
    ("-singlefile", Arg.String (fun s -> single_file := s),
     "only display results for this this c file")
  ]
             

let version_info = "CodeHawk C Analyzer (KTAdvance)" 

let usage_message =
  "\n" ^ (string_repeat "-~" 40) ^
    "\n" ^ version_info ^
    "\n" ^ (string_repeat "-~" 40) ^
    "\n\n === Requires graphviz (dot) to be installed === " ^
    "\n\nInvoke with" ^
    "\n   chc_gui -xpm <location of icon pixmaps> -summaries <path>/cchsummaries.jar" ^
    "\n   chc_gui -xpm <location of icon pixmaps> -summaries <path>/cchsummaries.jar -analysisdir <Analysis dir>" ^
    "\n"

let read_args () = Arg.parse speclist (fun s -> single_file := Filename.basename s) usage_message

let main () =
  try
    begin
      read_args () ;
      system_settings#set_filterabspathfiles false ;
      set_ppo_pixmaps () ;
      CCHGui.run_gui system_settings#get_path !single_file;
    end
  with
    | CHCommon.CHFailure p ->
      begin pr_debug [ STR "CHFailure " ; p ; NL ] ; exit 0 end
    | CCHUtilities.CCHFailure p ->
      begin pr_debug [ STR "CCHFailure " ; p ; NL ] ; exit 0 end
    | CHXmlDocument.XmlDocumentError (line,col,p) ->
       begin
         pr_debug [ STR "XmlDocumentError (" ; INT line ;
                    STR "," ; INT col ; STR ") " ; p ; NL ] ;
         exit 0
       end
     
let _ = Printexc.print main ()

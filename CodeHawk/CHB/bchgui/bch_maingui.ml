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

(* bchlib *)
open BCHBasicTypes
open BCHFunctionSummaryLibrary
open BCHPreFileIO
open BCHSystemInfo
open BCHSystemSettings

let speclist = [
  ("-summaries", Arg.String system_settings#set_summary_jar,
   "sets the directory where the summary jar files can be found") ;
  ("-appsdir",Arg.String system_settings#set_apps_dir,
   "location of application-dependent summaries and java native method signatures")
 ]

let usage_message = "gui <exe file>"
let read_args () = Arg.parse speclist system_info#set_filename usage_message

let main () =
  try
    begin
      read_args () ;
      system_info#initialize ;
      BCHGui.run_gui ()
    end
  with
    | CHCommon.CHFailure p ->
      begin pr_debug [ STR "CHFailure " ; p ; NL ] ; exit 0 end
    | CHXmlReader.XmlParseError (line,col,p)
    | BCHXmlUtil.XmlReaderError (line,col,p)
    | CHXmlDocument.XmlDocumentError (line,col,p) ->
      begin 
	pr_debug [ STR "XmlDocumentError (" ; 
		   INT line ; STR "," ; INT col ; STR ") " ; p ; NL ] ; exit 0 
      end
    | BCH_failure p -> pr_debug [ STR "BCH_failure: " ; p ; NL ]


     
let _ = Printexc.print main ()

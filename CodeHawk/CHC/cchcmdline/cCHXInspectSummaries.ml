(* =============================================================================
   CodeHawk C Analyzer 
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

(* chutil *)
open CHFileIO
open CHLogger
open CHXmlDocument

(* cchlib *)
open CCHFunctionSummary
open CCHSettings
open CCHUtilities

let jarname = ref ""

let inspect_summaries () = 
  apply_to_xml_jar (fun name s ->
      if name = "libraryvars.xml" then
        ()
      else
        function_summary_library#read_function_summary_string name s) (fun _ _ -> ()) !jarname

let usage_msg = "inspectsummaries <jar-filename>"
let speclist = [
       ("-wordsize", Arg.Int system_settings#set_wordsize,
        "set word size (e.g., 16, 32, or 64)") 
  ]
    
let read_args () = Arg.parse speclist (fun s -> jarname := s) usage_msg

let main () =
  try
    begin
      read_args () ;
      inspect_summaries () ;
      pr_debug [ function_summary_library#statistics_to_pretty ; NL ] ;
      file_output#saveFile "inspect_summaries.chlog" chlog#toPretty ;
    end
  with
  | XmlDocumentError (line,col,p) ->
      pr_debug [ STR "Xml error: (" ; INT line ; STR ", " ; INT col ; STR "): " ; p ; NL ]
  | CCHFailure p ->
    pr_debug [ STR "CHFailure: " ; p ; NL ]
      
      
let _ = Printexc.print main ()

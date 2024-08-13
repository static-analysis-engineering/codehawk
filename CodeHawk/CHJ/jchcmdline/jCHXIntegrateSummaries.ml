(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020  Kestrel Technology LLC
   Copyright (c) 2020-2024  Henny B. Sipma

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

(* standalone main program to create template class summary files *)

(* chlib *)
open CHCommon
open CHPretty

(* chutil *)
open CHLogger
open CHFileIO
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHDictionary

(* jchpre *)
open JCHClassLoader
open JCHIntegrateSummaries
open JCHSystemSettings

let name = ref ""
let save_log = ref false

let speclist =
  [("-classpath", Arg.String system_settings#add_classpath_unit,
    "sets java classpath");
   ("-apis", Arg.String set_api_summary_classpath,
    "api-summary jar file");
   ("-profiles", Arg.String set_profile_summary_classpath,
    "profile-summary jar file");
   ("-supplements", Arg.String set_supplement_summary_classpath,
    "supplement-summary jar file");
   ("-log",Arg.Set save_log,"save log file")
 ]

let usage_msg = "ch_integrate filename"
let read_args () = Arg.parse speclist   (fun s -> name := s) usage_msg


let main () =
  try
    let _ = read_args () in
    let cn = make_cn !name in
    let _ = load_class_and_dependents cn in
    let logname = cn#name ^ "_integrate.chlog" in
    begin
      save_xml_class_or_interface_summary cn;
      file_output#saveFile logname chlog#toPretty
    end
  with
  | CHFailure p
  | JCH_failure p ->
     begin
       pr_debug [STR "Error in chj_template: "; p];
       exit 1
     end
  | CHXmlReader.XmlParseError (l,c,p) ->
     begin
       pr_debug
         [NL;
          STR "Xml parse error at (";
          INT l;
          STR ",";
          INT c;
          STR "): ";
          p;
          NL];
       exit 1
     end
  | XmlDocumentError(line, col, p) ->
     begin
       pr_debug [
           NL; STR "XML document error at (";
           INT line;
           STR ",";
           INT col;
           STR "): ";
           p;
           NL];
       exit 1
     end


let _ = Printexc.print main ()

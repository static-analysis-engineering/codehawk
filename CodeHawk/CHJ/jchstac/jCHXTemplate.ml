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

(** standalone main program to create template class summary files *)

(* chlib *)
open CHCommon
open CHPretty

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHFile
open JCHDictionary

(* jchpre *)
open JCHApplication
open JCHClassLoader
open JCHClassUserTemplate
open JCHPreFileIO
open JCHSystemSettings

let name = ref ""
let speclist = [("-classpath", Arg.String system_settings#add_classpath_unit,
		 "sets java classpath") ]
								
let usage_msg = "chj_template filename"
let read_args () = Arg.parse speclist   (fun s -> name := s) usage_msg

let main () =
  try
    let _ = read_args () in
    let cn = make_cn !name in
    let _ = load_class_and_dependents cn in
    save_xml_user_class_template_file cn
  with
    CHFailure p
  | JCH_failure p ->
    pr_debug [ STR "Error in chj_template: " ; p ]

let _ = Printexc.print main ()

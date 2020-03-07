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
open CHCommon
open CHPretty

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes

(* jchpre *)
open JCHApplication
open JCHCHAUtil
open JCHNativeMethods
open JCHSystemSettings

let jars = ref []
let output_directory = ref ""

let read_jar_name s = 
  begin
    jars := s :: !jars ;
    app#add_application_jar s
  end

let name = ref ""
let speclist = [
  ("-classpath", Arg.String system_settings#add_classpath_unit, "sets java classpath") ;
  ("-o", Arg.Set_string output_directory, "output directory where results get saved") ;
  ("-load", Arg.Rest read_jar_name, "list of jars to be loaded")
]
								
let usage_msg = "get_native_signatures filename"
let read_args () = Arg.parse speclist   (fun s -> name := s) usage_msg

let main () =
  try
    let _ = read_args () in
    let dir = if !output_directory = "" then "ch_native_signatures" else !output_directory in
    begin
      (if not (Sys.file_exists dir) then Unix.mkdir dir 0o750) ;
      save_native_signatures dir !jars ;
      pr_debug [ STR "Load library calls: " ; NL ] ;
      pr_debug (List.map (fun s -> LBLOCK [ STR "  " ; STR s ; NL ]) (get_loadlibrarycalls ()))
    end
  with
  | CHFailure p
  | JCH_failure p ->
    pr_debug [ STR "Error in get_native_signatures: " ; p ]

let _ = Printexc.print main ()

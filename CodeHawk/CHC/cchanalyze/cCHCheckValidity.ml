(* =============================================================================
   CodeHawk C Analyzer 
   Author: Henny Sipma
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
open CHAtlas
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader


(* cchlib *)
open CCHBasicTypes
open CCHContext
open CCHFileEnvironment
open CCHSettings
open CCHUtilities

(* cchpre *)
open CCHCallsite
open CCHPPO
open CCHPreFileIO
open CCHPreTypes
open CCHProofObligation
open CCHProofScaffolding


(* cchanalyze *)
open CCHEnvironment
open CCHOrakel
open CCHPOChecker

let prr p l = fixed_length_pretty ~alignment:StrRight p l
let fenv = CCHFileEnvironment.file_environment

let function_to_be_analyzed = ref ""
let do_reset = ref false
let assumptionfilename = ref ""
let system_assumptions = ref []


let read_system_assumptions () = () 

let process_function fname =
  let fmsg = LBLOCK [ STR "function " ; STR fname ] in
  let starttime = Unix.gettimeofday () in
  let fundec = read_function_semantics fname in
  let fdecls = fundec.sdecls in
  let _ = pr_debug [ fixed_length_pretty
                       (LBLOCK [ STR "  check " ; fmsg ]) 72 ] in
  let _ = read_proof_files fname fdecls in
  let _ = read_api fname in
  let varmgr = read_vars fname fdecls in
  let env = mk_c_environment fundec varmgr in
  let invio = read_invs fname varmgr#vard in
  let proofObligations = proof_scaffolding#get_proof_obligations fname in
  try
    if !function_to_be_analyzed = fname || !function_to_be_analyzed = "" then
      let fnApi = proof_scaffolding#get_function_api fname in
      begin
        check_proof_obligations env fnApi invio proofObligations ;
        save_proof_files fname ;
        save_api fname ;
        pr_debug [ STR (Printf.sprintf "%8.2f sec" ((Unix.gettimeofday ()) -. starttime)) ; NL ]
      end
  with
  | CCHFailure p ->
     begin
       ch_error_log#add "failure" (LBLOCK [ fmsg ; STR ": " ; p ]) ;
       raise (CCHFailure  (LBLOCK [ fmsg ; STR ": " ; p]))
     end
  | XmlParseError (line,col,p)
    | XmlDocumentError (line,col,p) ->
     let msg = LBLOCK
                 [ STR "Xml error in "; fmsg ;  STR ": " ; p ; STR " at " ; 
		   STR "(" ; INT line ; STR ", " ; INT col ; STR ")" ; NL ]  in
     begin
       pr_debug [ msg ] ;
       ch_error_log#add "xml error" msg ;
       raise (XmlDocumentError (line,col,msg))
     end
  | Invalid_argument s ->
      ch_error_log#add "invalid argument" (LBLOCK [ fmsg ; STR ": " ; STR s ])
  | Not_found ->
     ch_error_log#add "not-found" (LBLOCK [ fmsg ])
  | Failure s ->
     begin
       ch_error_log#add s (LBLOCK [ fmsg ]) ;
       raise (CCHFailure (LBLOCK [ fmsg ; STR ": Failure(" ; STR s ; STR ")" ]))
     end
                                                            
let check_process_file () =
  try
    let _ = read_cfile_dictionary () in
    let cfile = read_cfile () in
    let _ = fenv#initialize cfile in
    let _ = read_cfile_predicate_dictionary () in
    let _ = read_cfile_context () in
    let _ = read_cfile_interface_dictionary () in
    let functions = fenv#get_application_functions in
    begin
      List.iter (fun f -> ignore (process_function f.vname)) functions ;
      save_cfile_predicate_dictionary () ;
      save_cfile_dictionary () ;
      save_cfile_context () ;
      save_cfile_interface_dictionary () 
    end
  with
    CHXmlReader.IllFormed ->
      ch_error_log#add "ill-formed content" (STR system_settings#get_cfilename)
  | XmlDocumentError (line,col,p) ->
     pr_debug [ STR "Xml error in checking file " ;
                STR system_settings#get_cfilename ; STR ": " ; p ;
	        STR " (" ; INT line ; STR ", " ; INT col ; STR "): " ; p ; NL ]


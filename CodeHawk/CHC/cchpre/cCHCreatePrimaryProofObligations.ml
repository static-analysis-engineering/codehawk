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
open CHPretty

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* cchlib *)
open CCHBasicTypes
open CCHBasicUtil
open CCHDeclarations
open CCHFileContract
open CCHFileEnvironment
open CCHSettings
open CCHUtilities

(* cchpre *)
open CCHAssignDictionary
open CCHCheckValid
open CCHGlobalAssignment
open CCHPreFileIO
open CCHPreTypes
open CCHPrimaryProofObligations
open CCHProofObligation
open CCHProofScaffolding

let prr p l = fixed_length_pretty ~alignment:StrRight p l
let fenv = CCHFileEnvironment.file_environment

let process_global (g:global) =
  match g with
  | GVar (vinfo,Some init,loc) ->
     begin 
       ignore (assigndictionary#index_assignment
                 (InitAssignment (vinfo.vname,vinfo.vid,init))) ;
       set_global_value vinfo
     end
  | _ -> ()
         
let process_function (fname:string) =
  let _ =
    if system_settings#verbose then
      pr_debug [ STR "Processing function " ; STR fname ; NL ] in
  try
    let fundec = read_function_semantics fname in
    let fdecls = fundec.sdecls in
    let createppos = true in (* not (file_contract#ignore_function fname) in *)
    begin
      read_proof_files fname fdecls ;
      create_proof_obligations ~createppos fundec ;
      CCHCheckValid.process_function fname ;
      save_proof_files fname ;
      save_api fname ;
    end
  with
  | CCHFailure p ->
    begin
      pr_debug [ STR "Error in processing function " ; STR fname ; STR ": " ; p ; NL ] ;
      ch_error_log#add "failure" (LBLOCK [ STR "function " ; STR fname ; STR ": " ; p ])
    end
  | Invalid_argument s ->
    ch_error_log#add "failure" (LBLOCK [ STR "function " ; STR fname ; STR ": " ; STR s ])
    

let primary_process_file () =
  try
    let _ = read_cfile_dictionary () in
    let _ = read_cfile_interface_dictionary () in
    let cfile = read_cfile () in
    let _ = fenv#initialize cfile in
    let _ = cdeclarations#index_location call_sink in
    let functions = fenv#get_application_functions in
    let _ = read_cfile_contract () in
    begin
      List.iter (fun f -> process_function f.vname) functions ;
      List.iter process_global cfile.globals ;
      save_cfile_assignment_dictionary () ;
      save_cfile_predicate_dictionary () ;
      save_cfile_interface_dictionary() ;
      save_cfile_dictionary () ;
      save_cfile_context () ;
    end
  with
    CHXmlReader.IllFormed ->
      ch_error_log#add "ill-formed content" (STR system_settings#get_cfilename)

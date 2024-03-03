(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHUtils

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil

(* bchlib *)
open BCHBasicTypes
open BCHConstantDefinitions
open BCHFunctionSummary
open BCHFunctionSummaryLibrary
open BCHLibTypes
open BCHSystemInfo
open BCHSystemSettings
open BCHTypeDefinitions

module H = Hashtbl


let const_files = ref []

let speclist = [
    ("-use", Arg.String (fun s -> const_files := s :: !const_files),
     "use constants for given type")]
  
let usage_msg = "inspect_summaries <jar name>"

let read_args () = 
  Arg.parse speclist (fun s -> system_settings#set_summary_jar s) usage_msg
  
let save_log_files () =
  begin
    file_output#saveFile "bchsummaries.ch_error_log" ch_error_log#toPretty ;
    file_output#saveFile "bchsummaries.chlog" chlog#toPretty
  end
    
let inspect_summaries () = function_summary_library#read_summary_files 
    

let print_statistics () =
  let summaries = function_summary_library#get_library_functions in
  let enums = new StringCollections.set_t in
  let _ = List.iter (fun s -> enums#addList s#get_enums_referenced) summaries in
  let _ = List.iter 
    (fun s ->
      begin pr_debug [ STR s ; NL ] ; system_info#read_xml_constant_file s end)
    enums#toList in

  let fActions = List.fold_left (fun acc s ->
    let fname = s#get_name in
    match s#get_io_actions with [] -> acc | l -> 
      (fname, List.map (fun iox -> iox.iox_cat) l) :: acc) [] summaries in
  let pActions = List.map (fun (fname, cats) ->
    LBLOCK [ STR fname  ; STR ": " ;
	     pretty_print_list cats (fun c -> STR c) "" ", " "" ; NL ]) fActions in
  (* let paramRoles = List.fold_left (fun acc s ->
    let name = s#get_name in
    let params = s#get_function_api.fapi_parameters in
    let roles = List.fold_left (fun acc1 p -> match p.apar_roles with [] -> acc1 | l ->
      let roles = List.sort Stdlib.compare p.apar_roles in
      (p.apar_name,roles) :: acc1) [] params in
    match roles with [] -> acc | _ -> (name,roles) :: acc) [] summaries in *)
  let nParamRoles =
    List.fold_left (fun acc s ->
        let nRoles =
          List.fold_left (fun acc1 p -> acc1 + List.length (p.apar_roles))
            0 s#get_function_interface.fintf_type_signature.fts_parameters in
        acc + nRoles) 0 summaries in
  (* let pRoles = List.map (fun (fname,froles) ->
    LBLOCK [ STR fname ; NL ;
	     INDENT (3, LBLOCK (List.map (fun (pname,proles) ->
	       LBLOCK [ STR pname ; STR ": " ; 
			pretty_print_list proles (fun (rt,rn) ->
			  LBLOCK [ STR "(" ; STR rt ; STR "," ; STR rn ; STR ")" ])
			    "" "; " "" ; NL ]) froles)) ; NL ]) paramRoles in *)
  let count_sideeffects s = List.length s#get_sideeffects in 
  let count_preconditions s = List.length s#get_preconditions in
  let count_postconditions s = List.length s#get_postconditions in
  let count_errorpostconditions s = List.length s#get_errorpostconditions in
  let nPreconditions = 
    List.fold_left (fun a s -> a + (count_preconditions s)) 0 summaries in
  let nPostconditions = 
    List.fold_left (fun a s -> a + (count_postconditions s)) 0 summaries in
  let nErrorpostconditions =
    List.fold_left (fun a s -> a + (count_errorpostconditions s)) 0 summaries in
  let nSideeffects = 
    List.fold_left (fun a s -> a + (count_sideeffects s)) 0 summaries in
  begin
    pr_debug [ STR "Summaries          : " ; INT (List.length summaries) ; NL ;
	       STR "Preconditions      : " ; INT nPreconditions ; NL ;
	       STR "Postconditions     : " ; INT nPostconditions ; NL ;
	       STR "Errorpostconditions: " ; INT nErrorpostconditions ; NL ;
	       STR "Sideeffects        : " ; INT nSideeffects ; NL ; 
	       STR "Type definitions: " ; NL ; type_definitions#toPretty ; NL ;
               STR "IO action categories: " ; INT (List.length pActions) ; NL ;
               STR "Parameter roles     : " ; INT nParamRoles ; NL ;
	       constant_statistics_to_pretty () ;  NL ]
  end
    
let main () =
  try
    read_args () ;
    List.iter system_info#read_xml_constant_file !const_files ;
    system_info#initialize_type_definitions ;
    inspect_summaries () ;
    print_statistics () ;
    save_log_files ()
  with
    CHFailure p | BCH_failure p ->
      begin
	pr_debug [ NL ; STR "Failure in reading summaries: " ; p ; NL ] ;
	save_log_files ()
      end
  | CHXmlReader.XmlParseError (l,c,p) ->
    begin
      pr_debug [ NL; STR "Xml parse error at (" ; INT l ; STR "," ; INT c ; STR "): " ; 
		 p ; NL ] ;
      save_log_files ()
    end
  | CHXmlDocument.XmlDocumentError (l,c,p) ->
    begin
      pr_debug [ NL; STR "Xml document error at (" ; INT l ; STR "," ; INT c ; STR "): " ; 
		 p ; NL ] ;
      save_log_files ()
    end
      
let _ = Printexc.print main ()
  

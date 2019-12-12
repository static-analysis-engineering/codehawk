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
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* cchlib *)
open CCHBasicTypes
open CCHBasicTypesXml
open CCHFileEnvironment
open CCHTypesToPretty
open CCHUtilities

(* cchpre *)
open CCHPreFileIO
open CCHProofObligation
open CCHProofScaffolding

(* cchgui *)
open CCHSystemDisplay

module H = Hashtbl

let c2xfile f = (Filename.chop_extension f) ^ ".xml"
let string_printer = CHPrettyUtil.string_printer
let pp_str p = string_printer#print p

let get_application_functions cfilename =
  let app_functions = [] in
  let cfile = get_xml_cfile cfilename in
  begin
    pr_debug [ STR cfilename ; NL ] ;
    List.iter (fun g ->
        match g with
        | GFun (vinfo, loc) -> ignore(vinfo.vname :: app_functions)
        | _ -> ()) cfile.globals
  end 

let read_primary_proof_stats fname =
  let ppos = (proof_scaffolding#get_ppo_manager fname)#get_ppos in
  let total = List.length ppos in
  let proven = ref 0 in
  let _ = List.iter (fun ppo -> if ppo#is_closed then proven := !proven + 1) ppos in
  (total, !proven)

let xml_error filename line column p =
  LBLOCK [ STR "Xml error in " ; STR filename ;
       STR " (" ; INT line ; STR ", " ; INT column ; STR "): " ; p ]

let build_po_pretty po =
  let prr p len = fixed_length_pretty ~alignment:StrRight p len in
  let api = int_of_string (po#getAttribute "api") in
  let contract = int_of_string (po#getAttribute "contract") in
  let local = int_of_string (po#getAttribute "local") in
  let openppo = int_of_string (po#getAttribute "open") in
  let stmt = int_of_string (po#getAttribute "stmt") in
  let violated = int_of_string (po#getAttribute "violated") in
  let total = (api + contract + local + openppo + stmt + violated) in
  let name = po#getAttribute "name" in
  LBLOCK [ fixed_length_pretty (STR name) 32 ;
	   prr (INT api) 12 ;
           prr (INT contract) 12 ;
           prr (INT local) 12 ;
           prr (INT openppo) 12 ;
           prr (INT stmt) 12 ;
           prr (INT violated) 12 ; 
           prr (INT total) 12 ; NL ]
  
let get_app_summary_stats () =
  let filename = get_xml_summaryresults_name () in
  if Sys.file_exists filename then
    try
      let doc = readXmlDocument filename in
      let root = doc#getRoot in
      let tagresults = root#getTaggedChild "tagresults" in
      let fileresults = root#getTaggedChild "fileresults" in
      let ppos = tagresults#getTaggedChild "ppos" in
      let spos = tagresults#getTaggedChild "spos" in
      let file_ppos = fileresults#getTaggedChild "ppos" in
      let file_spos = fileresults#getTaggedChild "spos" in
      let ppo_types = ppos#getChildren in
      let spo_types = spos#getChildren in
      let file_ppo_types = file_ppos#getChildren in
      let file_spo_types = file_spos#getChildren in
      let make_header info =
        LBLOCK [ fixed_length_pretty (STR info) 32 ;
		 STR "         api" ; STR "    contract" ; STR "       local" ;
                 STR "     openppo" ; STR "        stmt" ; STR "    violated" ;
                 STR "       total" ; NL ; STR (string_repeat "-" 116) ; NL ] in
      let pp = ref [ make_header "ppos" ] in
      let _ = begin 
          List.iter ( fun x -> pp := (build_po_pretty x) :: !pp ) ppo_types ;
          pp := (LBLOCK [ NL ]) :: !pp ;
          pp := (make_header "spos") :: !pp ;
          List.iter ( fun x -> pp := (build_po_pretty x) :: !pp ) spo_types ;
          pp := (LBLOCK [ NL ]) :: !pp ;
          pp := (make_header "ppos by file") :: !pp ;
          List.iter ( fun x -> pp := (build_po_pretty x) :: !pp ) file_ppo_types ;
          pp := (LBLOCK [ NL ]) :: !pp ;
          pp := (make_header "spos by file") :: !pp ;
          List.iter ( fun x -> pp := (build_po_pretty x) :: !pp ) file_spo_types
        end in
      pp_str
        (LBLOCK [ STR "KT Advance C Analyzer" ; NL ; NL ; (LBLOCK (List.rev !pp)) ])
    with
    | XmlDocumentError (line,col,p)
    | XmlParseError (line,col,p) ->
      raise (CCHFailure (xml_error filename line col p))
  else
    pp_str (LBLOCK [ STR "Summary results file " ; STR filename ; STR " not found" ; NL ])

let get_rv_assumptions_stats () = "get_rv_assumptions_stats"

let get_global_assumptions_stats () = "get_global_assumptions_stats_stub"

let get_global_assignment_stats () = "get_global_assignment_stats"
	
let get_field_assignment_stats () = "get_field_assignment_stats"

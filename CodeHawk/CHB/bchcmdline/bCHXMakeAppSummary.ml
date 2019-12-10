(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHCommon
open CHPretty

(* chutil *)
open CHFileIO
open CHXmlDocument

(* bchlib *)
open BCHPreFileIO
open BCHSystemInfo
open BCHUtilities

let name = ref ""
let address = ref ""
let cfilename = ref ""
let efilename = ref ""
let num_parameters = ref 0
let stdcall = ref false
let cdecl = ref false
let mips = ref false
let parameter_names = ref []
let add_parameter s = parameter_names := s :: !parameter_names

(* Split a list into two lists, the first one with n elements,
   the second list with the remaining (if any) elements
*)
let split_list (n:int) (l:'a list):('a list * 'a list) =
  let rec loop i p l =
    if i = n then 
      (List.rev p,l)
    else loop (i+1) ((List.hd l)::p) (List.tl l) in
  if (List.length l) <= n then (l,[]) else loop 0 [] l


let speclist = [
  ("-parameters", Arg.Rest add_parameter, "parameter names in order") ;
  ("-stdcall", Arg.Unit (fun _ -> stdcall := true), "stdcall calling convention") ;
  ("-cdecl", Arg.Unit (fun _ -> cdecl := true), "cdecl calling convention") ; 
  ("-name", Arg.String (fun s -> name := s), "name of the function") ;
  ("-address", Arg.String (fun s -> address := s), "hex address of the function") ;
  ("-cfile", Arg.String (fun s -> cfilename := s), "name of the c source code file") ;
  ("-efile", Arg.String (fun s -> efilename := s), "name of executable file") ;
  ("-mips", Arg.Unit (fun _ -> mips := true), "use mips register arguments") ]

  
let ccNode =
  xml_string
    "copyright-notice" "Copyright 2012-2019, Kestrel Technology LLC, Palo Alto, CA 94304" 
  
let usage_msg = "apptemplate name"
let read_args () = Arg.parse speclist (fun s -> name := s) usage_msg

let write_xml_apidoc (node:xml_element_int) (parameters:string list) =
  let append = node#appendChildren in
  let ptNode = match parameters with
    | [] -> xml_string "pt" (!name ^ " (void)") 
    | [ n ] -> xml_string "pt" (!name ^ " (" ^ n ^ ")") 
    | _ ->
      let ptNode = xmlElement "pt" in
      let fNode = xml_string "ll" (!name ^ "(") in
      let mNodes = List.map (fun n -> xml_string "ld" n) parameters in
      let lNode = xml_string "ll" ")" in
      begin
	ptNode#appendChildren (fNode :: (mNodes @ [ lNode ])) ;
	ptNode
      end in
  let parNodes = List.map (fun p ->
    let pNode = xml_string "par" " " in
    begin pNode#setAttribute "name" p ; pNode end) parameters in
  let rNode = 
    let rNode = xmlElement "return" in
    let sNode = xml_string "rc" " " in
    let fNode = xml_string "rc" " " in
    begin
      rNode#appendChildren [ sNode ; fNode ] ;
      sNode#setAttribute "cond" "success" ;
      fNode#setAttribute "cond" "failure" ;
      rNode
    end in
  append ((ptNode :: (parNodes)) @ [ rNode ])
  

let write_xml_doc (node:xml_element_int) parameters =
  let append = node#appendChildren in
  let descNode = xml_string "desc" " " in
  let apiNode = xmlElement "apidoc" in
  begin
    write_xml_apidoc apiNode parameters ;
    append [ descNode ; apiNode ]
  end

let write_xml_api (node:xml_element_int) parameters =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let pars = List.rev (List.mapi (fun i name ->
    let pNode = xmlElement "par" in
    let tNode = xml_string "type" " "  in
    let set = pNode#setAttribute in
    let seti = pNode#setIntAttribute in
    begin
      pNode#appendChildren [ tNode ] ;
      set "loc" "stack" ;
      set "name" name ;
      seti "nr" (i+1) ;
      pNode
    end) parameters) in
  let rNode = xml_string "returntype" " " in
  begin
    append (pars @ [ rNode ]) ;
    (if !stdcall then set "cc" "stdcall") ;
    (if !cdecl then set "cc" "cdecl") ;
    (if !stdcall then seti "adj" (4 * (List.length parameters))) ;
    (if !cdecl then seti "adj" 0) ;
    set "name" !name
  end

let write_xml_mips_api (node:xml_element_int) parameters =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let mk_regpars regpars =
    List.rev (List.mapi (fun i name ->
        let pNode = xmlElement "par" in
        let tNode = xml_string "type" " " in
        let set = pNode#setAttribute in
        begin
          pNode#appendChildren [ tNode ] ;
          set "loc" "register" ;
          set "name" name ;
          set "reg" ("mips($a" ^ (string_of_int i) ^ ")") ;
          pNode
        end) regpars) in
  let mk_stackpars stackpars =
    List.rev (List.mapi (fun i name ->
        let pNode = xmlElement "par" in
        let tNode = xmlElement "type" in
        let set = pNode#setAttribute in
        begin
          pNode#appendChildren [ tNode ] ;
          set "loc" "stack" ;
          set "name" name ;
          seti "nr" (i+4) ;
          pNode
        end) stackpars) in        
  let (regpars,stackpars) = split_list 4 parameters in
  let pars = List.concat [ (mk_regpars regpars); (mk_stackpars stackpars) ] in
  let rNode = xml_string "returntype" " " in
  begin
    append (pars @ [ rNode ]) ;
    (if !cdecl then set "cc" "cdecl") ;
    (if !cdecl then seti "adj" 0) ;
    set "name" !name
  end
  


let write_xml_postconditions (node:xml_element_int) = ()

let write_xml_sideeffects (node:xml_element_int) = ()

let write_xml_sem (node:xml_element_int) =
  let append = node#appendChildren in
  let preNode = xmlElement "preconditions" in
  let postNode = xmlElement "postconditions" in
  let sideNode = xmlElement "sideeffects" in
  let exNode = xmlElement "external-effects" in
  begin
    write_xml_postconditions postNode ;
    write_xml_sideeffects sideNode ;
    append [ preNode ; postNode ; sideNode ; exNode ]
  end
  
let write_xml_summary (node:xml_element_int) parameters =
  let append = node#appendChildren in
  let docNode = xmlElement "documentation" in
  let apiNode = xmlElement "api" in
  let semNode = xmlElement "semantics" in
  begin
    write_xml_doc docNode parameters ;
    (if !mips then
       write_xml_mips_api apiNode parameters
     else
       write_xml_api apiNode parameters) ;
    write_xml_sem semNode ;
    append [ docNode ; apiNode ; semNode ]
  end

let get_filename () = (replace_dot !efilename) ^ "_" ^ !address ^ "_u.xml"   

let main () =
  try
    let _ = read_args () in
    let doc = xmlDocument () in
    let root = xmlElement "codehawk-binary-analyzer" in
    let header = xmlElement "header" in
    let node = xmlElement "function-summary" in 
    let parameters = List.rev !parameter_names in
    begin
      doc#setNode root ;
      write_xml_summary node parameters ;
      root#appendChildren [ header ; node ; ccNode ] ;
      header#setAttribute "date" (time_to_string (Unix.gettimeofday ())) ;
      node#setAttribute "name" !name ;
      node#setAttribute "address" !address ;
      node#setAttribute "cfile" !cfilename ;
      node#setAttribute "file" !efilename ;
      file_output#saveFile (get_filename ()) doc#toPretty ;
    end
  with
    CHFailure p -> pr_debug [ STR "Error in template: " ; p ; NL ]

let _ = Printexc.print main ()
  

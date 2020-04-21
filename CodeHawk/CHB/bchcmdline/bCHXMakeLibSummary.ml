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
open CHCommon
open CHPretty

(* chutil *)
open CHFileIO
open CHXmlDocument

(* bchlib *)
open BCHPreFileIO
open BCHSystemInfo

let name = ref ""
let libname = ref ""
let iox_cat = ref ""
let ansi_unicode = ref false
let num_parameters = ref 0
let stdcall = ref false
let cdecl = ref false
let sets_errno = ref false
let parameter_names = ref []
let post = ref []
let enumpost = ref []
let add_parameter s = parameter_names := s :: !parameter_names

let msn = ref false
let tog = ref false

let refNode s = xml_attr_string "reference" "href" s
let msnNode = refNode "http://msdn.microsoft.com/"
let togNode = refNode "http://pubs.opengroup.org/onlinepubs/000095399/"

let speclist = [
  ("-parameters", Arg.Rest add_parameter, "parameter names in order") ;
  ("-stdcall", Arg.Unit (fun _ -> stdcall := true), "stdcall calling convention") ;
  ("-cdecl", Arg.Unit (fun _ -> cdecl := true), "cdecl calling convention") ; 
  ("-name", Arg.String (fun s -> name := s), "name of the function") ;
  ("-lib", Arg.String (fun s -> libname := s), "name of the library") ;
  ("-errno", Arg.Unit (fun _ -> sets_errno := true), "sets errno") ;
  ("-post", Arg.String (fun s -> post := s :: !post), "adds a shortcut postcondition") ;
  ("-enumpost", Arg.String (fun s -> enumpost := s :: !enumpost), "adds an enum postcondition") ;
  ("-msn", Arg.Set msn, "documentation obtained from MSDN website") ;
  ("-tog", Arg.Set tog, "documentation obtained from The Open Group website") ;
  ("-aw" , Arg.Set ansi_unicode, "create ansi and unicode versions as well") ;
  ("-io" , Arg.String (fun s -> iox_cat := s), "initializes an io action with category s") ]
  
let ccNode =
  xml_string
    "copyright-notice" "Copyright 2012-2020, Kestrel Technology LLC, Palo Alto, CA 94304" 
  
let usage_msg = "mktemplate name"
let read_args () = Arg.parse speclist (fun s -> name := s) usage_msg

let post_shortcuts = [
  "notzero-zero" ; "nonzero-zero" ; "one-zero" ; "zero-negone" ; 
  "notnull" ; "notnull-null" ; 
  "nonnegative-negative" ; "positive-nonpositive" ; "positive-zero" ]
  

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
  let pars = List.mapi (fun i name ->
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
    end) parameters in
  let rNode = xml_string "returntype" " " in
  begin
    append (pars @ [ rNode ]) ;
    (if !stdcall then set "cc" "stdcall") ;
    (if !cdecl then set "cc" "cdecl") ;
    (if !stdcall then seti "adj" (4 * (List.length parameters))) ;
    (if !cdecl then seti "adj" 0) ;
    set "name" !name
  end


let write_xml_postconditions (node:xml_element_int) = 
  let append = node#appendChildren in
  let pNodes = List.fold_left (fun acc p ->
    if List.mem p post_shortcuts then 
      (xmlElement p) :: acc 
    else
      begin
	pr_debug [ STR "Warning: " ; STR p ; STR " is not a valid postcondition" ; NL ] ;
	acc
      end) [] !post in
  let pNodes = List.fold_left (fun acc p ->
    let pNode = xmlElement "enum" in
    begin pNode#setAttribute "name" p ; pNode :: acc end) pNodes !enumpost in
  append pNodes

let write_xml_sideeffects (node:xml_element_int) =
  if !sets_errno then
    let sNode = xmlElement "sideeffect" in
    let mNode = xmlElement "math" in
    let eNode = xmlElement "sets-errno" in
    begin
      sNode#appendChildren [ mNode ] ;
      mNode#appendChildren [ eNode ] ;
      node#appendChildren [ sNode ]
    end
  else
    ()

let write_xml_io_actions (node:xml_element_int) parameters =
  if !iox_cat = "" then () else
    let append = node#appendChildren in
    let ioNode = xmlElement "io-action" in
    begin
      node#appendChildren [ ioNode ] ;
      ioNode#setAttribute "cat" !iox_cat ;
      ioNode#setAttribute "desc" " "
    end
      
let write_xml_sem (node:xml_element_int) parameters =
  let append = node#appendChildren in
  let preNode = xmlElement "preconditions" in
  let postNode = xmlElement "postconditions" in
  let sideNode = xmlElement "sideeffects" in
  let ioNode = xmlElement "io-actions" in
  begin
    write_xml_postconditions postNode ;
    write_xml_sideeffects sideNode ;
    write_xml_io_actions ioNode parameters ;
    append [ ioNode ; preNode ; postNode ; sideNode ]
  end
  
let write_xml_summary (node:xml_element_int) parameters =
  let append = node#appendChildren in
  let docNode = xmlElement "documentation" in
  let apiNode = xmlElement "api" in
  let semNode = xmlElement "semantics" in
  begin
    write_xml_doc docNode parameters ;
    write_xml_api apiNode parameters ;
    write_xml_sem semNode parameters ;
    append [ docNode ; apiNode ; semNode ]
  end

let save_aw_version (char_type:string) =
    let doc = xmlDocument () in
    let root = xmlElement "codehawk-binary-analyzer" in
    let header = xmlElement "header" in
    let node = xmlElement "libfun" in
    let rNode = xmlElement "refer-to" in
    let suffix = if char_type = "ansi" then "A" else "W" in
    let awname = !name ^ suffix in
    begin
      doc#setNode root ;
      root#appendChildren [ header ; node ; ccNode ] ;
      header#setAttribute "date" (time_to_string (Unix.gettimeofday ())) ;
      node#setAttribute "name" awname ;
      node#setAttribute "lib" !libname ;
      node#appendChildren [ rNode ] ;
      rNode#setAttribute "char-type" char_type ;
      rNode#setAttribute "name" !name ;
      file_output#saveFile (awname ^ ".xml") doc#toPretty 
    end

let save_ansi_unicode_versions () =
  if !libname = "" then
    pr_debug [ STR "Cannot save ansi/unicode versions without a library name" ; NL ]
  else
    begin
      save_aw_version "ansi" ;
      save_aw_version "unicode" 
    end
    

let main () =
  try
    let _ = read_args () in
    let doc = xmlDocument () in
    let root = xmlElement "codehawk-binary-analyzer" in
    let header = xmlElement "header" in
    let node = xmlElement "libfun" in 
    let parameters = List.rev !parameter_names in
    begin
      doc#setNode root ;
      write_xml_summary node parameters ;
      (if !msn then root#appendChildren [ msnNode ]) ;
      (if !tog then root#appendChildren [ togNode ]) ;
      root#appendChildren [ header ; node ; ccNode ] ;
      header#setAttribute "date" (time_to_string (Unix.gettimeofday ())) ;
      node#setAttribute "name" !name ;
      (if !libname = "" then () else node#setAttribute "lib" !libname) ;
      file_output#saveFile (!name ^ ".xml") doc#toPretty ;
      if !ansi_unicode then save_ansi_unicode_versions ()
    end
  with
    CHFailure p -> pr_debug [ STR "Error in template: " ; p ; NL ]

let _ = Printexc.print main ()
  

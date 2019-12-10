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

let name = ref ""
let value_names = ref []
let add_value_name s = value_names := s :: !value_names
let flags = ref false

let msn = ref false
let tog = ref false

let refNode s = xml_attr_string "reference" "href" s
let msnNode = refNode "http://msdn.microsoft.com/"
let togNode = refNode "http://pubs.opengroup.org/onlinepubs/000095399/"

let speclist = [
  ("-enum", Arg.Set_string name, "name of the enumeration") ;
  ("-flags", Arg.Set flags, "create symbolic flags") ;
  ("-msn", Arg.Set msn, "documentation obtained from MSDN website") ;
  ("-tog", Arg.Set tog, "documentation obtained from The Open Group website") ;
  ("-names", Arg.Rest add_value_name, "names of symbolic values (must be last)")
]

let write_xml_constants (node:xml_element_int) (names:string list) =
  let tag = if !flags then "symf" else "symc" in
  node#appendChildren (List.map (fun name ->
    let sNode = xmlElement tag in
    let dNode = xml_string "desc" " " in
    begin
      sNode#appendChildren [ dNode ] ;
      sNode#setAttribute "name" name ;
      sNode#setAttribute "value" " " ; 
      sNode
    end) names)
  
let ccNode =
  xml_string
    "copyright-notice" "Copyright 2012-2019, Kestrel Technology LLC, Palo Alto, CA 94304" 

let usage_msg = "mktemplate name"
let read_args () = Arg.parse speclist (fun s -> name := s) usage_msg

let main () =
  try
    let _ = read_args () in
    let doc = xmlDocument () in
    let root = xmlElement "codehawk-binary-analyzer" in
    let header = xmlElement "header" in
    let tag = if !flags then "symbolic-flags" else "symbolic-constants" in
    let node = xmlElement tag in
    let vNode = xmlElement "values" in
    let names = List.rev !value_names in
    begin
      doc#setNode root ;
      write_xml_constants vNode names ;
      (if !msn then root#appendChildren [ msnNode ]) ;
      (if !tog then root#appendChildren [ togNode ]) ;
      root#appendChildren [ header ; node ; ccNode ] ;
      node#appendChildren [ vNode ] ;
      header#setAttribute "date" (time_to_string (Unix.gettimeofday ())) ;
      node#setAttribute "type" !name ;
      file_output#saveFile (!name ^ ".xml") doc#toPretty ;
    end
  with
    CHFailure p -> pr_debug [ STR "Error in template: " ; p ; NL ]

let _ = Printexc.print main ()
  

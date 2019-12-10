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
let fieldnames = ref []
let add_field s = fieldnames := s :: !fieldnames

let msn = ref false
let tog = ref false

let refNode s = xml_attr_string "reference" "href" s
let msnNode = refNode "http://msdn.microsoft.com/"
let togNode = refNode "http://pubs.opengroup.org/onlinepubs/000095399/"

let speclist = [
  ("-name", Arg.String (fun s -> name := s), "name of the struct") ;
  ("-msn", Arg.Set msn, "documentation obtained from MSDN website") ;
  ("-tog", Arg.Set tog, "documentation obtained from The Open Group website") ;
  ("-fields", Arg.Rest add_field, "names of symbolic values (must be last)")
]

let write_xml_fields (node:xml_element_int) (fields:string list) =
  node#appendChildren (List.map (fun fname ->
    let fNode = xmlElement "field" in
    begin
      fNode#setAttribute "name" fname ;
      fNode#setAttribute "offset" " " ; 
      fNode#setAttribute "size" " " ;
      fNode#appendChildren [ xml_string "type" " " ] ;
      fNode
    end) fields)
  
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
    let node = xmlElement "struct" in
    let ffNode = xmlElement "fields" in
    let fields = List.rev !fieldnames in
    begin
      doc#setNode root ;
      write_xml_fields ffNode fields ;
      (if !msn then root#appendChildren [ msnNode ]) ;
      (if !tog then root#appendChildren [ togNode ]) ;
      root#appendChildren [ header ; node ; ccNode ] ;
      node#appendChildren [ ffNode ] ;
      header#setAttribute "date" (time_to_string (Unix.gettimeofday ())) ;
      node#setAttribute "name" !name ;
      file_output#saveFile (!name ^ ".xml") doc#toPretty ;
    end
  with
    CHFailure p -> pr_debug [ STR "Error in struct template: " ; p ; NL ]

let _ = Printexc.print main ()
  

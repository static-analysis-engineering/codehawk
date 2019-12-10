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
open CHPretty

(* chutil *)
open CHFileIO
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHVariableType

let stdcall = ref false
let className = ref ""
let thisPar = ref ""
let nDataMembers = ref 0

let virtualFunctions = ref []
let nonVirtualFunctions = ref []
let add_vf s = virtualFunctions := s :: !virtualFunctions
let add_nvf s = nonVirtualFunctions := s :: !nonVirtualFunctions

let set_class_name s = className := s
let set_datamember_count n = nDataMembers := n

let speclist = [
  ("-name", Arg.String set_class_name, "name of the class") ;
  ("-dms", Arg.Int set_datamember_count, "number of data members") ;
  ("-vfs", Arg.Rest add_vf, "names of virtual functions") ;
  ("-nvfs", Arg.Rest add_nvf, "names of non-virtual fucntions") ;
  ("-this", Arg.String (fun s -> thisPar := s), 
   "location of this for virtual or non-virtual functions") ;
  ("-stdcall", Arg.Set stdcall, "stdcall calling convention") ;
]
let usage_msg = "mkclasstemplate -name <name> -vfs <virtual functions>"
let read_args () = Arg.parse speclist (fun _ -> ()) usage_msg

let write_xml_par_template (node:xml_element_int) =
  let set = node#setAttribute in
  let sets t = set t " " in
  begin
    set "loc" "stack" ;
    sets "name" ;
    sets "nr" ;
    node#appendChildren [ xml_string "type" " " ]
  end

let write_xml_this (node:xml_element_int) (this:string) =
  let set = node#setAttribute in
  let append = node#appendChildren in
  let tNode = xmlElement "type" in
  let pNode = xml_string "ptr" !className in
  begin
    tNode#appendChildren [ pNode ] ;
    append [ tNode ] ;
    set "name" "this" ;
    (if this = "ecx" then
	begin set "loc" "register" ; set "reg" "ecx" end
     else if this = "arg1" then
       begin set "loc" "stack" ; set "nr" "1" end
     else ())
  end

let write_xml_vfapi_template (node:xml_element_int) (name:string) =
  let set = node#setAttribute in
  let append = node#appendChildren in
  let pNode = xmlElement "par" in
  let rNode = xml_string "returntype" " " in
  begin
    (if !thisPar = "" then () else 
	let tNode = xmlElement "par" in
	begin write_xml_this tNode !thisPar ; append [ tNode ] end) ;
    write_xml_par_template pNode ;
    append [ pNode ; rNode ] ;
    set "name" name ;
    set "adj" "0" ;
    (if !stdcall then set "cc" "stdcall" else set "cc" "cdecl")
  end

let write_xml_vtable_template (node:xml_element_int) =
  let set = node#setAttribute in
  let sets t = set t " " in
  begin
    node#appendChildren (List.map (fun vf ->
      let vNode = xmlElement "vf" in
      let aNode = xmlElement "api" in
      begin
	write_xml_vfapi_template aNode vf ;
	vNode#setAttribute "offset" " " ;
	vNode#appendChildren [ aNode ] ;
	vNode 
      end) (List.rev !virtualFunctions)) ;	
    set "kind" "vfptr" ;
    sets "offset"
  end

let write_xml_cpp_data_member_template (node:xml_element_int) =
  let set = node#setAttribute in
  let sets t = set t " " in
  begin
    sets "name" ;
    sets "offset" ;
    sets "size" ;
    set "kind" "data" ;
    node#appendChildren [ xml_string "type" " " ]
  end

let write_xml_cpp_class_template (node:xml_element_int) (ndata_members:int)  =
  let set = node#setAttribute in
  let mNode = xmlElement "members" in
  let sNode = xmlElement "static-functions" in
  let nNode = xmlElement "non-virtual-functions" in
  let cNode = xmlElement "constructors" in
  begin
    for i = 1 to ndata_members do 
      let n = xmlElement "member" in 
      begin write_xml_cpp_data_member_template n ; mNode#appendChildren [ n ] end done ;
    (match !virtualFunctions with
    | [] -> ()
    | l -> 
      let n = xmlElement "member" in
      begin
	write_xml_vtable_template n ;
	n#setAttribute "kind" "vfptr" ;
	n#setAttribute "offset" " " ;
	n#setAttribute "a" "0x0" ;
	mNode#appendChildren [ n ]
      end) ;
    nNode#appendChildren (List.map (fun nvf -> 
      let nNode = xmlElement "nvf" in
      let aNode = xmlElement "api" in
      begin 
	write_xml_vfapi_template aNode nvf ;
	nNode#appendChildren [ aNode ] ;
	nNode#setAttribute "offset" " " ;
	nNode
      end) (List.rev !nonVirtualFunctions)) ;
    node#appendChildren [ sNode ; cNode ; nNode ; mNode ] ;
    set "name" !className
  end

let main () =
  try
    let _ = read_args () in
    let doc = xmlDocument () in
    let node = xmlElement "codehawk-cpp-class-file" in
    let hNode = xmlElement "header" in
    let cNode = xmlElement "cpp-class" in
    begin
      doc#setNode node ;
      write_xml_cpp_class_template cNode !nDataMembers ;
      node#appendChildren [ hNode ; cNode ] ;
      hNode#setAttribute "date" (time_to_string (Unix.gettimeofday ())) ;
      file_output#saveFile (!className ^ "_cppclass.xml") doc#toPretty
    end
  with
    BCH_failure p -> pr_debug [ STR "Error in template: " ; p ; NL ]

let _ = Printexc.print main ()
  

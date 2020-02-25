(* =============================================================================
   CodeHawk Java Analyzer
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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHFileIO
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHFile

(* jchpre *)
open JCHApplication
open JCHPreAPI
open JCHXmlUtil

module P = Pervasives

(*
let get_parameter_name (mInfo:method_info_int) (par:int) =
  let par = if mInfo#is_static then par else par+1 in
  let name = mInfo#get_local_variable_name par 0 in
  if name = "none" then None else Some name

let write_xml_user_method_signature (node:xml_element_int) (mInfo:method_info_int) =
  let ms = mInfo#get_class_method_signature#method_signature in
  let append = node#appendChildren in
  begin
    append
      (List.mapi (fun i a ->
	let pNode = xmlElement "arg" in
	let _ = match get_parameter_name mInfo i with
	  | Some name -> pNode#setAttribute "name" name | _ -> () in
	begin write_xml_parameter pNode (i+1) a ; pNode end) ms#descriptor#arguments) ;
    (match ms#descriptor#return_value with
    | Some r -> 
      let rNode = xmlElement "return" in
      begin write_xml_value_type rNode r ; append [ rNode ] end
    | _ -> ())
  end
*)

let write_xml_summary_method (node:xml_element_int) (cms:class_method_signature_int) =
  let mInfo = app#get_method cms in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let sNode = xmlElement "signature" in
  let varnamemapping = if mInfo#has_local_variable_table then
      Some (fun i -> mInfo#get_local_variable_name i 0)
    else None in
  begin
    cms#method_signature#write_xmlx ~varnamemapping sNode ;
    append [ sNode ] ;
    set "name" cms#method_name_string ;
    sety "final" mInfo#is_final ;
    sety "abstract" mInfo#is_abstract ;
    sety "static" mInfo#is_static ;
    set "access" (access_to_string mInfo#get_visibility) ;
    node#setNameString mInfo#get_method_name
  end

let write_xml_summary_constructor
    (node:xml_element_int) (cms:class_method_signature_int) =
  let mInfo = app#get_method cms in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let sNode = xmlElement "signature" in
  let varnamemapping = if mInfo#has_local_variable_table then
      Some (fun i -> mInfo#get_local_variable_name i 0)
    else None in
  let argtypes =
    List.map value_type_to_string
             cms#method_signature#method_signature_data#descriptor#arguments in
  let nameString = "(" ^ (String.concat "," argtypes) ^ ")" in
  begin
    cms#method_signature#write_xmlx ~varnamemapping sNode ;
    append [ sNode ] ;
    sety "final" mInfo#is_final ;
    sety "abstract" mInfo#is_abstract ;
    sety "static" mInfo#is_static ;
    set "access" (access_to_string mInfo#get_visibility) ;
    node#setNameString nameString
  end

let write_xml_user_class_template (node:xml_element_int) (cn:class_name_int) =
  let cInfo = app#get_class cn in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety key v = if v then set key "yes" else () in
  let mmNode = xmlElement "methods" in
  let xxNode = xmlElement "constructors" in
  let cmss = List.map (fun ms -> make_cms cn ms) cInfo#get_methods_defined in
  let _ = List.iter (fun cms ->
    if app#has_method cms then () else 
      app#add_method (cInfo#get_method cms#method_signature)) cmss in
  let (constructors,cmss) = 
    List.fold_left (fun (c,m) cms -> 
      if cms#name = "<init>" then (cms::c,m) else (c,cms::m)) ([],[]) cmss in
  let cmss = List.sort (fun cms1 cms2 -> P.compare cms1#name cms2#name) cmss in
  begin
    mmNode#appendChildren (List.map (fun cms ->
      let mNode = xmlElement "method" in
      begin write_xml_summary_method mNode cms ; mNode end) cmss) ;
    xxNode#appendChildren (List.map (fun cms ->
      let cNode = xmlElement "constructor" in
      begin write_xml_summary_constructor cNode cms ; cNode end) constructors) ;
    append [ xxNode ; mmNode ] ;
    set "name" cn#simple_name ;
    set "package" cn#package_name ;
    sety "final" cInfo#is_final ;
    sety "abstract" cInfo#is_abstract
  end



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
open CHPretty

(* chutil *)
open CHFileIO
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm

(* jchpre *)
open JCHApplication
open JCHClassSummary
open JCHFunctionSummary
open JCHFunctionSummaryLibrary
open JCHFunctionSummaryXmlDecoder
open JCHPreAPI
open JCHPreFileIO
open JCHSystemSettings

module P = Pervasives

let ccNode =
  xml_string 
    "copyright-notice" "Copyright 2012-2020, Kestrel Technology LLC, Palo Alto, CA 94304"

let summary_classpath = ref None

let get_summary_classpath () =
  match !summary_classpath with
  | None ->
    let cp = system_settings#get_summary_classpath in
    begin summary_classpath := Some cp ; cp end	
  | Some cp -> cp

let load_class_library_summary cn =
  let summaryClasspath = get_summary_classpath () in
  if JCHFile.has_summary_class summaryClasspath cn then
    let summaryString = JCHFile.get_summary_class summaryClasspath cn in
    let summary = read_xml_class_file_from_string cn#name summaryString in
    function_summary_library#add_class_summary summary
  else
    ()
  

let write_xml_method_summary (node:xml_element_int) (mInfo:method_info_int) =
  let cms = mInfo#get_class_method_signature in
  let ms = cms#method_signature in
  let append = node#appendChildren in
  let summary =
    if function_summary_library#has_method_summary cms then
      Some (function_summary_library#get_method_summary cms)
    else
      None in
  (* ---------------------------------------------------------- time-cost *)
  let timecost =
    match summary with
    | Some s -> s#get_time_cost
    | _ -> top_jterm_range in
  if timecost#is_top then
    ()
  else
    let tNode = xmlElement "time-cost" in
    let cNode = xmlElement "cost" in
    begin
      timecost#write_xmlx cNode ms ;
      tNode#appendChildren [ cNode ] ;
      append [ tNode ]
    end
  
let write_xmlx_method
      (node:xml_element_int) (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let mInfo = app#get_method cms in
  let ms = cms#method_signature in
  let _ = node#setNameString ms#name in
  (* ---------------------------------------------------- signature *)
  let _ =
    let sNode = xmlElement "signature" in
    let _ = cms#method_signature#write_xmlx sNode in
    append [ sNode ] in
  (* ---------------------------------------------------- exceptions *)
  let _ =
    let eeNode = xmlElement "exceptions" in
    append [ eeNode ] in
  (* ------------------------------------------------------  summary *)
  let _ =
    let fNode = xmlElement "summary" in
    let _ = write_xml_method_summary fNode mInfo in
    append [ fNode ] in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cms#name ;
      sety "final" mInfo#is_final ;
      sety "abstract" mInfo#is_abstract ;
      sety "static" mInfo#is_static ;
      sety "bridge" mInfo#is_bridge ;
      sety "native" mInfo#is_native ;
      set "access" (access_to_string mInfo#get_visibility) ;
    end in
  ()

  
let write_xmlx_constructor
      (node:xml_element_int)  (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let mInfo = app#get_method cms in
  let _ =
    let argtypes =
      List.map value_type_to_string
               cms#method_signature#method_signature_data#descriptor#arguments in
    let nameString = "(" ^ (String.concat "," argtypes) ^ ")" in
    node#setNameString nameString in
  (* ---------------------------------------------------- signature *)
  let _ =
    let sNode = xmlElement "signature" in
    let _ = cms#method_signature#write_xmlx sNode in
    append [ sNode ] in
  (* ---------------------------------------------------- exceptions *)
  let _ =
    let eeNode = xmlElement "exceptions" in
    append [ eeNode ] in
  (* ------------------------------------------------------  summary *)
  let _ =
    let fNode = xmlElement "summary" in
    let _ = write_xml_method_summary fNode mInfo in
    append [ fNode ] in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      set "access" (access_to_string mInfo#get_visibility) ;
    end in
  ()


let write_xmlx_interface_method
      (node:xml_element_int) (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let mInfo = app#get_method cms in
  let _ = node#setNameString  mInfo#get_method_name in
  (* ---------------------------------------------------- signature *)
  let _ =
    let sNode = xmlElement "signature" in
    let _ = cms#method_signature#write_xmlx sNode in
    append [ sNode ] in
  (* ---------------------------------------------------- exceptions *)
  let _ =
    let eeNode = xmlElement "exceptions" in
    append [ eeNode ] in
  (* ------------------------------------------------------  summary *)
  let _ =
    let fNode = xmlElement "summary" in
    let _ = write_xml_method_summary fNode mInfo in
    append [ fNode ] in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cms#name ;
      sety "final" mInfo#is_final ;
      sety "abstract" mInfo#is_abstract ;
      sety "static" mInfo#is_static ;
      sety "bridge" mInfo#is_bridge ;
      sety "native" mInfo#is_native ;
      set "access" (access_to_string mInfo#get_visibility) ;
    end in
  ()

  
let write_xml_summary_class
      (node:xml_element_int) (cInfo:class_info_int) =
  let cn = cInfo#get_class_name in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety key v = if v then set key "yes" else () in
  (* ----------------------------------------------------- interfaces *)
  let _ =
    let iiNode = xmlElement "interfaces" in
    let interfaces = app#get_all_interfaces cn in
    let hasSuperClass =
      cInfo#has_super_class && 
        (not (cInfo#get_super_class#name = "java.lang.Object")) in
    let  _ =
      iiNode#appendChildren
        (List.map (fun i ->
             xml_string "implements" i#name) interfaces) in
    let _ =
      if hasSuperClass then
        append [ xml_string "superclass" cInfo#get_super_class#name ] in
    append [ iiNode ] in

  (* ----------------------------------------------- class properties *)
  let _ =
    if function_summary_library#has_class_summary cn then
      let summary = function_summary_library#get_class_summary cn in
      let cprops = summary#get_class_properties in
      match summary#get_class_properties with
      | [] -> ()
      | _ ->
         let ppNode = xmlElement "class-properties" in
         let _ =
           ppNode#appendChildren
             (List.map (fun p ->
                  let pNode = xmlElement "cprop" in
                  begin
                    write_xml_class_property pNode p ;
                    pNode
                  end) cprops) in
         append [ ppNode ] in
  
  (* --------------------------------------------------- constructors *)
  let _ =
    let xxNode = xmlElement "constructors" in
    let _ = xxNode#setGroupString "CONSTRUCTORS" in
    let cmss = List.map (make_cms cn) cInfo#get_methods_defined in
    let cmss = List.filter (fun c -> c#name = "<init>") cmss in
    let _ =
      List.iter (fun cms ->
          if app#has_method cms then () else
            app#add_method (cInfo#get_method cms#method_signature)) cmss in
    let _ =
      xxNode#appendChildren
        (List.map (fun cms ->
             let mNode = xmlElement "constructor"  in
             begin
               write_xmlx_constructor mNode cms ;
               mNode
             end) cmss) in
    append [ xxNode ] in   
  
  (* -------------------------------------------------------- methods *)
  let _ =
    let mmNode = xmlElement "methods" in
    let _ = mmNode#setGroupString "METHODS" in
    let cmss = List.map (make_cms cn) cInfo#get_methods_defined in
    let cmss =                    (* exclude class/object constructors *)
      List.filter (fun c ->
          not (List.mem c#name [ "<clinit>" ; "<init>" ])) cmss in
    let _ =
      List.iter (fun cms ->
          if app#has_method cms then () else
            app#add_method (cInfo#get_method cms#method_signature)) cmss in
    let cmss = List.sort (fun c1 c2 -> P.compare c1#name c2#name) cmss in
    let _ =
      mmNode#appendChildren
        (List.map (fun cms ->
             let mNode = xmlElement "method" in
             begin
               write_xmlx_method mNode cms ;
               mNode
             end) cmss) in
    append [ mmNode ] in
  
  (* ----------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cn#simple_name ;
      set "package" cn#package_name ;
      sety "final" cInfo#is_final ;
      sety "abstract" cInfo#is_abstract ;
      sety "immutable" cInfo#is_immutable
    end in
  ()
  
  
let write_xml_summary_interface
      (node:xml_element_int) (cInfo:class_info_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let cn = cInfo#get_class_name in
  (* ----------------------------------------------------- interfaces *)
  let _ =
    let ssNode = xmlElement "superinterfaces" in
    let interfaces = app#get_all_interfaces cn in
    let _ =
      ssNode#appendChildren
        (List.map (fun cni ->
             xml_string "superinterface" cni#name) interfaces) in
    append [ ssNode ] in
    
  (* ----------------------------------------------- class properties *)
  let _ =
    if function_summary_library#has_class_summary cn then
      let summary = function_summary_library#get_class_summary cn in
      let cprops = summary#get_class_properties in
      match summary#get_class_properties with
      | [] -> ()
      | _ ->
         let ppNode = xmlElement "class-properties" in
         let _ =
           ppNode#appendChildren
             (List.map (fun p ->
                  let pNode = xmlElement "cprop" in
                  begin
                    write_xml_class_property pNode p ;
                    pNode
                  end) cprops) in
         append [ ppNode ] in

  (* -------------------------------------------------------- methods *)
  let _ =
    let mmNode = xmlElement "methods" in
    let _ = mmNode#setGroupString "METHODS" in
    let cmss = List.map (make_cms cn) cInfo#get_methods_defined in
    let cmss =
      List.filter (fun  c ->
          not (List.mem c#name [ "<clinit>" ; "<init>" ])) cmss in
    let cmss = List.sort (fun c1 c2 -> P.compare c1#name c2#name) cmss in
    let _ =
      List.iter (fun cms ->
          if app#has_method cms then () else
            app#add_method  (cInfo#get_method cms#method_signature)) cmss in
    let _ =
      mmNode#appendChildren
        (List.map (fun cms ->
             let mNode = xmlElement "method" in
             begin write_xmlx_interface_method mNode cms ; mNode end) cmss) in
    append [ mmNode ] in

  (* ----------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cn#simple_name ;
      set "package" cn#package_name ;
    end in
  ()

let save_xml_class_or_interface_summary (cn:class_name_int) =
  let _ = load_class_library_summary cn in
  let cInfo = app#get_class cn in
  let tag = if cInfo#is_interface then "interface" else "class" in
  let node = xmlElement tag in
  let doc = xmlDocument () in
  let root = get_jch_root tag in
  begin
    doc#setNode root ;
    root#appendChildren [ node ; ccNode ] ;
    (if cInfo#is_interface then
       write_xml_summary_interface node cInfo
     else
       write_xml_summary_class node cInfo) ;
    file_output#saveFile (cn#simple_name ^ ".xml") doc#toPretty
  end

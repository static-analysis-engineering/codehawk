(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny Sipma

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

(* jchpre *)
open JCHApplication
open JCHClassSummary
open JCHFunctionSummary
open JCHFunctionSummaryLibrary
open JCHFunctionSummaryXmlDecoder
open JCHPreAPI
open JCHPreFileIO
open JCHSystemSettings
open JCHTemplateUtil


let ccNode =
  xml_string
    "copyright-notice"
    "Copyright 2020-2024, Henny Sipma, Palo Alto, CA 94306"

let summary_classpath = ref None


let write_xmlx_field (node:xml_element_int) (cfs:class_field_signature_int) =
  let fInfo = app#get_field cfs in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety key v = if v then set key "yes" else () in
  let sNode = xmlElement "signature" in
  begin
    write_xmlx_value_type sNode cfs#field_signature#descriptor;
    append [sNode];
    (if fInfo#has_value then
	let vNode = xmlElement "value" in
	begin
	  write_xmlx_constant_value vNode fInfo#get_value;
	  append [vNode]
	end);
    sety "static" fInfo#is_static;
    sety "final" fInfo#is_final;
    sety "not-null" fInfo#is_not_null;
    set "access" (access_to_string fInfo#get_visibility);
    set "name" cfs#field_signature#name;
    node#setNameString ("field:"^ cfs#field_signature#name)
  end


let get_summary_classpath () =
  match !summary_classpath with
  | None ->
    let cp = system_settings#get_summary_classpath in
    begin summary_classpath := Some cp; cp end
  | Some cp -> cp


let load_class_library_summary cn =
  try
    let summaryClasspath = get_summary_classpath () in
    if JCHFile.has_summary_class summaryClasspath cn then
      let summaryString = JCHFile.get_summary_class summaryClasspath cn in
      let summary = read_xml_class_file_from_string cn#name summaryString in
      function_summary_library#add_class_summary summary
    else
      ()
  with
  | JCHFile.No_class_found _ ->
     raise (JCH_failure (LBLOCK [STR "No class found: "; cn#toPretty]))


let write_xml_method_summary (node:xml_element_int) (mInfo:method_info_int) =
  let cms = mInfo#get_class_method_signature in
  let ms = cms#method_signature in
  let append = node#appendChildren in
  let summary =
    if function_summary_library#has_method_summary cms then
      Some (function_summary_library#get_method_summary cms)
    else
      None in
  (* -------------------------------------------------------- taint *)
  let _ =
    let tnode = xmlElement "taint" in
    let _ =
      match summary with
      | Some s -> s#get_taint#write_xml tnode ms
      | _ -> () in
    append [tnode] in
  (* ----------------------------------------------- postconditions *)
  let _ =
    match summary  with
    | None -> ()
    | Some s ->
       let postconditions = s#get_post @ s#get_error_post in
       match postconditions with
       | [] -> ()
       | _ ->
          let ppNode = xmlElement "postconditions" in
          begin
            ppNode#appendChildren
              (List.map
                 (fun p ->
                   let tag = if p#is_error then "error-post" else "post" in
                   let pnode = xmlElement tag in
                   begin p#write_xml pnode ms; pnode end) postconditions);
            append [ppNode]
          end in
  (* --------------------------------------------------------- side effects *)
  let _ =
    match summary with
    | None -> ()
    | Some s ->
       let sideeffects = s#get_sideeffects in
       match sideeffects with
       | [] ->  ()
       | _ ->
          let ssNode = xmlElement "side-effects" in
          begin
            ssNode#appendChildren
              (List.map
                 (fun s ->
                   let sNode = xmlElement "side-effect" in
                   begin write_xml_sideeffect sNode s ms; sNode end) sideeffects);
            append [ssNode]
          end in

  (* --------------------------------------------------------- sinks *)
  let _ =
    let sinks =
      match summary with
      | Some s -> (s#get_string_sinks, s#get_resource_sinks)
      | _ -> ([],[]) in
    let _ =
      match sinks with
      | ([],[]) -> ()
      | (sl,rl) ->
         let ssnode = xmlElement "sinks" in
         let _ =
           ssnode#appendChildren
             (List.map (fun s ->
                  let snode = xmlElement "sink" in
                  begin
                    s#write_xml snode ms;
                    snode#setAttribute "type" "string";
                    snode
                  end) sl) in
         let _ =
           ssnode#appendChildren
             (List.map (fun s ->
                  let snode = xmlElement "sink" in
                  begin
                    s#write_xml snode ms;
                    snode#setAttribute "type" "resource";
                    snode
                  end) rl) in
         append [ssnode] in
    () in
  match summary with None -> false | _ -> true


let get_exceptions mInfo =
  let cms = mInfo#get_class_method_signature in
  if function_summary_library#has_method_summary  cms then
    let summary = function_summary_library#get_method_summary cms in
    let einfos = summary#get_exception_infos in
    List.fold_left
      (fun acc c ->
        if List.exists (fun e -> e#get_exception#equal c) acc then
          acc
        else
          (make_exception_info c) :: acc) einfos mInfo#get_exceptions
  else
    List.map make_exception_info mInfo#get_exceptions


let write_xml_exceptions
      (node:xml_element_int)
      (ms:method_signature_int)
      (einfos:exception_info_int list) =
  node#appendChildren
    (List.map (fun einfo ->
         if einfo#has_safety_condition then
           let eNode = xmlElement "c-throws" in
           begin einfo#write_xml eNode ms; eNode end
         else
           xml_string "throws" einfo#get_exception#name) einfos)


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
    append [sNode] in
  (* ---------------------------------------------------- exceptions *)
  let _ =
    let exceptions = get_exceptions mInfo in
    let eeNode = xmlElement "exceptions" in
    let _ = write_xml_exceptions eeNode ms exceptions in
    append [eeNode]  in
  (* ------------------------------------------------------  summary *)
  let fromsummary =
    let fNode = xmlElement "summary" in
    let fromsummary = write_xml_method_summary fNode mInfo in
    begin
      append [fNode];
      fromsummary
    end in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cms#name;
      sety "final" mInfo#is_final;
      sety "abstract" mInfo#is_abstract;
      sety "static" mInfo#is_static;
      sety "bridge" mInfo#is_bridge;
      sety "native" mInfo#is_native;
      set "access" (access_to_string mInfo#get_visibility);
      (if not fromsummary then set "valid" "no");
    end in
  ()


let write_xmlx_constructor
      (node:xml_element_int)  (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let mInfo = app#get_method cms in
  let ms = cms#method_signature in
  let _ =
    let argtypes =
      List.map
        value_type_to_string
        cms#method_signature#method_signature_data#descriptor#arguments in
    let nameString = "(" ^ (String.concat "," argtypes) ^ ")" in
    node#setNameString nameString in
  (* ---------------------------------------------------- signature *)
  let _ =
    let sNode = xmlElement "signature" in
    let _ = cms#method_signature#write_xmlx sNode in
    append [sNode] in
  (* ---------------------------------------------------- exceptions *)
  let _ =
    let exceptions = get_exceptions mInfo in
    let eeNode = xmlElement "exceptions" in
    let _ = write_xml_exceptions eeNode ms exceptions in
    append [eeNode]  in
  (* ------------------------------------------------------  summary *)
  let fromsummary =
    let fNode = xmlElement "summary" in
    let fromsummary = write_xml_method_summary fNode mInfo in
    begin
      append [fNode];
      fromsummary
    end in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      set "access" (access_to_string mInfo#get_visibility);
      (if not fromsummary then set "valid" "no")
    end in
  ()


let write_xmlx_interface_method
      (node:xml_element_int) (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let mInfo = app#get_method cms in
  let ms = cms#method_signature in
  let _ = node#setNameString  mInfo#get_method_name in
  (* ---------------------------------------------------- signature *)
  let _ =
    let sNode = xmlElement "signature" in
    let _ = cms#method_signature#write_xmlx sNode in
    append [sNode] in
  (* ---------------------------------------------------- exceptions *)
  let _ =
    let exceptions = get_exceptions mInfo in
    let eeNode = xmlElement "exceptions" in
    let _ = write_xml_exceptions eeNode ms exceptions in
    append [eeNode]  in
  (* ------------------------------------------------------  summary *)
  let fromsummary =
    let fNode = xmlElement "summary" in
    let fromsummary = write_xml_method_summary fNode mInfo in
    begin
      append [fNode];
      fromsummary
    end in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cms#name;
      sety "final" mInfo#is_final;
      sety "abstract" mInfo#is_abstract;
      sety "static" mInfo#is_static;
      sety "bridge" mInfo#is_bridge;
      sety "native" mInfo#is_native;
      set "access" (access_to_string mInfo#get_visibility);
      (if not fromsummary then  set "valid" "no")
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
        append [xml_string "superclass" cInfo#get_super_class#name] in
    append [iiNode] in

  (* ----------------------------------------------- class properties *)
  let _ =
    if function_summary_library#has_class_summary cn then
      let summary = function_summary_library#get_class_summary cn in
      let cprops = summary#get_class_properties in
      let _ = sety "immutable" summary#is_immutable in
      match summary#get_class_properties with
      | [] -> ()
      | _ ->
         let ppNode = xmlElement "class-properties" in
         let _ =
           ppNode#appendChildren
             (List.map (fun p ->
                  let pNode = xmlElement "cprop" in
                  begin
                    write_xml_class_property pNode p;
                    pNode
                  end) cprops) in
         append [ppNode] in

  (* --------------------------------------------------------- fields *)
  let _ =
    let ffNode = xmlElement "fields" in
    let _ = ffNode#setGroupString  "FIELDS" in
    let cfss =
      try
        List.map (fun fs -> make_cfs cn fs) cInfo#get_fields_defined
      with
      | JCHFile.No_class_found s ->
         raise
           (JCH_failure
              (LBLOCK [
                   STR "get fields defined: ";
                   cn#toPretty;
                   STR "; No class found:  ";
                   STR s])) in
    let cfss =
      List.filter (fun cfs ->
          let _ =
            if app#has_field cfs then
              ()
            else
              app#add_field (cInfo#get_field cfs#field_signature) in
          let fInfo = app#get_field cfs in
          fInfo#is_public || fInfo#is_protected) cfss in
    let cfssInherited = get_inherited_fields ~allfields:false cn in
    let _ =
      begin
        ffNode#appendChildren
          (List.map (fun cfs ->
               let fNode = xmlElement "field" in
               begin write_xmlx_field fNode cfs; fNode end) cfss);
        ffNode#appendChildren
          (List.map (fun (fs,cn) ->
               let fNode = xmlElement "field" in
               begin
                 write_xmlx_inherited_field fNode fs cn;
                 fNode
               end) cfssInherited)
      end in
    append [ffNode] in
  (* --------------------------------------------------- constructors *)
  let _ =
    let xxNode = xmlElement "constructors" in
    let _ = xxNode#setGroupString "CONSTRUCTORS" in
    let cmss = List.map (make_cms cn) cInfo#get_methods_defined in
    let cmss = List.filter (fun c -> c#name = "<init>") cmss in
    let cmss =
      List.filter (fun cms ->
          let _ =
            if app#has_method cms then () else
              app#add_method (cInfo#get_method cms#method_signature) in
          let mInfo = app#get_method cms in
          mInfo#is_public || mInfo#is_protected) cmss in
    let _ =
      xxNode#appendChildren
        (List.map (fun cms ->
             let mNode = xmlElement "constructor"  in
             begin
               write_xmlx_constructor mNode cms;
               mNode
             end) cmss) in
    append [xxNode] in

  (* -------------------------------------------------------- methods *)
  let _ =
    let mmNode = xmlElement "methods" in
    let _ = mmNode#setGroupString "METHODS" in
    let cmss = List.map (make_cms cn) cInfo#get_methods_defined in
    let cmss =                    (* exclude class/object constructors *)
      List.filter (fun c ->
          not (List.mem c#name ["<clinit>"; "<init>"])) cmss in
    let cmss =                (* only include public/protected methods *)
      List.filter (fun cms ->
          let _ =
            if app#has_method cms then
              ()
            else
              app#add_method (cInfo#get_method cms#method_signature) in
          let mInfo = app#get_method cms in
          mInfo#is_public || mInfo#is_protected) cmss in
    let cmss = List.sort (fun c1 c2 -> Stdlib.compare c1#name c2#name) cmss in
    let cmssInherited =
      List.sort
        (fun c1 c2 -> Stdlib.compare (fst c1)#name (fst c2)#name)
        (get_inherited_methods cn) in
    let _ =
      begin
        mmNode#appendChildren
          (List.map (fun cms ->
               let mNode = xmlElement "method" in
               begin
                 write_xmlx_method mNode cms;
                 mNode
               end) cmss);
        mmNode#appendChildren
          (List.map (fun (ms,cn) ->
               let mNode = xmlElement "method" in
               begin
                 write_xmlx_inherited_method mNode ms cn;
                 mNode
               end) cmssInherited)
      end in
    append [mmNode] in

  (* ----------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cn#simple_name;
      set "package" cn#package_name;
      sety "final" cInfo#is_final;
      sety "abstract" cInfo#is_abstract
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
    append [ssNode] in

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
                    write_xml_class_property pNode p;
                    pNode
                  end) cprops) in
         append [ppNode] in

  (* --------------------------------------------------------- fields *)
  let _ =
    let ffNode = xmlElement "fields" in
    let _ = ffNode#setGroupString "FIELDS" in
    let cfss =
      try
        List.map (fun fs -> make_cfs cn fs) cInfo#get_fields_defined
      with
      | JCHFile.No_class_found s ->
         raise
           (JCH_failure
              (LBLOCK [
                   STR "get fields defined: ";
                   cn#toPretty;
                   STR "; No class found:  ";
                   STR s])) in
    let cfss =
      List.filter (fun cfs ->
          let _ =
            if app#has_field cfs then
              ()
            else
              app#add_field (cInfo#get_field cfs#field_signature) in
          let fInfo = app#get_field cfs in
          fInfo#is_public || fInfo#is_protected) cfss in
    let _ =
      ffNode#appendChildren
        (List.map (fun cfs ->
             let fNode = xmlElement "field" in
             begin
               write_xmlx_field fNode cfs;
               fNode
             end) cfss) in
    append [ffNode] in

  (* -------------------------------------------------------- methods *)
  let _ =
    let mmNode = xmlElement "methods" in
    let _ = mmNode#setGroupString "METHODS" in
    let cmss = List.map (make_cms cn) cInfo#get_methods_defined in
    let cmss =
      List.filter (fun  c ->
          not (List.mem c#name ["<clinit>"; "<init>"])) cmss in
    let cmss = List.sort (fun c1 c2 -> Stdlib.compare c1#name c2#name) cmss in
    let _ =
      List.iter (fun cms ->
          if app#has_method cms then () else
            app#add_method  (cInfo#get_method cms#method_signature)) cmss in
    let _ =
      mmNode#appendChildren
        (List.map (fun cms ->
             let mNode = xmlElement "method" in
             begin write_xmlx_interface_method mNode cms; mNode end) cmss) in
    append [mmNode] in

  (* ----------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cn#simple_name;
      set "package" cn#package_name;
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
    doc#setNode root;
    root#appendChildren [node; ccNode];
    (if cInfo#is_interface then
       write_xml_summary_interface node cInfo
     else
       write_xml_summary_class node cInfo);
    file_output#saveFile (cn#simple_name ^ ".xml") doc#toPretty
  end

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
open JCHFile
open JCHJTerm

(* jchpre *)
open JCHApplication
open JCHBcPattern
open JCHBcPatternSummary
open JCHClassSummary
open JCHFunctionSummary
open JCHFunctionSummaryLibrary
open JCHFunctionSummaryXmlDecoder
open JCHPreAPI
open JCHPreFileIO
open JCHSystemSettings
open JCHTemplateUtil

module P = Pervasives

let ccNode =
  xml_string 
    "copyright-notice" "Copyright 2012-2020, Kestrel Technology LLC, Palo Alto, CA 94304"

let api_summary_classpath = ref None
let profile_summary_classpath = ref None
let supplement_summary_classpath = ref None

let set_api_summary_classpath s =
  if s =  "" || s = " " then () else
    api_summary_classpath := Some (JCHFile.class_path s)

let set_profile_summary_classpath s =
  if s = "" || s = " " then () else
    profile_summary_classpath := Some (JCHFile.class_path s)
  
let set_supplement_summary_classpath s =
  if  s = "" || s = " " then () else
    supplement_summary_classpath := Some (JCHFile.class_path s)

let apisummaries = mk_function_summary_library ()
let profilesummaries = mk_function_summary_library ()
let supplementsummaries = mk_function_summary_library ()

let load_class_summary classpath library cn =
  match classpath with
  | Some cp ->
     if JCHFile.has_summary_class cp cn then
       let summaryString = JCHFile.get_summary_class cp cn in
       let summary = read_xml_class_file_from_string cn#name summaryString in
       library#add_class_summary summary
     else
       ()
  |  _ ->
      pr_debug [ STR "No summary found for " ; cn#toPretty ; NL ]

let load_api_summary cn =
  load_class_summary !api_summary_classpath apisummaries cn

let get_api_class_summary cn =
  if apisummaries#has_class_summary cn then
    Some (apisummaries#get_class_summary cn)
  else
    None

let get_api_summary cms =
  if apisummaries#has_method_summary cms then
    Some (apisummaries#get_method_summary cms)
  else
    None

let load_profile_summary cn =
  load_class_summary !profile_summary_classpath profilesummaries cn

let get_profile_class_summary cn =
  if profilesummaries#has_class_summary cn  then
    Some (profilesummaries#get_class_summary cn)
  else
    None

let get_profile_summary cms =
  if profilesummaries#has_method_summary cms then
    Some (profilesummaries#get_method_summary cms)
  else
    None

let load_supplement_summary cn =
  load_class_summary !supplement_summary_classpath supplementsummaries cn

let get_supplement_summary cms =
  if supplementsummaries#has_method_summary cms then
    Some (supplementsummaries#get_method_summary cms)
  else
    None

let get_class_codependents (c:java_class_or_interface_int) =
  let result = c#get_interfaces in
  match c#get_super_class with Some sc -> sc :: result | _ -> result

let load_class (c:java_class_or_interface_int) =
  let coDependents = get_class_codependents c in
  let methods = List.filter (fun m -> m#is_concrete) c#get_methods in
  begin
    List.iter (fun d -> 
      if app#has_class d then () else app#add_missing_class d) coDependents ;
    app#add_class c ;
    List.iter app#add_method methods ;
  end

let rec load_class_and_dependents (cn:class_name_int) =
  if app#has_class cn then () else
    let cp = system_settings#get_classpath in
    let c = get_class cp cn in
    let classes = c :: (List.map (get_class cp) c#get_interfaces) in
    let load_super c = 
      match c#get_super_class with 
      | Some sc -> load_class_and_dependents sc | _ -> () in
    begin
      List.iter app#add_class classes ;
      List.iter load_super classes ;
      List.iter load_class_and_dependents c#get_interfaces 
    end

module MethodSignatureCollections = CHCollections.Make (
  struct
    type t = method_signature_int
    let compare ms1 ms2 = ms1#compare ms2
    let toPretty ms = ms#toPretty
  end)

let write_xmlx_field (node:xml_element_int) (cfs:class_field_signature_int) =
  let fInfo = app#get_field cfs in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety key v = if v then set key "yes" else () in
  let sNode = xmlElement "signature" in
  begin
    write_xmlx_value_type sNode cfs#field_signature#descriptor ;
    append [ sNode ] ;
    (if fInfo#has_value then
	let vNode = xmlElement "value" in
	begin 
	  write_xmlx_constant_value vNode fInfo#get_value ; 
	  append [ vNode ] 
	end) ;
    sety "static" fInfo#is_static ;
    sety "final" fInfo#is_final ;
    sety "not-null" fInfo#is_not_null ;
    set "access" (access_to_string fInfo#get_visibility) ;
    set "name" cfs#field_signature#name ;
    node#setNameString ("field:"^ cfs#field_signature#name)
  end

let get_inherited_interface_methods (cInfo:class_info_int) =
  let interfaces = app#get_all_interfaces cInfo#get_class_name in
  let inheritedMethods = new MethodSignatureCollections.table_t in
  let definedMethods = new MethodSignatureCollections.set_t in
  let _ = List.iter definedMethods#add cInfo#get_methods_defined in
  let _ = List.iter (fun cni ->
    let _ = if app#has_class cni then () else load_class_and_dependents cni in
    let cniInfo = app#get_class cni in
    let iDefined = 
      List.filter (fun ms -> not (List.mem ms#name [ "<clinit>" ; "<init>" ]))
	cniInfo#get_methods_defined in
    List.iter (fun ms -> 
      if definedMethods#has ms then () else inheritedMethods#set ms cni) iDefined)
    interfaces in
  inheritedMethods#listOfPairs

let join_taint (t1:taint_int option) (t2:taint_int option) =
  match (t1,t2) with
  | (None,None) -> None
  | (None,_) -> t2
  | (_,None) -> t1
  | (Some taint1,Some taint2) ->
     let t = make_taint taint1#get_elements in
     let _ = List.iter t#add_element taint2#get_elements in
     Some t

let join_sinks l1 l2 = ((fst l1) @ (fst l2),(snd l1) @ (snd l2))

let write_xml_method_summary (node:xml_element_int) (mInfo:method_info_int) =
  let cms = mInfo#get_class_method_signature in
  let ms = cms#method_signature in
  let append = node#appendChildren in
  let apisummary = get_api_summary cms  in
  let profilesummary = get_profile_summary cms in
  let supplementsummary = get_supplement_summary cms in
  (* -------------------------------------------------------- taint *)
  let _ =
    let apitaint =
      match apisummary with
      | Some s -> Some s#get_taint
      | _ -> None in
    let supplementtaint =
      match supplementsummary with
      | Some s -> Some s#get_taint
      | _ -> None in
    match join_taint apitaint supplementtaint with
    | Some t ->
       let tNode = xmlElement "taint" in
       begin t#write_xml tNode ms ; append [ tNode ] end
    | _  -> () in
  (* ----------------------------------------------------- time cost *)
  let _ =
    let cost =
      match supplementsummary with
      | Some s -> s#get_time_cost
      | _ -> top_jterm_range in
    let cost =
      if cost#is_top then
        match profilesummary with
        | Some s -> s#get_time_cost
        | _ -> top_jterm_range
      else
        cost in
    if cost#is_top then
      ()
    else
      let tNode = xmlElement "time-cost" in
      let cNode = xmlElement "cost"  in
      begin
        cost#write_xmlx cNode ms ;
        tNode#appendChildren [ cNode ] ;
        node#appendChildren [ tNode ]
      end in
  (* ----------------------------------------------- postconditions *)
  let _ =
    let apipostconditions =
      match apisummary with
      | Some s -> s#get_post
      | _ -> [] in
    let supplementpostconditions =
      match supplementsummary with
      | Some s -> s#get_post
      | _ -> [] in
    match apipostconditions @ supplementpostconditions with
    | [] -> ()
    | l ->
       let ppNode = xmlElement "postconditions" in
       begin
         ppNode#appendChildren
           (List.map
              (fun p ->
                let tag = if p#is_error then "error-post" else "post" in
                let pnode = xmlElement tag in
                begin p#write_xml pnode ms ; pnode end) l) ;
         append [ ppNode ]
       end in
  (* --------------------------------------------------------- side effects *)
  let _ =
    let apisideeffects =
      match apisummary with
      | Some s -> s#get_sideeffects
      | _ -> [] in
    let supplementsideeffects =
      match supplementsummary with
      | Some s -> s#get_sideeffects
      | _ -> []  in
    match apisideeffects @ supplementsideeffects with
    | [] -> ()
    | l ->
       let ssNode = xmlElement "side-effects" in
       begin
         ssNode#appendChildren
           (List.map
              (fun s ->
                let sNode = xmlElement "side-effect" in
                begin write_xml_sideeffect sNode s ms ; sNode end) l) ;
         append [ ssNode ]
       end in
  (* --------------------------------------------------------- sinks *)
  let _ =
    let apisinks =
      match apisummary with
      | Some s -> (s#get_string_sinks, s#get_resource_sinks)
      | _ -> ([],[]) in
    let supplementsinks  =
      match supplementsummary with
      | Some s -> (s#get_string_sinks, s#get_resource_sinks)
      | _ -> ([],[]) in
    let _ =
      match join_sinks apisinks supplementsinks with
      | ([],[]) -> ()
      | (sl,rl) ->
         let ssnode = xmlElement "sinks" in
         let _ =
           ssnode#appendChildren
             (List.map (fun s ->
                  let snode = xmlElement "sink" in
                  begin
                    s#write_xml snode ms ;
                    snode#setAttribute "type" "string" ;
                    snode
                  end) sl) in
         let _ =
           ssnode#appendChildren
             (List.map (fun s ->
                  let snode = xmlElement "sink" in
                  begin
                    s#write_xml snode ms;
                    snode#setAttribute "type" "resource" ;
                    snode
                  end) rl) in
         append [ ssnode ] in
    () in
  (* match (apisummary,supplementsummary) with
  | (None,None) -> false
  | _ -> true *)
  match apisummary with
  | None -> false
  | _ -> true
       
  
let get_exceptions mInfo =
  let cms = mInfo#get_class_method_signature in
  let einfos = List.map make_exception_info mInfo#get_exceptions in
  if apisummaries#has_method_summary cms then
    let summary = apisummaries#get_method_summary cms in
    summary#get_exception_infos @ einfos
  else
    einfos

let write_xml_exceptions
      (node:xml_element_int) (ms:method_signature_int) (einfos:exception_info_int list) =
  node#appendChildren
    (List.map (fun einfo ->
         if einfo#has_safety_condition then
           let eNode = xmlElement "c-throws" in
           begin einfo#write_xml eNode ms ; eNode end
         else
           xml_string "throws" einfo#get_exception#name) einfos)
  
let write_xmlx_method
      (node:xml_element_int) (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
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
    let exceptions = get_exceptions mInfo in
    let eeNode = xmlElement "exceptions" in
    let _ = write_xml_exceptions eeNode ms exceptions in
    append [ eeNode ]  in
  (* ------------------------------------------------------  summary *)
  let isvalidsummary =
    let fNode = xmlElement "summary" in
    let isvalidsummary = write_xml_method_summary fNode mInfo in
    begin
      append [ fNode ] ;
      isvalidsummary
    end in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cms#name ;
      (if mInfo#has_bytecode then
         seti "instrs" mInfo#get_bytecode#get_code#instr_count) ;
      sety "final" mInfo#is_final ;
      sety "abstract" mInfo#is_abstract ;
      sety "static" mInfo#is_static ;
      sety "bridge" mInfo#is_bridge ;
      sety "native" mInfo#is_native ;
      set "access" (access_to_string mInfo#get_visibility) ;
      (if not isvalidsummary then set "valid" "no")
    end in
  ()

  
let write_xmlx_constructor
      (node:xml_element_int)  (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let mInfo = app#get_method cms in
  let ms = cms#method_signature in
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
    let exceptions = get_exceptions mInfo in
    let eeNode = xmlElement "exceptions" in
    let _ = write_xml_exceptions eeNode ms exceptions in
    append [ eeNode ] in
  (* ------------------------------------------------------  summary *)
  let isvalidsummary =
    let fNode = xmlElement "summary" in
    let isvalidsummary = write_xml_method_summary fNode mInfo in
    begin
      append [ fNode ] ;
      isvalidsummary
    end in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      (if mInfo#has_bytecode then
         seti "instrs" mInfo#get_bytecode#get_code#instr_count) ;
      set "access" (access_to_string mInfo#get_visibility) ;
      (if not isvalidsummary then set "valid" "no")
    end in
  ()


let write_xmlx_interface_method
      (node:xml_element_int) (cms:class_method_signature_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let mInfo = app#get_method cms in
  let ms = cms#method_signature in
  let _ = node#setNameString  mInfo#get_method_name in
  (* ---------------------------------------------------- signature *)
  let _ =
    let sNode = xmlElement "signature" in
    let _ = cms#method_signature#write_xmlx sNode in
    append [ sNode ] in
  (* ---------------------------------------------------- exceptions *)
  let _ =
    let exceptions = get_exceptions mInfo in
    let eeNode = xmlElement "exceptions" in
    let _ = write_xml_exceptions eeNode ms exceptions in
    append [ eeNode ] in
  (* ------------------------------------------------------  summary *)
  let isvalidsummary =
    let fNode = xmlElement "summary" in
    let isvalidsummary = write_xml_method_summary fNode mInfo in
    begin
      append [ fNode ] ;
      isvalidsummary
    end in
  (* ---------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cms#name ;
      (if mInfo#has_bytecode then
         seti "instrs" mInfo#get_bytecode#get_code#instr_count) ;
      sety "final" mInfo#is_final ;
      sety "abstract" mInfo#is_abstract ;
      sety "static" mInfo#is_static ;
      sety "bridge" mInfo#is_bridge ;
      sety "native" mInfo#is_native ;
      set "access" (access_to_string mInfo#get_visibility) ;
      (if not isvalidsummary then set "valid" "no")
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
    let apisummary = get_api_class_summary  cn in
    match apisummary with
    | Some s ->
       let cprops = s#get_class_properties in
       let defaultImplementations = s#get_default_implementations in
       begin
         (match cprops with
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
            append [ ppNode ]) ;
         (match defaultImplementations with
          | [] -> ()
          | l ->
             let ddNode = xmlElement "default-implementations"  in
             begin
               ddNode#appendChildren
                 (List.map (fun d ->
                      xml_string "class" d#name) l) ;
               append [ ddNode ]
             end)
       end
    | _ -> () in
  (* --------------------------------------------------------- fields *)
  let _ =
    let ffNode = xmlElement "fields" in
    let _ = ffNode#setGroupString  "FIELDS" in
    let cfss = List.map (fun fs -> make_cfs cn fs) cInfo#get_fields_defined in
    let _ =
      List.iter (fun cfs ->
          if app#has_field cfs then () else
            app#add_field (cInfo#get_field cfs#field_signature)) cfss in
    let cfssInherited = get_inherited_fields cn in
    let _ =
      begin
        ffNode#appendChildren
          (List.map (fun cfs ->
               let fNode = xmlElement "field" in
               begin write_xmlx_field fNode cfs ; fNode end) cfss) ;
        ffNode#appendChildren
          (List.map (fun (fs,cn) ->
               let fNode = xmlElement "field" in
               begin write_xmlx_inherited_field fNode fs cn ; fNode end) cfssInherited)
      end in
    append [ ffNode ] in
    
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
    let cmssInherited =  get_inherited_methods cn in
    let _ =
      List.iter (fun cms ->
          if app#has_method cms then () else
            app#add_method (cInfo#get_method cms#method_signature)) cmss in
    let cmss = List.sort (fun c1 c2 -> P.compare c1#name c2#name) cmss in
    let _ =
      begin
        mmNode#appendChildren
          (List.map (fun cms ->
               let mNode = xmlElement "method" in
               begin
                 write_xmlx_method mNode cms ;
                 mNode
               end) cmss) ;
        mmNode#appendChildren
          (List.map (fun (ms,cn) ->
               let mNode = xmlElement "method" in
               begin write_xmlx_inherited_method mNode ms cn ; mNode end) cmssInherited)
      end in        
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
  let apisummary = get_api_class_summary cn in
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
    match apisummary with
    | Some s ->
       let cprops = s#get_class_properties in
       let defaultImplementations = s#get_default_implementations in
       begin
         (match cprops with
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
            append [ ppNode ]) ;
         (match defaultImplementations with
          | [] -> ()
          | l ->
             let ddNode = xmlElement "default-implementations"  in
             begin
               ddNode#appendChildren
                 (List.map (fun d ->
                      xml_string "class" d#name) l) ;
               append [ ddNode ]
             end)
       end
    | _ -> () in
  
  (* --------------------------------------------------------- fields *)
  let _ =
    let ffNode = xmlElement "fields" in
    let _ = ffNode#setGroupString "FIELDS" in
    let cfss = List.map (fun fs -> make_cfs cn fs) cInfo#get_fields_defined in
    let _ =
      List.iter (fun cfs ->
          if app#has_field cfs then () else
            app#add_field (cInfo#get_field cfs#field_signature)) cfss in
                 
    let _ =
      ffNode#appendChildren
        (List.map (fun cfs ->
             let fNode = xmlElement "field" in
             begin write_xmlx_field fNode cfs ; fNode end) cfss) in
    append [ ffNode ] in
  (* -------------------------------------------------------- methods *)
  let _ =
    let mmNode = xmlElement "methods" in
    let _ = mmNode#setGroupString "METHODS" in
    let cmss = List.map (make_cms cn) cInfo#get_methods_defined in
    let cmss =
      List.filter (fun  c ->
          not (List.mem c#name [ "<clinit>" ; "<init>" ])) cmss in
    let cmss = List.sort (fun c1 c2 -> P.compare c1#name c2#name) cmss in
    let cmssInherited =  get_inherited_interface_methods cInfo in
    let _ =
      List.iter (fun cms ->
          if app#has_method cms then () else
            app#add_method  (cInfo#get_method cms#method_signature)) cmss in
    let _ =
      begin
        mmNode#appendChildren
          (List.map (fun cms ->
               let mNode = xmlElement "method" in
               begin write_xmlx_interface_method mNode cms ; mNode end) cmss) ;
        mmNode#appendChildren
          (List.map (fun (ms,cn) ->
               let mNode = xmlElement "method" in
               begin write_xmlx_inherited_method mNode ms cn ; mNode end) cmssInherited)
      end in
    append [ mmNode ] in
  (* ----------------------------------------------------- attributes *)
  let _ =
    begin
      set "name" cn#simple_name ;
      set "package" cn#package_name ;
      set "dispatch" "yes"
    end in
  ()
  
  
let save_xml_class_or_interface_summary (cn:class_name_int) =
  let _ = load_api_summary cn in
  let _ = load_profile_summary cn in
  let _ = load_supplement_summary cn in
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

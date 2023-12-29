(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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

(* -----------------------------------------------------------------------------
 * Functionality to construct and save a library method summary xml file
 *------------------------------------------------------------------------------ *)

(* chlib *)
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHFileIO
open CHLogger
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHFile

(* jchpre *)
open JCHApplication
open JCHBcPattern
open JCHBcPatternSummary
open JCHFunctionSummary
open JCHFunctionSummaryLibrary
open JCHFunctionSummaryXmlDecoder
open JCHIFSystem
open JCHPreAPI
open JCHPreFileIO
open JCHPreSumTypeSerializer
open JCHSystemSettings


module MethodSignatureCollections = CHCollections.Make (
  struct
    type t = method_signature_int
    let compare ms1 ms2 = ms1#compare ms2
    let toPretty ms = ms#toPretty
  end)

module FieldSignatureCollections =
  CHCollections.Make (
      struct
        type t = field_signature_int
        let compare fs1 fs2 = fs1#compare fs2
        let toPretty fs = fs#toPretty
      end)

let bytecodemethods = ref 0
let patterned_methods = ref 0
let summarized_methods = ref 0
let nativemethods = ref 0

let add_bytecode_method () = bytecodemethods := !bytecodemethods + 1
let add_patterned_method () = patterned_methods := !patterned_methods + 1
let add_summarized_method () = summarized_methods := !summarized_methods + 1
let add_native_method () = nativemethods := !nativemethods + 1

let get_method_stats () =
  (!bytecodemethods, !patterned_methods, !summarized_methods,!nativemethods)

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

class method_summary_builder_t (mInfo:method_info_int):method_summary_builder_int =
object (self)

  val mutable exception_infos = []
  val mutable postconditions = []
  val mutable sideeffects = []
  val mutable taint = no_taint_info
  val mutable is_valid = false
  val mutable string_sinks = []
  val mutable resource_sinks = []

  method add_exception_info (eInfo:exception_info_int) =
    exception_infos <- eInfo :: exception_infos

  method add_post (post:postcondition_int) =
    postconditions <- post :: postconditions

  method add_sideeffect (sideeffect:sideeffect_t) =
    sideeffects <- sideeffect :: sideeffects

  method set_taint (t:taint_int) = taint <- t

  method set_valid = is_valid <- true

  method add_string_sink (sink:string_sink_int) =
    string_sinks <- sink :: string_sinks

  method add_resource_sink (sink:resource_sink_int) =
    resource_sinks <- sink :: resource_sinks

  method to_function_summary =
    make_function_summary
      ~is_static:mInfo#is_static
      ~is_final:mInfo#is_final
      ~is_abstract:mInfo#is_abstract
      ~is_inherited:false
      ~is_valid
      ~is_bridge:mInfo#is_bridge
      ~visibility:mInfo#get_visibility
      ~exception_infos
      ~post:postconditions
      ~sideeffects
      ~taint
      ~resource_sinks
      ~string_sinks
      mInfo#get_class_method_signature

  method toPretty = self#to_function_summary#toPretty

  method write_xml (node:xml_element_int) = self#to_function_summary#write_xml node

end

let get_inherited_fields (cn:class_name_int) =
  let inheritedFields = new FieldSignatureCollections.table_t in
  let definedFields = new FieldSignatureCollections.set_t in
  let cInfo = ref (app#get_class cn) in
  let _ = List.iter definedFields#add !cInfo#get_fields_defined in
  begin
    while !cInfo#has_super_class do
      let sc = !cInfo#get_super_class in
      let _ = cInfo := app#get_class sc in
      let scDefined = !cInfo#get_fields_defined in
      List.iter (fun fs ->
          if !cInfo#defines_field fs then
            if definedFields#has fs || inheritedFields#has fs then () else
              inheritedFields#set fs sc
          else
            ()) scDefined
    done;
    inheritedFields#listOfPairs
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

let write_xml_default_summary (node:xml_element_int) =
  node#appendChildren [ xmlElement "taint" ]

let write_xml_pattern_summary
      (node:xml_element_int) (mInfo:method_info_int) ?(libsummary:function_summary_int option=None) (p:bc_pattern_t) =
  let cms = mInfo#get_class_method_signature in
  let ms = cms#method_signature in
  let append = node#appendChildren in
  let valid = ref false in
  let get_instrs () =
    let opcodes = mInfo#get_bytecode#get_code in
    let lst = ref [] in
    let _ = opcodes#iteri (fun _ opc -> lst := opc :: !lst) in
    List.rev !lst in
  let logmsg () =
    let instrs = get_instrs () in
    LBLOCK [ cms#toPretty ; NL ;
             INDENT (8,bc_pattern_to_pretty p) ; NL ;
             INDENT (8,LBLOCK [ STR "bytecode: " ; NL ]) ;
             INDENT (8,LBLOCK
                         (List.map (fun p ->
                              LBLOCK [ STR "        " ;
                                       opcode_to_pretty p ; NL ]) instrs)) ; NL ] in
  (* ---------------------------------------------------------- taint *)
  let taint = mk_pattern_taintflow mInfo p in
  let taint =
    match taint with
    | Some t ->
       begin
         (match libsummary with
         | Some s -> List.iter t#add_element s#get_taint_elements
         | _ -> ()) ;
         valid := true ;
         chlog#add "pattern used" (logmsg ()) ;
         t
       end
    | _ ->
       match libsummary with
       | Some s ->
          begin
            valid := true ;            
            make_taint s#get_taint_elements
          end
       | _ ->
          begin
            chlog#add "pattern not used" (logmsg ()) ;
            make_taint []
          end in
  let _ =
    let tnode = xmlElement "taint" in
    begin
      taint#write_xml tnode ms ;
      append [ tnode ]
    end in
  (* -------------------------------------------------- postconditions *)
  let postconditions = mk_pattern_postconditions mInfo p in
  let postconditions =
    match libsummary with
    | Some s -> postconditions @ s#get_post @ s#get_error_post
    | _ -> postconditions in
  let _ =
    match postconditions with
    | [] -> ()
    | l ->
       let ppnode = xmlElement "postconditions" in
       begin
         ppnode#appendChildren
           (List.map
              (fun p ->
                let tag = if p#is_error then "error-post" else "post" in
                let pnode = xmlElement tag in
                begin p#write_xml pnode ms ; pnode end) l) ;
         append [ ppnode ]
       end in
  (* --------------------------------------------------------- sinks *)
  let stringsinks =
    match libsummary with
    | Some s -> s#get_string_sinks
    | _ -> [] in
  let resourcesinks =
    match libsummary with
    | Some s -> s#get_resource_sinks
    | _ -> [] in
  let _ =
    match (stringsinks,resourcesinks) with
    | ([],[]) ->  ()
    | _ ->
       let ssnode = xmlElement "sinks" in
       begin
         ssnode#appendChildren
           (List.map ((fun s ->
                let snode = xmlElement "sink" in
                begin
                  (* TODO: find a method_signature_int for the second argument s#write_xml snode ; *)
                  snode#setAttribute "type" "string" ;
                  snode
                end): (string_sink_int -> xml_element_int)) stringsinks) ;
         ssnode#appendChildren
           (List.map (fun s ->
                let snode = xmlElement "sink" in
                begin
                  (* TODO: find a method_signature_int for the second argument s#write_xml snode ; *)
                  snode#setAttribute "type" "resource" ;
                  snode
                end) resourcesinks) ;
         append [ ssnode ]
       end  in
  !valid
 
let write_xml_method_summary
      (node:xml_element_int) (cInfo:class_info_int) ?(libsummary:function_summary_int option = None) (mInfo:method_info_int) =
  let default () =
    match libsummary with
    | Some s -> begin s#write_xml_summary node ; true end
    | _ -> begin write_xml_default_summary node ; false end in
  if mInfo#has_bytecode then
    let _ = add_bytecode_method () in
    let p = JCHBcPatternSummary.get_pattern mInfo#get_index in
    match p with
    | Some pattern ->
       let valid = write_xml_pattern_summary node mInfo ~libsummary pattern in
       begin
         add_patterned_method () ;
         if valid then add_summarized_method () ;
         valid
       end
    | _ ->
       default ()
  else
    let _ = if mInfo#is_native then add_native_method () in
    default ()

let write_xml_exceptions (node:xml_element_int) ?(libsummary=None) ms exceptions =
  let einfos =
    match libsummary with
    | Some s -> s#get_exception_infos
    | _ -> [] in
  let einfos =
    List.fold_left
      (fun acc e ->
        if List.exists (fun einfo -> einfo#get_exception#equal e) acc then
          acc
        else
          (make_exception_info e) :: acc) einfos exceptions in
  node#appendChildren
    (List.map (fun e ->
         if e#has_safety_condition then
	   let eNode = xmlElement "c-throws" in 
	   begin e#write_xml eNode ms ; eNode end
         else
	   xml_string "throws" e#get_exception#name) einfos)
         
  
let write_xmlx_constructor (node:xml_element_int) (cms:class_method_signature_int) =
  let mInfo = app#get_method cms in
  let ms = cms#method_signature in
  let libsummary:function_summary_int option =
    if function_summary_library#has_method_summary cms then
      Some (function_summary_library#get_method_summary cms)
    else
      None in
  let cInfo = app#get_class cms#class_name in
  let exceptions = mInfo#get_exceptions in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let eNode = xmlElement "exceptions" in
  let sNode = xmlElement "signature" in
  let fNode = xmlElement "summary" in
  let valid = write_xml_method_summary fNode cInfo ~libsummary mInfo in
  let argtypes =
    List.map value_type_to_string
             cms#method_signature#method_signature_data#descriptor#arguments in
  let nameString = "(" ^ (String.concat "," argtypes) ^ ")" in
  begin
    cms#method_signature#write_xmlx sNode ;
    (if mInfo#has_bytecode then seti "instrs" mInfo#get_bytecode#get_code#instr_count) ;
    write_xml_exceptions eNode ~libsummary ms exceptions ;
    (* eNode#appendChildren (List.map (fun e -> xml_string "throws" e#name) exceptions) ; *)
    append [ sNode ; eNode ; fNode ] ;
    set "access" (access_to_string mInfo#get_visibility) ;
    (if valid then () else set "valid" "no") ;
    node#setNameString nameString
  end

let write_xmlx_method (node:xml_element_int) (cms:class_method_signature_int) =
  let mInfo = app#get_method cms in
  let ms = cms#method_signature in
  let libsummary =
    if function_summary_library#has_method_summary cms then
      Some (function_summary_library#get_method_summary cms)
    else
      None in
  let cInfo = app#get_class cms#class_name in
  let exceptions = mInfo#get_exceptions in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let sety tag v = if v then set tag "yes" else () in
  let eNode = xmlElement "exceptions" in
  let sNode = xmlElement "signature" in
  let fNode = xmlElement "summary" in
  let valid = write_xml_method_summary fNode cInfo ~libsummary mInfo in
  begin
    cms#method_signature#write_xmlx sNode ;
    write_xml_exceptions eNode ~libsummary ms exceptions ;
    append [ sNode ; eNode ; fNode ] ;
    set "name" cms#method_name_string ;
    (if mInfo#has_bytecode then seti "instrs" mInfo#get_bytecode#get_code#instr_count) ;
    sety "final" mInfo#is_final ;
    sety "abstract" mInfo#is_abstract ;
    sety "static" mInfo#is_static ;
    sety "bridge" mInfo#is_bridge ;
    sety "native" mInfo#is_native ;
    set "access" (access_to_string mInfo#get_visibility) ;
    (if valid then () else set "valid" "no") ;
    node#setNameString mInfo#get_method_name
  end



let write_xmlx_inherited_method 
    (node:xml_element_int) (ms:method_signature_int) (defining_class:class_name_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sNode = xmlElement "signature" in
  begin
    ms#write_xmlx sNode ;
    append [ sNode ] ;
    set "name" ms#name ;
    set "inherited" "yes" ;
    set "from" defining_class#name ;
    node#setNameString ("(inherited) " ^ ms#name)
  end

let write_xmlx_inherited_field
      (node:xml_element_int) (fs:field_signature_int) (defining_class:class_name_int) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sNode = xmlElement "signature" in
  begin
    write_xmlx_value_type sNode fs#descriptor ;
    append [ sNode ] ;
    set "name" fs#name ;
    set "inherited" "yes" ;
    set "from" defining_class#name ;
    node#setNameString ("(inherited) field:" ^ fs#name)
  end

let write_xmlx_interface_method 
    (node:xml_element_int) (cms:class_method_signature_int) =
  let mInfo = app#get_method cms in
  let cInfo = app#get_class cms#class_name in  
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let sety key v = if v then set key "yes" else () in
  let sNode = xmlElement "signature" in
  let eNode = xmlElement "exceptions" in
  let fNode = xmlElement "summary" in
  let valid = write_xml_method_summary fNode cInfo mInfo in  
  begin
    eNode#appendChildren 
      (List.map (fun e -> xml_string "throws" e#name) mInfo#get_exceptions) ;
    (if mInfo#has_bytecode then seti "instrs" mInfo#get_bytecode#get_code#instr_count) ;    
    cms#method_signature#write_xmlx sNode ;
    append [ sNode ; eNode ; fNode ] ;
    set "name" cms#name ;
    sety "abstract" mInfo#is_abstract ;
    sety "default" (not mInfo#is_abstract) ;
    sety "static" mInfo#is_static ;
    (if valid then () else set "valid" "no") ;
    node#setNameString mInfo#get_method_name     
  end
    
    
let write_xml_summary_interface (node:xml_element_int) (cn:class_name_int) =
  let cInfo = app#get_class cn in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let mmNode = xmlElement "methods" in
  let _ = mmNode#setGroupString "METHODS" in
  let ffNode = xmlElement "fields" in
  let _ = ffNode#setGroupString "FIELDS" in
  let ssNode = xmlElement "superinterfaces" in
  let interfaces = app#get_all_interfaces cn in
  let cmss = List.map (fun ms -> make_cms cn ms) cInfo#get_methods_defined in
  let cmss = List.sort (fun cms1 cms2 -> Stdlib.compare cms1#name cms2#name)
    (List.filter (fun cms -> not (List.mem cms#name [ "<clinit>" ; "<init>" ])) cmss) in
  let _ = List.iter (fun cms -> 
    if app#has_method cms then () else
      app#add_method (cInfo#get_method cms#method_signature)) cmss in
  let cmssInherited = get_inherited_interface_methods cInfo in
  let cfss = List.map (fun fs -> make_cfs cn fs) cInfo#get_fields_defined in
  let cfss = List.filter (fun cfs ->
    let _ = if app#has_field cfs then () else
	app#add_field (cInfo#get_field cfs#field_signature) in
    let fInfo = app#get_field cfs in
    match fInfo#get_visibility with Public | Protected -> true | _ -> false) cfss in
  begin
    ssNode#appendChildren (List.map (fun cni ->
      xml_string "superinterface" cni#name) interfaces) ;
    ffNode#appendChildren (List.map (fun cfs ->
      let fNode = xmlElement "field" in
      begin write_xmlx_field fNode cfs ; fNode end) cfss) ;
    mmNode#appendChildren (List.map (fun cms ->
      let mNode = xmlElement "method" in
      begin write_xmlx_interface_method mNode cms ; mNode end) cmss) ;
    mmNode#appendChildren (List.map (fun (ms,cn) ->
      let mNode = xmlElement "method" in
      begin write_xmlx_inherited_method mNode ms cn ; mNode end) cmssInherited) ;
    append [ ssNode ; ffNode ; mmNode ; ccNode ] ;
    set "name" cn#simple_name ;
    set "package" cn#package_name ;
    set "dispatch" "yes" ;
  end

let write_xml_summary_class
    (node:xml_element_int)
    ?(all_methods=false) 
    (cn:class_name_int)
    (mloop_infos:method_loop_infos_t list) =
  let cInfo = app#get_class cn in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let sety key v = if v then set key "yes" else () in
  let mmNode = xmlElement "methods" in
  let _ = mmNode#setGroupString "METHODS" in
  let ffNode = xmlElement "fields" in
  let _ = ffNode#setGroupString "FIELDS" in
  let xxNode = xmlElement "constructors" in
  let _ = xxNode#setGroupString "CONSTRUCTORS" in
  let cmssInherited = get_inherited_methods cn in
  let cmssInherited = 
    List.sort (fun (ms1,_) (ms2,_) ->
        Stdlib.compare ms1#name ms2#name) cmssInherited in
  let cmss = List.map (fun ms -> make_cms cn ms) cInfo#get_methods_defined in
  let _ = List.iter (fun cms ->
    if app#has_method cms then () else 
      app#add_method (cInfo#get_method cms#method_signature)) cmss in
  let _ = List.iter (fun cms ->
              let mInfo = app#get_method cms in
              if mInfo#has_bytecode then
                match JCHBcPattern.get_pattern "summary" mInfo cInfo with
                | Some p -> add_pattern cms#index p
                | _ -> ()) cmss in
  let cmss = if all_methods then cmss else
      List.filter (fun cms ->
	(not (cms#name = "<clinit>")) &&
	  (let mInfo = app#get_method cms in
	   match mInfo#get_visibility with
	   | Public | Protected -> true
	   | _ -> false)) cmss in
  let (constructors,cmss) = 
    List.fold_left (fun (c,m) cms -> 
      if cms#name = "<init>" then (cms::c,m) else (c,cms::m)) ([],[]) cmss in
  let cmss =
    List.sort (fun cms1 cms2 -> Stdlib.compare cms1#name cms2#name) cmss in
  let cfss = List.map (fun fs -> make_cfs cn fs) cInfo#get_fields_defined in
  let _ =
    List.iter (fun cfs ->
        if app#has_field cfs then
          ()
        else
	  app#add_field (cInfo#get_field cfs#field_signature)) cfss in
  let cfssInherited = get_inherited_fields cn in
  let interfaces = app#get_all_interfaces cn in
  let hasSuperclass = cInfo#has_super_class && 
    (not (cInfo#get_super_class#name = "java.lang.Object")) in
  begin
    mmNode#appendChildren (List.map (fun cms ->
      let mNode = xmlElement "method" in
      begin 
	write_xmlx_method mNode cms ;
	mNode 
      end) cmss) ;
    mmNode#appendChildren (List.map (fun (ms,cn) ->
      let mNode = xmlElement "method" in
      begin write_xmlx_inherited_method mNode ms cn ; mNode end) cmssInherited) ;
    ffNode#appendChildren (List.map (fun cfs ->
      let fNode = xmlElement "field" in
      begin write_xmlx_field fNode cfs ; fNode end) cfss) ;
    ffNode#appendChildren
      (List.map (fun (fs,cn) ->
           let fNode = xmlElement "field" in
           begin write_xmlx_inherited_field fNode fs cn ; fNode end) cfssInherited) ;
    xxNode#appendChildren (List.map (fun cms ->
      let cNode = xmlElement "constructor" in
      begin 
	write_xmlx_constructor cNode cms ; 
	cNode 
      end) constructors) ;
    (match interfaces with [] -> () | _ ->
      let iiNode = xmlElement "interfaces" in
      begin 
	iiNode#appendChildren (List.map (fun i -> xml_string "implements" i#name) interfaces);
	append [ iiNode ]
      end) ;
    (if hasSuperclass then append [ xml_string "superclass" cInfo#get_super_class#name ]) ;
    append [ ffNode ; xxNode ; mmNode ; ccNode ] ;
    set "name" cn#simple_name ;
    set "package" cn#package_name ;
    sety "final" cInfo#is_final ;
    sety "abstract" cInfo#is_abstract ;
    sety "immutable" cInfo#is_immutable 
  end

let write_xml_class_or_interface_summary 
    (node:xml_element_int)
    ?(all_methods=false)
    (cn:class_name_int)
    (loop_infos:method_loop_infos_t list) =
  if (app#get_class cn)#is_interface then
    write_xml_summary_interface node cn
  else
    write_xml_summary_class node ~all_methods cn loop_infos

let save_xml_class_or_interface_summary
    ?(all_methods=true)
    (cn:class_name_int) =
  let _ = load_class_library_summary cn in
  let cInfo = app#get_class cn in
  let tag = if cInfo#is_interface then "interface" else "class" in
  let node = xmlElement tag in
  let doc = xmlDocument () in
  let root = get_jch_root tag in
  begin
    doc#setNode root ;
    root#appendChildren [ node ] ;
    write_xml_class_or_interface_summary node ~all_methods cn [];
    file_output#saveFile (cn#simple_name ^ ".xml") doc#toPretty
  end


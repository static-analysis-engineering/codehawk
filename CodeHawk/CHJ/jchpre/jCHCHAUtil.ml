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
open CHUtils
open CHPretty

(* chutil *)
open CHLogger

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHSignature

(* jchpre *)
open JCHApplication
open JCHBytecodeLocation
open JCHClassSummary
open JCHPreAPI
open JCHSystemSettings

module ClassNameCollections = CHCollections.Make (
  struct
    type t = class_name_int
    let compare n1 n2 = n1#compare n2
    let toPretty n = n#toPretty
  end)

module ClassMethodSignatureCollections = CHCollections.Make (
  struct
    type t = class_method_signature_int
    let compare cms1 cms2 = cms1#compare cms2
    let toPretty cms = cms#toPretty
  end)

module ClassFieldSignatureCollections = CHCollections.Make (
  struct
    type t = class_field_signature_int
    let compare cfs1 cfs2 = cfs1#compare cfs2
    let toPretty cfs = cfs#toPretty
  end)

let startup_classes = [ 
  "java.lang.Throwable" ;
  "java.lang.Exception" ;
  "java.lang.RuntimeException" ;
  "java.lang.ArithmeticException" ;
  "java.lang.NullPointerException" ;
  "java.lang.ArrayIndexOutOfBoundsException" ;
  "java.lang.ArrayStoreException" ;
  "java.lang.ClassCastException" ;
  "java.lang.IllegalMonitorStateException" ;
  "java.lang.NegativeArraySizeException" ;
  "java.lang.Object"  ]


let main_method_names =
  [ "main" ; "doGet" ; "doPut" ; "doPost" ; "doDelete" ; "run" ; "call" ;
    "handle" ;     (* for AbstractHttpHandler *)
    "startDocument" ;
    "endDocument" ;
    "startElement" (* for sitemap transformers *) ;
    "endElement"   (* for sitemap transformers *) ;
    "generate"     (* for sitemap generators and readers *) ;
    "match"        (* for matcher components *) ;
(*
    "process"      (* for sitemap form components *) ; 
    "service"      (* for serviceable components *) ;
    "select"       (* for selector components *) ;
    "setup"        (* for sitemap components *)
*) ]

let is_main_method (name:string) =  List.mem name main_method_names

let has_main_method (c:java_class_or_interface_int) =
  if c#is_class then
    List.exists (fun m -> is_main_method m#get_class_method_signature#method_signature#name) 
      c#get_concrete_methods 
  else
    false 

let is_valid_class_name s =
  let is_uppercase c = 
    let ascii_code = int_of_char c in
    ascii_code >= 65 && ascii_code <= 90 in
  let valid_class_name =
    Str.regexp 
      "^\\([a-zA-Z_$-][a-zA-Z_$0-9-]*\\.\\)*\\([a-zA-Z_$0-9-]+\\$\\)*[a-zA-Z_$0-9-]+$"
  in
  (Str.string_match valid_class_name s 0) &&
    (let l = ExtString.String.nsplit s "." in
     match l with 
       [] | [_] -> false 
     | _ -> 
       if List.exists (fun s -> s = "") l then 
	 false
       else
	 let pk = List.tl (List.rev l) in
	 let cn = List.hd (List.rev l) in
	 is_uppercase (cn.[0]) && List.for_all (fun n -> not (is_uppercase n.[0])) pk)

let is_sun_class_name s =
  let l = ExtString.String.nsplit s "." in
  match l with
  | "sun" :: _ -> true
  | "com" :: "sun" :: _ -> true
  | _ -> false

let is_same_package (cn1:class_name_int) (cn2:class_name_int) = 
  cn1#package_name = cn2#package_name

let is_descendant_of (junior:class_name_int) (senior:class_name_int) =
  List.exists (fun cn -> cn#equal senior) (app#get_ancestors junior)

let implements_interface (cn:class_name_int) (interface:class_name_int) =
  List.exists (fun i -> i#equal interface) (app#get_all_interfaces cn)

let rec get_class_name_from_value_type vt =
  match vt with
  | TBasic _ -> None
  | TObject (TClass cn) -> Some cn
  | TObject (TArray vts) -> get_class_name_from_value_type vts

and get_class_name_from_object_type ot =
  match ot with
  | TClass cn -> Some cn
  | TArray vt -> get_class_name_from_value_type vt

let get_class_summary_codependents (c:class_summary_int) =
  let fieldclasses =
    List.fold_left (fun acc fsig ->
        match get_class_name_from_value_type fsig#descriptor with
        | Some cn -> cn :: acc
        | _ -> acc) [] c#get_fields in
  List.concat [
      fieldclasses ;
      c#get_interfaces ;
      c#get_default_implementations ;
      (if c#has_super_class then [ c#get_super_class ] else []) ] 

let get_class_codependents (c:java_class_or_interface_int) =
  let result = c#get_interfaces in
  match c#get_super_class with Some sc -> sc :: result | _ -> result

let is_sql_interface (interface:class_name_int) =
  match interface#package with
      [ "java" ; "sql" ] 
    | "com" :: "mysql" :: _ -> true
    | _ -> false

let is_dynamic_class_loading (cms:class_method_signature_int) =
  let cn = cms#class_name in
  let ms = cms#method_signature in
  (cn#name = "java.lang.Class"  && ms#name = "forName") ||
    (cn#name = "java.lang.ClassLoader" &&
	(ms#name = "loadClass" || ms#name = "defineClass" || ms#name = "findClass" ||
	    ms#name = "findSystemClass" || ms#name = "findLoadedClass"))

let is_system_getProperty_call (cms:class_method_signature_int) =
  let cn = cms#class_name in
  let ms = cms#method_signature in
  cn#name = "java.lang.System" && ms#name = "getProperty"


let get_signature_classes ms =
  let value_types = ms#descriptor#arguments in
  let value_types = match ms#descriptor#return_value with
    | Some vt -> vt :: value_types
    | _ -> value_types in
  List.fold_left
    (fun acc vt -> match get_class_name_from_value_type vt with
    | Some cn -> cn :: acc
    | _ -> acc) [] value_types

let get_field_signature_classes (fs:field_signature_int) = 
  match get_class_name_from_value_type fs#descriptor with 
  | Some cn -> [ cn ] | _ -> []

let rec get_field_type_signature_classes (fs:field_type_signature_int) =
  match fs#kind with
    ClassType -> get_class_type_signature_classes fs#class_type
  | ArrayType -> get_type_signature_classes fs#array_type
  | TypeVariable -> new ClassNameCollections.set_t

and get_class_type_signature_classes (cs:class_type_signature_int) =
  let cnSet = new ClassNameCollections.set_t in
  let _ = List.iter (fun name -> 
    cnSet#add (make_cn ((String.concat "." cs#package) ^ "." ^ name)))
    (List.map (fun s -> 
      s#name) (cs#simple_class_type_signature :: cs#enclosing_classes)) in
  cnSet

and get_type_signature_classes (ts:type_signature_int) =
  match ts#kind with
  | BasicType -> new ClassNameCollections.set_t
  | ObjectType -> get_field_type_signature_classes ts#object_type

let get_exception_table_classes (bc:bytecode_int) =
  let cnSet = new ClassNameCollections.set_t in
  begin
    List.iter (fun h -> 
      match h#catch_type with Some cn -> cnSet#add cn | _ -> ()) bc#get_exception_table ;
    cnSet
  end

let get_local_variable_table_classes (bc:bytecode_int) =
  let cnSet = new ClassNameCollections.set_t in
  let _ = 
    match bc#get_local_variable_table with
      Some table ->
	List.iter (fun (_,_,_,ty,_) -> match get_class_name_from_value_type ty with
	  Some cn -> cnSet#add cn | _ -> ()) table 
    | _ -> () in
  cnSet

let get_local_variable_type_table_classes (bc:bytecode_int) =
  let cnSet = new ClassNameCollections.set_t in
  let _ = 
    match bc#get_local_variable_type_table with
      Some table ->
	List.iter (fun (_,_,_,ty,_) -> 
	  cnSet#addSet (get_field_type_signature_classes ty)) table
    | _ -> () in
  cnSet

let get_classes_referenced (mInfo:method_info_int) =
  let signatureclasses =
    get_signature_classes mInfo#get_class_method_signature#method_signature in
  if not mInfo#has_bytecode then
    signatureclasses
  else
    let bc = mInfo#get_bytecode in
    let cnSet = new ClassNameCollections.set_t in
    let add_value_type vt = 
      match get_class_name_from_value_type vt with 
      | Some cn -> cnSet#add cn | _ -> () in
    let add_object_type ot = 
      match get_class_name_from_object_type ot with
      | Some cn -> cnSet#add cn | _ -> () in
    begin
      mInfo#bytecode_iteri
	(fun i opc ->
	  match opc with
	  | OpNew cn -> cnSet#add cn
	  | OpGetStatic (cn,fs)
	  | OpGetField (cn,fs)
	  | OpPutStatic (cn,fs)
	  | OpPutField (cn,fs) ->
             cnSet#addList (cn :: (get_field_signature_classes fs))
	  | OpCheckCast ot
	  | OpInstanceOf ot
	  | OpAMultiNewArray (ot,_)
	  | OpClassConst ot -> add_object_type ot
	  | OpNewArray vt -> add_value_type vt
	  | OpInvokeSpecial (cn,ms)
	  | OpInvokeStatic (cn,ms)
	  | OpInvokeInterface (cn,ms)
	  | OpInvokeVirtual (TClass cn,ms) ->
	    begin cnSet#addList (cn :: (get_signature_classes ms)) end
	  | _ -> ()) ;
      cnSet#addSet (get_exception_table_classes bc) ;
      cnSet#addSet (get_local_variable_table_classes bc) ;
      cnSet#addSet (get_local_variable_type_table_classes bc);
      cnSet#addList mInfo#get_exceptions ;
      cnSet#addList signatureclasses ;
      cnSet#toList
    end
      
let get_methods_referenced (mInfo:method_info_int) =
  if not mInfo#has_bytecode then [] else
    let cmsSet = new ClassMethodSignatureCollections.set_t in
    begin
      mInfo#bytecode_iteri
	(fun i opc ->
	  match opc with
	  | OpInvokeSpecial (cn,ms)
	  | OpInvokeStatic (cn,ms)
	  | OpInvokeInterface (cn,ms)
	  | OpInvokeVirtual (TClass cn,ms) -> cmsSet#add (make_cms cn ms)
	  | OpInvokeVirtual (_,ms) ->
	    cmsSet#add (make_cms (make_cn "java.lang.Object") ms)
	  | _ -> ()) ;
      cmsSet#toList
    end
      
let get_fields_referenced (mInfo:method_info_int) =
  if not mInfo#has_bytecode then [] else
    let cfsSet = new ClassFieldSignatureCollections.set_t in
    begin
      mInfo#bytecode_iteri
	(fun i opc ->
	  match opc with
	  | OpGetStatic (cn,fs)
	  | OpPutStatic (cn,fs)
	  | OpGetField (cn,fs)
	  | OpPutField (cn,fs) -> cfsSet#add (make_cfs cn fs)
	  | _ -> ()) ;
      cfsSet#toList
    end
      
let inherits_from_final_method (cms:class_method_signature_int) =
  let ancestors = app#get_ancestors cms#class_name in
  let ms = cms#method_signature in
  List.exists (fun acn -> 
    let acms = make_cms acn ms in 
    app#has_method acms && (app#get_method acms)#is_final) ancestors
    
let rec get_value_type_classes vt = 
  match vt with 
  | TBasic _ -> []
  | TObject ot -> get_object_type_classes ot

and get_object_type_classes ot =
  match ot with 
  | TClass cn -> [ cn ] 
  | TArray vt -> get_value_type_classes vt
  
and get_element_value_classes ev = match ev with
  | EVEnum (cn,_) -> [ cn ]
  | EVClass (Some vt) -> get_value_type_classes vt
  | EVAnnotation a -> get_annotation_classes a
  | EVArray l -> List.concat (List.map get_element_value_classes l)
  | _ -> []
    
and get_constant_value_classes ev = match ev with
  | ConstClass ot -> get_object_type_classes ot
  | _ -> []
    
and get_annotation_classes a = 
  List.concat (List.map (fun (_,ev) -> 
    get_element_value_classes ev) a.element_value_pairs)
    
let get_fs_classes (fs:field_signature_int) = 
  get_value_type_classes fs#descriptor
  
let get_ms_classes (ms:method_signature_int) =
  let cnSet = new ClassNameCollections.set_t in
  let descriptor = ms#descriptor in
  begin
    List.iter (fun vt -> 
      cnSet#addList (get_value_type_classes vt)) descriptor#arguments ;
    (match descriptor#return_value with 
    | Some vt -> cnSet#addList (get_value_type_classes vt) 
    | _ -> () );
    cnSet#toList
  end			
    
let get_class_summary_classes summary =
  let cnSet = new ClassNameCollections.set_t in
  begin
    cnSet#add summary#get_class_name ;
    (if summary#has_super_class then cnSet#add summary#get_super_class) ;
    cnSet#addList summary#get_interfaces ;
    List.iter (fun ms -> cnSet#addList (get_ms_classes ms)) summary#get_methods ;
    List.iter (fun fs -> cnSet#addList (get_fs_classes fs)) summary#get_fields ;
    cnSet#toList
  end
    
let get_field_stub_classes (field:field_stub_int) =
  let cnSet = new ClassNameCollections.set_t in
  begin
    cnSet#add field#get_defining_class ;
    cnSet#add field#get_class_name ;
    cnSet#addList (get_fs_classes field#get_signature) ;
    (if field#has_value then 
	cnSet#addList (get_constant_value_classes field#get_value)) ;
    cnSet#toList
  end
    
let get_field_classes l =
  let cnSet = new ClassNameCollections.set_t in
  begin
    List.iter (fun (cfs,field) -> 
      begin 
	cnSet#add cfs#class_name ; 
	cnSet#addList (get_fs_classes cfs#field_signature)  ;
	cnSet#addList (get_field_stub_classes field)
      end) l ;
    cnSet#toList
  end
    
let get_method_stub_classes summary =
  let cnSet = new ClassNameCollections.set_t in
  begin
    cnSet#addList summary#get_exceptions ;
    (if summary#has_defining_method then 
	cnSet#add summary#get_defining_method#class_name) ;
    cnSet#toList
  end
    
let get_method_classes l =
  let cnSet = new ClassNameCollections.set_t in
  begin
    List.iter (fun (cms, _,summary) ->
      begin
	cnSet#add cms#class_name ;
	cnSet#addList (get_ms_classes cms#method_signature) ;
	cnSet#addList (get_method_stub_classes summary)
      end) l ;
    cnSet#toList
  end

let get_classes_referenced_in_summary classpath summary =
  let ((cn,class_summary), field_list, method_list) = summary in
  let cnSet = new ClassNameCollections.set_t in
  let missingSet = new StringCollections.set_t in
  let _ = cnSet#add cn in
  let _ = cnSet#addList (get_class_summary_classes class_summary) in
  let _ = cnSet#addList (get_field_classes field_list) in
  let _ = cnSet#addList (get_method_classes method_list) in
  let _ = cnSet#iter (fun cn -> 
    try ignore (JCHFile.get_class classpath cn) with 
    | JCHFile.No_class_found s -> missingSet#add s) in
  (cnSet#toList, missingSet#toList)
    
    
let get_invokeinterface_classes (target:class_name_int) (types:class_name_int list) =
  let targetClasses = target :: (app#get_class target)#get_implementing_classes in
  match types with
  | [] -> targetClasses 
  | _ ->
    if List.for_all (fun cn -> app#has_class cn) types then
      let cnSet = new ClassNameCollections.set_t in
      let (classTypes,interfaceTypes) = List.fold_left 
	(fun (c,i) cn -> 
	  let cInfo = app#get_class cn in 
	  if cInfo#is_interface then (c,cn::i) else (cn::c,i))
	([],[]) types in
      let _ = List.iter (fun cn -> 
	cnSet#addList (cn :: (app#get_class cn)#get_subclasses)) classTypes in
      let _ = List.iter (fun cn -> 
	cnSet#addList (cn :: (app#get_class cn)#get_implementing_classes))
	interfaceTypes in
      List.filter (fun cn ->
	List.exists (fun t -> cn#equal t) targetClasses) cnSet#toList
    else
      targetClasses
	
let get_invokevirtual_classes (target:class_name_int) (types:class_name_int list) =
  let targetClasses = target :: (app#get_class target)#get_subclasses in
  match types with
  | [] -> targetClasses 
  | _ ->
    if List.for_all (fun cn -> app#has_class cn) types then
      let cnSet = new ClassNameCollections.set_t in
      let (classTypes,interfaceTypes) = List.fold_left
	(fun (c,i) cn -> 
	  let cInfo = app#get_class cn in 
	  if cInfo#is_interface then (c,cn::i) else (cn::c,i))
	([],[]) types in
      let _ = List.iter (fun cn -> 
	cnSet#addList (cn :: (app#get_class cn)#get_subclasses)) classTypes in
      let _ = List.iter (fun cn -> 
	cnSet#addList (cn :: (app#get_class cn)#get_implementing_classes))
	interfaceTypes in
      let l = List.filter 
	(fun cn -> 
	  (app#get_class cn)#is_missing || 
	    List.exists (fun t -> cn#equal t) targetClasses) cnSet#toList in
      match l with
	[] -> 
	  begin
	    ch_error_log#add "target list empty" 
	      (LBLOCK [ STR "target: " ; target#toPretty ; NL ;
			INDENT (3, pretty_print_list types 
			  (fun t -> t#toPretty) "[" "; " "]") ]) ;
	    targetClasses
	  end
      | _ -> l
    else
      targetClasses
	
let get_vcall_classes (summary:function_summary_int) =
  let cnSet = new ClassNameCollections.set_t in
  begin
    List.iter (fun cms -> cnSet#add cms#class_name) summary#get_virtual_calls ;
    List.iter (fun cms -> cnSet#add cms#class_name) summary#get_interface_calls ;
    cnSet#toList
  end
    
let set_dynamically_dispatched_methods () =
  let interfaceTable = new ClassNameCollections.table_t in
  let dispatchInterfaces = List.filter (fun cInfo -> cInfo#is_dispatch) app#get_classes in
  let dispatchInterfaces = List.map (fun cInfo -> cInfo#get_class_name) dispatchInterfaces in
  List.iter (fun mInfo ->
    if mInfo#has_bytecode then
      let cn = mInfo#get_class_method_signature#class_name in
      try
	let interfaces = match interfaceTable#get cn with
	    Some s -> s#toList
	  | _ ->
	    let interfaces = app#get_all_interfaces cn in
	    let interfaces =
	      List.filter (fun i -> List.exists (fun ii -> i#equal ii) dispatchInterfaces) interfaces in
	    let s = new ClassNameCollections.set_t in
	    begin
	      s#addList interfaces ;
	      interfaceTable#set cn s ;
	      interfaces
	    end in
	if List.exists (fun ms -> ms#equal mInfo#get_class_method_signature#method_signature)
	  (List.concat (List.map (fun i -> (app#get_class i)#get_methods_defined) interfaces)) then
	  mInfo#set_dynamically_dispatched 
      with
	JCH_failure p -> 
	  ch_error_log#add "identification of dispatch" 
	    mInfo#get_class_method_signature#toPretty)
    app#get_methods
    
let set_main_method () =
  List.iter (fun mInfo ->
    if mInfo#has_bytecode then
      if is_main_method mInfo#get_class_method_signature#method_signature#name then
	begin
	  mInfo#set_main_method
	end) app#get_methods
    
    

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

(* chlib *)
open CHPretty
open CHPrettyUtil
open CHUtils

(* chutil *)
open CHLogger
open CHUtil
open CHXmlDocument

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary

(* jchpre *)
open JCHClassInfo
open JCHFieldInfo
open JCHFunctionSummaryLibrary
open JCHInstructionInfo
open JCHMethodInfo
open JCHPreAPI
open JCHSystemSettings
open JCHXmlUtil


let prd p = if (get_verbose ()) then pr_debug p else ()

let jdk_package_prefixes =  [ "java" ; "javax" ; "org.w3c.dom" ; "org.xml.sax" ]
let non_jdk_packages = [ "javax.mail" ; "javax.media" ]


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

module MethodInfoCollections = CHCollections.Make (
  struct
    type t = method_info_int
    let compare m1 m2 = Stdlib.compare m1#get_index m2#get_index
    let toPretty m = m#toPretty
  end)

module FieldInfoCollections = CHCollections.Make (
  struct
    type t = field_info_int
    let compare f1 f2 = f1#get_class_signature#compare f2#get_class_signature
    let toPretty f = f#toPretty
  end)

module ClassFieldSignatureCollections = CHCollections.Make (
  struct
    type t = class_field_signature_int
    let compare cfs1 cfs2 = cfs1#compare cfs2
    let toPretty cfs = cfs#toPretty
  end)

module BytecodeLocationCollections = CHCollections.Make (
  struct
    type t = bytecode_location_int
    let compare l1 l2 = l1#compare l2
    let toPretty l = l#toPretty
  end)

class application_t:application_int =
object (self)

  val classes = new ClassNameCollections.table_t
  val methods = new ClassMethodSignatureCollections.table_t
  val fields  = new ClassFieldSignatureCollections.table_t
  val instructions = new BytecodeLocationCollections.table_t
  val mutable method_list = []
  val mutable application_jars = []

  method reset = 
    begin
      classes#removeList classes#listOfKeys ;
      methods#removeList methods#listOfKeys ;
      fields#removeList fields#listOfKeys ;
      instructions#removeList instructions#listOfKeys ;
      method_list <- [] ;
      application_jars <- []
    end

  method add_application_jar jar = application_jars <- jar :: application_jars

  method get_application_jars = application_jars

  method get_num_classes = classes#size

  method get_num_methods = methods#size

  method add_class (c:java_class_or_interface_int) =
    if system_settings#is_excluded_class c#get_name#index then () else
      classes#set c#get_name (make_class_info c)
      
  method replace_class (c:java_class_or_interface_int) =
    let _ = prd [ STR "Replace class " ; c#get_name#toPretty ; 
		  STR " (" ; INT c#get_name#index ; STR ")" ; NL ] in
    let oldInfo = self#get_class c#get_name in
    let cInfo = make_class_info c in
    begin
      (if oldInfo#is_dispatch then cInfo#set_dispatch) ;
      List.iter cInfo#add_creator oldInfo#get_creators ;
      List.iter cInfo#add_subclass oldInfo#get_subclasses ;
      (if cInfo#is_interface then 
	  List.iter cInfo#add_implementing_class oldInfo#get_implementing_classes) ;
      classes#remove c#get_name ;
      classes#set c#get_name cInfo ;
      if cInfo#has_super_class && not (self#has_class cInfo#get_super_class) then
	begin
	  ch_error_log#add "class summary" 
	    (LBLOCK [ STR "Super class " ; cInfo#get_super_class#toPretty ; STR " of " ;
		      c#get_name#toPretty ; STR " not in app" ]) ;
	  raise (JCH_failure (LBLOCK [ STR "Super class of " ; 
				       cInfo#get_super_class#toPretty ; STR " of " ;
				       c#get_name#toPretty ; STR " not in app" ]))
	end
    end
      
  method add_missing_class (cn:class_name_int) =
    let _ = prd [ STR "Add missing class " ; cn#toPretty ; STR " (" ; 
		  INT cn#index ; STR ")" ; NL ] in
    classes#set cn (make_missing_class_info cn)
      
  method add_class_stub (c:class_info_int) =
    let _ = prd [ STR "Add class stub " ; c#get_class_name#toPretty ; 
		  STR " (" ; INT c#get_class_name#index ; STR ")" ; NL ] in
    classes#set c#get_class_name c
      
  method add_method (m:method_int) = 
    let cms = m#get_class_method_signature in
    if methods#has cms then () else
      methods#set cms (make_method_info m) 
      
  method add_method_link 
    (cms:class_method_signature_int) (dst_cms:class_method_signature_int) =
    let _ = prd [ STR "Add method link " ; cms#toPretty ; STR " to " ; 
		  dst_cms#toPretty ; NL ] in
    methods#set cms (self#get_method dst_cms)

  method add_missing_method (cms:class_method_signature_int) =
    let _ = method_list <- [] in
    let _ = prd [ STR "Add missing method " ; cms#toPretty ; NL ] in
    methods#set cms (make_missing_method_info cms)

  method add_interface_inherited_method (cms:class_method_signature_int) =
    let _ = prd [ STR "Add interface-inherited method " ; cms#toPretty ; NL ] in
    methods#set cms (make_interface_inherited_method_info cms)

  method add_stub (x:function_summary_int) =
    let _ = method_list <- [] in
    let _ = prd [ STR "Add method stub " ; x#get_cms#toPretty ; NL ] in
    methods#set x#get_cms (make_method_stub_info x)

  method add_field (f:field_int) =
    let _ =
      prd [ STR "Add field " ; f#get_class_signature#toPretty ;
            STR " (" ; INT f#get_class_signature#index ; STR ")" ; NL ] in
    let class_name = f#get_class_signature#class_name in
    let has_summary = function_summary_library#has_class_summary class_name in
    fields#set f#get_class_signature (make_field_info has_summary f)

  method add_field_stub (f:field_stub_int) =
    let _ =
      prd [ STR "Add field stub " ; f#get_class_signature#toPretty ;
            STR " (" ; INT f#get_class_signature#index ; STR ")" ; NL ] in
    fields#set f#get_class_signature (make_field_stub_info f)

  method add_field_link (cfs:class_field_signature_int) (dst_cfs:class_field_signature_int) =
    let _ =
      prd [ STR "Add field link " ; cfs#toPretty ;
            STR " ("; INT cfs#index ; STR ") to " ; dst_cfs#toPretty ;
            STR " (" ; INT dst_cfs#index ; STR ")" ; NL ] in
    fields#set cfs (self#get_field dst_cfs)

  method add_missing_field (cfs:class_field_signature_int) =
    let _ = prd [ STR "Add missing field " ; cfs#toPretty ; NL ] in
    fields#set cfs (make_missing_field_info cfs)

  method add_instruction (instr:instruction_info_int) =
    instructions#set instr#get_location instr

  method get_class (cn:class_name_int) =
    match classes#get cn with Some c -> c | _ ->
     raise (JCH_failure (LBLOCK [ STR "No class found with name " ; cn#toPretty]))
				
  method get_derived_classes (cn:class_name_int) =
    let all_classes = classes#listOfValues in
    let result = new ClassNameCollections.set_t in
    let rec aux c =
      let subclasses = List.filter 
	(fun cc -> cc#has_super_class && cc#get_super_class#equal c#get_class_name) all_classes in
      begin
	List.iter (fun c -> result#add c#get_class_name) subclasses ;
	List.iter aux subclasses
      end in
    begin
      aux (self#get_class cn) ;
      result#toList
    end

  method is_inherited (cms:class_method_signature_int) =
    if self#has_method cms then
      not (cms#equal (self#get_method cms)#get_class_method_signature)
    else
      false

  method is_descendant (cn1:class_name_int) (cn2:class_name_int) =
    if self#has_class cn1 then
      let c1Info = self#get_class cn1 in
      if c1Info#has_super_class then
	let scn = c1Info#get_super_class in
	scn#equal cn2 || self#is_descendant scn cn2
      else
	false
    else
      begin
	raise_jch_failure
          (LBLOCK [ STR "Class " ; cn1#toPretty ; 
		    STR " has not been loaded; cannot determine descendancy" ]) ;
	false
      end


  (* methods that inherit their implementation from a super class *)
  method get_inherited_methods = 
    List.map
      (fun (cms,_) -> cms)
      (List.filter (fun (cms,m) ->
           not (cms#equal m#get_class_method_signature)) methods#listOfPairs)

  method implements_interface (cInfo:class_info_int) (cni:class_name_int) =
    ((not cInfo#is_interface) && cInfo#implements_interface cni) ||
      (cInfo#has_super_class &&
	 self#implements_interface (self#get_class (cInfo#get_super_class)) cni)

  method get_implementing_classes (cni:class_name_int) =
    if self#has_class cni then
      let iInfo = self#get_class cni in
      if iInfo#is_interface then
	List.filter (fun cn -> self#implements_interface cn cni) self#get_classes
      else
	raise (JCH_failure 
		 (LBLOCK [ STR "get-implementing-classes: " ; 
			   cni#toPretty ; STR " is not an interface" ]))
    else
      raise (JCH_failure 
	       (LBLOCK [ STR "get-implementing-classes: " ; 
			 cni#toPretty ; STR " not found"]))

  method get_ancestors (cn:class_name_int) =
    let obj = common_dictionary#make_class_name "java.lang.Object" in
    let rec aux (sc:class_name_int) =
      if self#has_class sc then
	let cInfo = self#get_class sc in
	if cInfo#has_super_class then
	  sc :: (aux cInfo#get_super_class)
	else
	  [ sc ]
      else
	begin
	  ch_error_log#add "class not in app" (LBLOCK [ STR "get_ancestors: " ; sc#toPretty]) ;
	  [ obj ]
	end in
    if self#has_class cn then
      let cInfo = self#get_class cn in
      if cInfo#has_super_class then aux cInfo#get_super_class else []
    else
      [ obj ]

  method get_subclasses (cn:class_name_int) =
    let result = ref [] in
    let _ = classes#iter (fun c _ -> 
      if List.exists (fun a -> a#equal cn) (self#get_ancestors c) then
				result := c :: !result) in
    !result

  method get_all_interfaces (cn:class_name_int) =
    let union l1 l2 = list_union_f l1 l2 (fun c1 c2 -> c1#equal c2) in
    if self#has_class cn then
      let cInfo = self#get_class cn in
      let superInterfaces = if cInfo#has_super_class then 
	  self#get_all_interfaces cInfo#get_super_class
	else
	  [] in
      let interfaces = union cInfo#get_interfaces superInterfaces in
      let rec aux wl completed result =
	match wl with
	  [] -> result
	| h::tl -> if self#has_class h then
	    let interfaces = (self#get_class h)#get_interfaces in
	    let newResult = union result interfaces in
	    let newCompleted = h :: completed in
	    let newIntf = List.filter (fun cn -> 
	      not (List.exists (fun cmp -> cn#equal cmp) newCompleted)) interfaces in
	    let newWl = union tl newIntf in
	    aux newWl newCompleted newResult
	  else
	    begin
	      ch_error_log#add "get all interfaces" 
		(LBLOCK [ STR "Class " ; h#toPretty ; STR " not found" ]) ;
	      aux tl completed result
	    end in
      aux interfaces [] interfaces
    else
      begin
	ch_error_log#add "get all interfaces" 
	  (LBLOCK [ STR "Class " ; cn#toPretty ; STR " not found" ]) ;
	[]
      end
				          
  method private get_ancestor_classes (cn:class_name_int) =
    let c = self#get_class cn in
    if c#has_super_class then
      let sc = c#get_super_class in sc :: (self#get_ancestor_classes sc)
    else
      []

  method get_method (cms:class_method_signature_int) =
    match methods#get cms with Some m -> m | _ ->
      raise (JCH_failure (LBLOCK [ STR "No method found with name " ; cms#toPretty]))

  method get_method_by_index (index:int) = self#get_method (retrieve_cms index)

  method get_field (cfs:class_field_signature_int) =
    match fields#get cfs with Some f -> f | _ ->
      raise (JCH_failure (LBLOCK [ STR "No field found with name " ; cfs#toPretty]))

  method get_instruction (bcloc:bytecode_location_int) =
    match instructions#get bcloc with Some i -> i | _ ->
      let cms = bcloc#get_class_method_signature in
      let pc = bcloc#get_pc in
      let is_modified = bcloc#is_modified in
      let mInfo = if self#has_method cms then self#get_method cms else
	  raise (JCH_failure (LBLOCK [ STR "Request for instruction from nonexisting method: " ;
				       cms#toPretty ])) in
      let bc = if mInfo#has_bytecode then mInfo#get_bytecode else
	  raise (JCH_failure (LBLOCK [ STR "Method " ; cms#toPretty ;
				       STR " does not have byte code" ])) in
      let opc = bc#get_code#at pc in
      let instr = make_instruction_info bcloc ~is_modified opc in
      begin
	instructions#set bcloc instr ;
	instr
      end

  method get_packages =
    let packages = new StringCollections.set_t in
    begin
      List.iter (fun c -> packages#add c#get_class_name#package_name) self#get_classes ;
      packages#toList
    end

  method get_classes = classes#listOfValues

  method get_application_classes =
    List.filter (fun cInfo -> 
      self#is_application_class cInfo#get_class_name) self#get_classes

  method iter_classes f = List.iter f classes#listOfValues

  method iter_methods f = List.iter f self#get_methods

  method iter_fields f = List.iter f self#get_fields

  method get_instructions = instructions#listOfValues

  method get_methods = 
    match method_list with
      [] ->
	let methods_set = new MethodInfoCollections.set_t in
	let _ = methods_set#addList methods#listOfValues in
	let _ = method_list <- methods_set#toList in
	method_list
    | _ -> method_list

  method get_stubbed_methods =
    match method_list with
      [] ->
	let methods_set = new MethodInfoCollections.set_t in
	let _ = methods_set#addList 
	  (List.filter (fun m -> m#is_stubbed) methods#listOfValues) in
	methods_set#toList
    | _ -> List.filter (fun m -> m#is_stubbed) method_list

  method get_fields = 
    let fields_set = new FieldInfoCollections.set_t in
    begin
      fields_set#addList fields#listOfValues ;
      fields_set#toList
    end

  method has_class (cn:class_name_int) =
    match classes#get cn with Some _ -> true | _ -> false

  method has_method (cms:class_method_signature_int) =
    match methods#get cms with Some _ -> true | _ -> false

  method has_field (cfs:class_field_signature_int) =
    match fields#get cfs with Some _ -> true | _ -> false

  method has_instruction (bcloc:bytecode_location_int) =
    match instructions#get bcloc with Some _ -> true | _ -> false

  method is_interface (cn:class_name_int) = (self#get_class cn)#is_interface

  method is_abstract_class (cn:class_name_int) = (self#get_class cn)#is_abstract

  method is_application_class (cn:class_name_int) =
    self#has_class cn
    && (List.mem (self#get_class cn)#get_source_origin application_jars)

  method is_application_method (cms:class_method_signature_int) =
    self#is_application_class cms#class_name

  method write_xml_missing_items (node:xml_element_int) =
    let missingclasses = ref [] in
    let missingmethods = ref [] in
    let missingfields = ref []  in
    let _ =
      self#iter_classes (fun cInfo -> 
          if cInfo#is_missing then
            missingclasses := cInfo#get_class_name :: !missingclasses) in
    let missingclasses =
      List.sort (fun c1 c2 -> Stdlib.compare c1#name c2#name) !missingclasses in
    let _ =
      self#iter_methods (fun mInfo ->
          if mInfo#is_missing then
            missingmethods :=
              mInfo#get_class_method_signature :: !missingmethods) in
    let missingmethods =
      List.sort (fun m1 m2 ->
          Stdlib.compare m1#class_method_signature_string
                    m2#class_method_signature_string) !missingmethods in
    let _ =
      self#iter_fields (fun fInfo ->
          if fInfo#is_missing then
            missingfields :=
              fInfo#get_class_signature :: !missingfields) in
    let missingfields =
      List.sort (fun f1 f2 ->
          Stdlib.compare f1#to_string f2#to_string) !missingfields in

    let ccNode = xmlElement "missing-classes" in
    let mmNode = xmlElement "missing-methods" in
    let ffNode = xmlElement "missing-fields" in
    begin
      ccNode#appendChildren
        (List.map (fun cn ->
	     let cNode = xmlElement "cn" in
	     begin
               cNode#setAttribute "name" cn#name ;
               cNode#setIntAttribute "ix" cn#index ;
               cNode
             end) missingclasses) ;
      mmNode#appendChildren
        (List.map (fun m ->
             let mNode = xmlElement "method" in
             begin
               mNode#setAttribute "name" m#class_method_signature_string ;
               mNode#setIntAttribute "ix" m#index ;
               mNode
             end) missingmethods) ;
      ffNode#appendChildren
        (List.map (fun f ->
             let fNode = xmlElement "field" in
             begin
               fNode#setAttribute "name" f#to_string ;
               fNode#setIntAttribute "ix" f#index ;
               fNode
             end) missingfields) ;
      node#appendChildren [ ccNode ; mmNode ; ffNode ]
    end

end
  
let app = new application_t
  

let bytecode_to_pretty () =
  let methods = List.filter (fun m -> m#has_bytecode) app#get_methods in
  let p = ref [] in
  begin
    List.iter (fun m -> p := (LBLOCK [ m#bytecode_to_pretty ; NL ; NL ]) :: !p) methods ;
    LBLOCK !p
  end
    
let class_bytecode_to_pretty (cn:class_name_int) =
  let methods = List.filter (fun m ->
    m#get_class_method_signature#class_name#equal cn && m#has_bytecode) app#get_methods in
  let p = ref [] in
  begin
    List.iter (fun m -> p := (LBLOCK [ m#bytecode_to_pretty ; NL ; NL ]) :: !p) methods ;
    LBLOCK !p
  end

module MethodSignatureCollections = CHCollections.Make (
  struct
    type t = method_signature_int
    let compare ms1 ms2 = ms1#compare ms2
    let toPretty ms = ms#toPretty
  end)
        
let get_inherited_methods (cn:class_name_int) =
  let is_inherited v = match v with Public | Protected -> true | _ -> false in
  let inheritedMethods = new MethodSignatureCollections.table_t in
  let definedMethods = new MethodSignatureCollections.set_t in
  let cInfo = ref (app#get_class cn) in
  let _ = List.iter definedMethods#add !cInfo#get_methods_defined in
  begin
    while !cInfo#has_super_class do 
      let sc = !cInfo#get_super_class in
      let _ = cInfo := app#get_class sc in
      let scDefined = !cInfo#get_methods_defined in
      let scDefined = 
	List.filter (fun ms -> 
	    not (List.mem ms#name [ "<clinit>" ; "<init>" ])) scDefined in
      begin
        List.iter (fun ms ->
	    if !cInfo#has_method ms then
	      let m = !cInfo#get_method ms in
	      if is_inherited m#get_visibility then
	        if definedMethods#has ms || inheritedMethods#has ms then () else
	          inheritedMethods#set ms sc
	      else
	        ()
	    else
	      let scms = make_cms sc ms in
	      if function_summary_library#has_method_summary scms then
	        let summary = function_summary_library#get_method_summary scms in
	        if definedMethods#has ms || inheritedMethods#has ms || summary#is_inherited then () else
                  inheritedMethods#set ms sc) scDefined ;
        List.iter (fun interface ->
            let iclass = app#get_class interface in
            let iDefined = iclass#get_interface_default_methods in
            List.iter (fun ms ->
                if definedMethods#has ms || inheritedMethods#has ms then () else
                  inheritedMethods#set ms iclass#get_class_name) iDefined)
                  !cInfo#get_interfaces
      end
    done ;
    inheritedMethods#listOfPairs
  end

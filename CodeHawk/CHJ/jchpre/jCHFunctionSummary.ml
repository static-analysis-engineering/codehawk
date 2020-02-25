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
open CHNumerical

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm

(* jchpre *)
open JCHPreAPI
open JCHSystemSettings
open JCHXmlUtil

module P = Pervasives

let p2s = string_printer#print

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end
        
let precondition_predicate_to_pretty p =
  match p with
  | PreRelationalExpr r -> relational_expr_to_pretty r
  | PreNull t -> LBLOCK [ STR "null (" ; jterm_to_pretty t ; STR ")" ]
  | PreNotNull t -> 
    LBLOCK [ STR "not-null (" ; jterm_to_pretty t ; STR ")" ]
  | PreValidString (t,s) -> 
    LBLOCK [ STR "valid (" ; jterm_to_pretty t ; STR "): " ; STR s ]
    
let precondition_predicate_to_xml 
    (pre:precondition_predicate_t) (ms:method_signature_int) =
  let txml t = jterm_to_xmlx t ms in
  let apply_term tag t = 
    let node = xmlElement "apply" in	
    begin node#appendChildren [ xmlElement tag ; txml t ] ; node end in
  match pre with
  | PreRelationalExpr (op,t1,t2) ->
    let node = xmlElement "apply" in
    begin 
      node#appendChildren 
	[ xmlElement (relational_op_to_xml_string op) ; txml t1 ; txml t2 ] ; 
      node 
    end
  | PreNull t -> apply_term "null" t
  | PreNotNull t -> apply_term "not-null" t
  | PreValidString (t,s) ->
    let node = xmlElement "apply" in
    let snode = xmlElement "valid" in
    begin
      snode#setAttribute "format" s ;
      node#appendChildren [ snode ; txml t ] ;
      node
    end
     	
class postcondition_t 
  (name:string) 
  (is_error:bool)
  (predicate:postcondition_predicate_t):postcondition_int =
object (self)
  
  method get_name = name
  method get_predicate = predicate
  method is_error = is_error
          
  method private write_xml_post_predicate 
    (node:xml_element_int) (ms:method_signature_int)  =
    let txml t = jterm_to_xmlx t ms in
    let apply_term tag t = 
      let aNode = xmlElement "apply" in	
      begin aNode#appendChildren [ xmlElement tag ; txml t ] ; aNode end in
    let mNode = xmlElement "math" in
    let addchild n = mNode#appendChildren [ n ] in
    let _ =
      match predicate with
      | PostRelationalExpr r -> write_xmlx_relational_expr mNode ms r
      | PostTrue -> addchild (xmlElement "true")
      | PostFalse -> addchild (xmlElement "false")
      | PostNewObject cn ->
	let aNode = xmlElement "apply" in
	begin 
	  aNode#appendChildren 
	    [ xmlElement "new-object" ; xml_string "object" cn#name ] ; 
	  addchild aNode
	end
      | PostObjectClass cn ->
         let aNode = xmlElement "apply" in
         begin
           aNode#appendChildren
             [ xmlElement "object-class" ;  xml_string "object" cn#name ] ;
           addchild aNode
         end
      | PostNull -> addchild (xmlElement "null")
      | PostNotNull -> addchild (xmlElement "not-null")
      | PostElement t -> addchild (apply_term "element" t)
      | PostEmptyCollection -> addchild (xmlElement "empty-collection")
      | PostSameCollection t -> addchild (apply_term "same-collection" t)
      | PostWrapped t -> addchild (apply_term "wrapped" t)
      | PostUnwrapped -> addchild (xmlElement "unwrapped")
      | PostValidString s -> 
	let aNode = xmlElement "valid" in 
	begin aNode#setAttribute "format" s ; addchild aNode end in
      node#appendChildren [ mNode ] 
      
  method write_xml (node:xml_element_int) (ms:method_signature_int) =
    begin
      self#write_xml_post_predicate node ms ;
      (if name = "none" then () else node#setAttribute "name" name)
    end
            
  method toPretty =
    match predicate with
    | PostRelationalExpr r -> relational_expr_to_pretty r
    | PostTrue -> STR "true"
    | PostFalse -> STR "false"
    | PostNewObject cn -> LBLOCK [ STR "new " ; cn#toPretty ]
    | PostObjectClass cn -> LBLOCK [ STR "object class" ; cn#toPretty ]
    | PostNull -> LBLOCK [ STR "null" ]
    | PostNotNull -> LBLOCK [ STR "not null" ]
    | PostElement t -> 
      LBLOCK [ STR "element (" ; jterm_to_pretty t ; STR ")" ]
    | PostEmptyCollection -> LBLOCK [ STR "empty collection" ]
    | PostSameCollection t -> 
      LBLOCK [ STR "same collection (" ; jterm_to_pretty t ; STR ")" ]
    | PostWrapped t -> LBLOCK [ STR "wrapped (" ; jterm_to_pretty t ; STR ")"  ]
    | PostUnwrapped -> LBLOCK [ STR "unwrapped" ]
    | PostValidString s -> LBLOCK [ STR "valid " ; STR s ]
      
end
  
let make_postcondition ?(name="none") 
    (is_error:bool) (predicate:postcondition_predicate_t) =
  new postcondition_t name is_error predicate
        
let rec sideeffect_to_pretty sideeffect =
  match sideeffect with
  | NumericJoin (t1,t2,t3) -> 
      LBLOCK [ STR "NumericJoin (" ; jterm_to_pretty t1; STR "," ; 
	       jterm_to_pretty t2 ; STR ", " ; jterm_to_pretty t3 ; STR ")" ]
  | NumericAbstract t -> 
    LBLOCK [ STR "NumericAbstract (" ; jterm_to_pretty t ; STR ")" ]
  | SetValue t -> LBLOCK [ STR "SetValue (" ; jterm_to_pretty t ; STR ")" ]
  | Wrap (t1,t2) ->
    LBLOCK [ STR "Wrap (" ; jterm_to_pretty t1 ; STR "," ; 
	     jterm_to_pretty t2 ; STR ")" ]
  | ConditionalSideEffect (pre, sideeffect) ->
    LBLOCK [ STR "if " ; precondition_predicate_to_pretty pre ; STR " then " ; 
	     sideeffect_to_pretty sideeffect ]

let write_xml_sideeffect 
    (node:xml_element_int) (s:sideeffect_t) (ms:method_signature_int) =
  let txml t = jterm_to_xmlx t ms in
  let mNode = xmlElement "math" in
  let apply_term tag terms =
    let anode = xmlElement "apply" in	
    begin 
      anode#appendChildren ((xmlElement tag) :: (List.map txml terms)) ; 
      anode 
    end in
  let rec aux s =
    match s with
    | NumericJoin (t1,t2,t3) -> apply_term "numeric-join" [ t1 ; t2 ; t3 ] 
    | NumericAbstract t -> apply_term "numeric-abstract" [ t ] 
    | SetValue t -> apply_term "set-value" [ t ] 
    | Wrap (t1,t2) -> apply_term "wrap" [ t1 ; t2  ] 
    | ConditionalSideEffect (pre,cse) ->
      let anode = xmlElement "apply" in
      begin 
	anode#appendChildren [ 
	  xmlElement "implies" ; 
	  precondition_predicate_to_xml pre ms ; 
	  aux cse ] ;
	node
      end in
  let _ = mNode#appendChildren [ aux s ] in
  node#appendChildren [ mNode ]
    
    
let taint_element_compare t1 t2 =
  match (t1,t2) with
    (TTransfer (x1,x2), TTransfer (y1,y2)) ->
      let l1 = jterm_compare x1 y1 in
      if l1 = 0 then
	jterm_compare x2 y2
      else l1
  | (TTransfer _, _) -> -1
  | (_, TTransfer _) -> 1
  | (TRefEqual (x1,x2), TRefEqual (y1,y2)) ->
     let l1 = jterm_compare x1 y1 in
     if l1 = 0 then
       jterm_compare x2 y2
     else
       l1
  | (TRefEqual _, _) -> -1
  | (_, TRefEqual _) -> 1
  | (TDefPut x, TDefPut y) -> jterm_compare x y
  | (TDefPut _, _) -> -1
  | (_, TDefPut _) -> 1
  | (TRemove x, TRemove y) -> jterm_compare x y
    
let taint_element_to_pretty taint_element =
  match taint_element with
  | TTransfer (t1,t2) -> 
     LBLOCK [ jterm_to_pretty t1 ; STR " -> " ; jterm_to_pretty t2 ]
  | TRefEqual (t1,t2) ->
      LBLOCK [ jterm_to_pretty t1 ; STR " == " ; jterm_to_pretty t2 ]
  | TDefPut t -> LBLOCK [ STR "defput " ; jterm_to_pretty t ]
  | TRemove t -> LBLOCK [ STR "remove " ; jterm_to_pretty t ]
    
let taint_element_to_xml (e:taint_element_t) (ms:method_signature_int) =
  let txml t = jterm_to_xmlx t ms in
  let apply_term tag t = 
    let node = xmlElement tag in 
    begin node#appendChildren [ txml t ] ; node end in
  match e with
  | TTransfer (t1,t2) -> 
    let node = xmlElement "transfer" in	
    begin node#appendChildren [ txml t1 ; txml t2 ] ; node end
  | TRefEqual (t1,t2) ->
     let node = xmlElement "refeq" in
     begin node#appendChildren [ txml t1 ; txml t2 ] ; node end
  | TDefPut t -> apply_term "defput" t
  | TRemove t -> apply_term "remove" t

let get_taint_element_class_dependencies (t:taint_element_t) =
  match t with
  | TTransfer (t1,t2) 
    | TRefEqual (t1,t2) ->
     (get_jterm_class_dependencies t1) @ (get_jterm_class_dependencies t2)
  | TDefPut t | TRemove t -> get_jterm_class_dependencies t
    
	
class taint_t (taint_elements:taint_element_t list):taint_int =
object (self:'a)
  
  val mutable taint_elements = taint_elements

  method add_taint (t:'a) =
    List.iter self#add_element t#get_elements
    
  method add_element (element:taint_element_t) =
    if List.exists (fun e -> 
      (taint_element_compare e element) = 0) taint_elements then
      () 
    else 
      taint_elements <- element :: taint_elements
	
  method get_elements = taint_elements

  method write_xml (node:xml_element_int) (ms:method_signature_int) =
    node#appendChildren (List.map (fun e -> 
      taint_element_to_xml e ms) taint_elements) 
      
  method toPretty = pretty_print_list taint_elements 
    (fun e -> LBLOCK [ taint_element_to_pretty e ; NL ]) "" "" ""
end
  
 	
class string_sink_t (arg:int) (form:string) (dest:string):string_sink_int =
object (self)
  method get_arg = arg
  method get_form = form
  method get_dest = dest
    
  method write_xml (node:xml_element_int) (ms:method_signature_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let arg = if ms#is_static then self#get_arg+1 else self#get_arg in
    begin 
      seti "arg" arg ;
      set "form" self#get_form ;
      set "dest" self#get_dest ;
    end
      
  method toPretty = 
    LBLOCK [ STR "arg" ; INT arg ; STR ": " ; STR form ; STR " --- " ; STR dest ; NL ]
end
      
let resource_type_to_string r =
  match r with
  | RMemory -> "memory"
  | RWaitingTime -> "waiting-time"
  | RThreads -> "threads"
  | RFileSize -> "file-size"
    
	
class resource_sink_t (arg:int) (rtype:resource_type_t):resource_sink_int =
object (self)
  method get_arg = arg
  method get_type = rtype
    
  method write_xml (node:xml_element_int) (ms:method_signature_int) =
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let arg = if ms#is_static then self#get_arg + 1 else self#get_arg in
    begin
      seti "arg" arg ;
      set "form" (resource_type_to_string self#get_type) ;
    end
      
  method toPretty = 
    LBLOCK [ STR "arg" ; INT arg ; STR ": " ; STR (resource_type_to_string self#get_type) ;
	     NL ]
      
end
  
  
let make_taint = new taint_t 
    
let make_string_sink = new string_sink_t
  
let make_resource_sink = new resource_sink_t 
  

class exception_info_t 
  ?(safe=[]) 
  ?(unsafe=[]) 
  ?(descr="") 
  (exn:class_name_int):exception_info_int =
object (self)
  method get_exception = exn
  method get_safety_condition = safe
  method get_error_condition = unsafe
  method get_description = descr
    
  method has_safety_condition = match safe with [] -> false | _ -> true
  method has_error_condition = match unsafe with [] -> false | _ -> true
  method has_description = not (descr="")
          
  method private write_xml_exception (node:xml_element_int) (ms:method_signature_int) =
    let append = node#appendChildren in
    let add_descr (n:xml_element_int) = 
      if descr="" then () else n#setAttribute "descr" descr in
    let pre_to_xml tag pre = 
      let node = xmlElement tag in
      let mNode = xmlElement "math" in
      begin 
	node#appendChildren [ mNode ] ;
	mNode#appendChildren [ precondition_predicate_to_xml pre ms ] ;
	node
      end in
    match (safe,unsafe) with
      ([],[]) -> let node = xml_string "throws" exn#name in add_descr node
    | _ ->
      let exnNode = xml_string "exn" exn#name in
      begin
	append (List.map (fun p -> pre_to_xml "safety-condition" p) safe) ;
	append (List.map (fun p -> pre_to_xml "error-condition" p) unsafe) ;
	append [ exnNode ] ;
	add_descr node ;
      end
	
  method write_xml (node:xml_element_int) (ms:method_signature_int) =
    self#write_xml_exception node ms
      
  method toPretty =
    let pSafe = if self#has_safety_condition then
	LBLOCK [ STR "safe if: " ; 
		 pretty_print_list safe precondition_predicate_to_pretty "" " and " "" ; NL ]
      else
	STR "" in
    let pUnsafe = if self#has_error_condition then
	LBLOCK [ STR "thrown if: " ; 
		 pretty_print_list unsafe precondition_predicate_to_pretty "" " or " "" ; NL ]
      else
	STR "" in
    let pDescr = if self#has_description then	LBLOCK [ STR descr ; NL ] else STR "" in
    LBLOCK [ exn#toPretty ; NL ; INDENT (3, LBLOCK [ pDescr ; pSafe ; pUnsafe ]) ]
end
  
let make_exception_info ?(safe=[]) ?(unsafe=[]) ?(descr="") (exn:class_name_int) =
  new exception_info_t ~safe ~unsafe ~descr exn
    
let no_taint_info = new taint_t []

let write_xml_call (node:xml_element_int) (cms:class_method_signature_int) =
  node#setIntAttribute "cmsix" cms#index

class function_summary_t 
  ~(cms:class_method_signature_int) 
  ~(visibility:access_t) 
  ~(is_static:bool) 
  ~(is_final:bool) 
  ~(is_bridge:bool)
  ~(is_abstract:bool) 
  ~(is_inherited:bool)
  ~(is_default:bool)
  ~(is_valid:bool)
  ~(defining_method:class_method_signature_int option)
  ~(exception_infos:exception_info_int list)
  ~(post:postcondition_int list)  
  ~(sideeffects:sideeffect_t list)
  ~(taint:taint_int)
  ~(virtual_calls:class_method_signature_int list)
  ~(interface_calls:class_method_signature_int list)
  ~(resource_sinks:resource_sink_int list) 
  ~(string_sinks:string_sink_int list)
  ~(pattern:bc_action_t option)
  ~(time_cost:jterm_range_int)
  ~(space_cost:jterm_range_int):function_summary_int =
object (self)
  
  method is_abstract = is_abstract
  method is_final = is_final
  method is_static = is_static
  method is_bridge = is_bridge
  method is_inherited = is_inherited
  method is_default = is_default
  method is_valid = is_valid
  method has_pattern = match pattern with Some _ -> true | _ -> false
  method get_post = List.filter (fun p -> not p#is_error) post
  method get_error_post = List.filter (fun p -> p#is_error) post
  method get_sideeffects = sideeffects
  method get_exceptions = List.map (fun eInfo -> eInfo#get_exception) exception_infos
  method get_exception_infos = exception_infos
  method get_cms = cms
  method get_method_signature = cms#method_signature
  method get_visibility = visibility
  method get_taint = taint
  method get_taint_elements = taint#get_elements
  method get_virtual_calls = virtual_calls
  method get_interface_calls = interface_calls
  method get_string_sinks = string_sinks
  method get_resource_sinks = resource_sinks
  method get_time_cost = time_cost
  method get_space_cost = space_cost
  method get_pattern =
    match pattern with
    | Some p -> p
    | _ -> raise (JCH_failure (LBLOCK [ STR "Function summary does not have a pattern" ]))

  method get_string_sink (index:int) = 
    try 
      List.find (fun s -> s#get_arg = index) self#get_string_sinks 
    with
      Not_found -> raise (JCH_failure 
			    (LBLOCK [ STR "No string sink found for arg " ; INT index ; 
				      STR " in summary for " ; cms#toPretty ]))
	
  method get_resource_sink (index:int) = 
    try 
      List.find (fun s -> s#get_arg = index) self#get_resource_sinks 
    with
      Not_found -> 
	raise (JCH_failure 
		 (LBLOCK [ STR "No resource quantity sink found for arg " ; 
			   INT index ; STR " in summary for " ; cms#toPretty ]))
	
  method has_defining_method = 
    match defining_method with Some _ -> true | _ -> false

  method get_defining_method = 
    match defining_method with Some cms -> cms | _ ->
      if self#is_inherited then 
	raise (JCH_failure 
		 (LBLOCK [ STR "Inherited function summary for " ; cms#toPretty ; 
			   STR " does not have a defining method recorded" ]))
      else
	cms
	
  method has_string_sink (index:int) =
    List.exists (fun s -> s#get_arg = index) self#get_string_sinks
      
  method has_resource_sink (index:int) =
    List.exists (fun s -> s#get_arg = index) self#get_resource_sinks
      
  method private write_xml_exceptions (node:xml_element_int) =
    node#appendChildren (List.map (fun e ->
      if e#has_safety_condition then
	let eNode = xmlElement "c-throws" in 
	begin e#write_xml eNode self#get_method_signature ; eNode end
      else
	xml_string "throws" e#get_exception#name) self#get_exception_infos)

  method private write_xml_virtual_calls (node:xml_element_int) =
    node#appendChildren (List.map (fun c ->
      let cNode = xmlElement "virtual-call" in
      begin write_xml_call cNode cms ; cNode end) self#get_virtual_calls)

  method private write_xml_interface_calls (node:xml_element_int) =
    node#appendChildren (List.map (fun c ->
      let cNode = xmlElement "interface-call" in
      begin write_xml_call cNode cms ; cNode end) self#get_interface_calls)

  method private write_xml_inherited (node:xml_element_int) =
    let seti = node#setIntAttribute in
    let cms = self#get_cms in
    begin
      seti "cmsix" cms#index ;
      if self#has_defining_method then
        seti "from" self#get_defining_method#class_name#index
    end

  method write_xml (node:xml_element_int) =
    if self#is_inherited then
      self#write_xml_inherited node
    else 
    let append = node#appendChildren in
    let set = node#setAttribute in
    let seti = node#setIntAttribute in
    let sety tag v = if v then set tag "yes" else () in
    let setn tag v = if v then () else set tag "no" in
    let sNode = xmlElement "signature" in
    let eeNode = xmlElement "exceptions" in
    let ccNode = xmlElement "calls" in
    let uNode = xmlElement "summary" in
    let cms = self#get_cms in
    begin
      (* cms#method_signature#write_xml sNode ; *)
      self#write_xml_exceptions eeNode ;
      self#write_xml_virtual_calls ccNode ;
      self#write_xml_interface_calls ccNode ;
      self#write_xml_summary uNode ;
      set "name" cms#method_name_string ;
      append [ sNode ; eeNode ; ccNode ; uNode ] ;
      seti "cmsix" cms#index ;
      setn "valid" is_valid ;
      sety "final" self#is_final ;
      sety "abstract" self#is_abstract ;
      sety "static" self#is_static ;
      sety "bridge" self#is_bridge ;
      set "access" (access_to_string self#get_visibility) ;
    end

  method private write_xml_postconditions (node:xml_element_int) =
    let ms = self#get_method_signature in
    begin
      node#appendChildren (List.map (fun p ->
	let pNode = xmlElement "post" in
	  begin p#write_xml pNode ms ; pNode end) self#get_post) ;
      node#appendChildren (List.map (fun p ->
	let pNode = xmlElement "error-post" in
	  begin p#write_xml pNode ms ; pNode end) self#get_error_post)
    end

  method private write_xml_sinks (node:xml_element_int) =
    let ms = self#get_method_signature in
    node#appendChildren (List.map (fun s -> 
      let sNode = xmlElement "sink" in
      begin s#write_xml sNode ms ; sNode end) self#get_string_sinks)
	
  method write_xml_summary (node:xml_element_int) =
    let append = node#appendChildren in
    let ppNode = xmlElement "postconditions" in
    let ssNode = xmlElement "sinks" in
    let tNode = xmlElement "taint" in
    begin
      taint#write_xml tNode self#get_method_signature ;
      self#write_xml_postconditions ppNode ;
      self#write_xml_sinks ssNode ;
      append [ ppNode ; ssNode ; tNode ]
    end
      
  method toPretty = 
    let pPost = match self#get_post with 
	[] -> STR ""
      | l -> LBLOCK [ 
	INDENT(3, LBLOCK [STR "post: " ; 
			  pretty_print_list l (fun p -> p#toPretty) 
			    "" " and " "" ; NL ]) ] in
    let pErrorPost = match self#get_error_post with
	[] -> STR ""
      | l -> LBLOCK [ 
	INDENT(3, LBLOCK [ STR "error-post: " ; 
			   pretty_print_list l (fun p -> p#toPretty) 
			     "" " or " "" ; NL ]) ] in
    let pSideEffects = match sideeffects with
	[] -> STR ""
      | l -> LBLOCK [ 
	INDENT (3, LBLOCK [ STR "side effects: " ; 
			    pretty_print_list l sideeffect_to_pretty 
			      "" " and " "" ; NL]) ] in
    let pTaint = match taint#get_elements with
	[] -> STR ""
      | _ -> LBLOCK [ STR "taint: " ; NL ; INDENT (3, taint#toPretty) ] in
    let pVirtualCalls = match self#get_virtual_calls with
	[] -> STR ""
      | l -> LBLOCK [ 
	STR "virtual calls: " ; NL ; 
	INDENT (3, pretty_print_list l (fun cms -> LBLOCK [ cms#toPretty ; NL ]) 
	  "" "" "") ; NL ] in
    let pStringSinks = match self#get_string_sinks with
	[] -> STR ""
      | l -> LBLOCK [ STR "string-sinks: " ; 
		      pretty_print_list l (fun s -> s#toPretty) "" ", " "" ] in
    let pResourceSinks = match self#get_resource_sinks with
	[] -> STR ""
      | l -> LBLOCK [ STR "resource-sinks: " ; 
		      pretty_print_list l (fun s -> s#toPretty) "" ", " "" ] in
    let pInterfaceCalls = match self#get_interface_calls with
	[] -> STR ""
      | l -> LBLOCK [ 
	STR "interface calls: " ; NL ;
	INDENT (3, pretty_print_list l (fun cms -> LBLOCK [ cms#toPretty ; NL ])
	  "" "" "") ; NL ] in	
    let pExceptions = match self#get_exception_infos with
	[] -> STR ""
      | l -> LBLOCK [ 
	STR "exceptions: " ; NL ;
	INDENT (3, pretty_print_list l (fun eInfo -> LBLOCK [ eInfo#toPretty ; NL ]) 
	  "" "" "") ; NL ] in
    LBLOCK [
      cms#toPretty ; 
      (if cms#method_signature#is_static then STR " (static)" else STR "") ; 
      NL ; 
      pExceptions ; pPost ; pErrorPost ; pSideEffects ; pTaint ; pStringSinks ; 
      pResourceSinks ; pVirtualCalls ; pInterfaceCalls ; NL ]
      
      
end
  
let make_function_summary
    ?(is_static=false)
    ?(is_final=false)
    ?(is_abstract=false)
    ?(is_inherited=false)
    ?(is_default=false)
    ?(is_valid=true)
    ?(defining_method=None)
    ?(is_bridge=false)
    ?(visibility=Public)
    ?(exception_infos=[])
    ?(post=[])
    ?(sideeffects=[])
    ?(taint=no_taint_info)
    ?(virtual_calls=[])
    ?(interface_calls=[])
    ?(resource_sinks=[])
    ?(string_sinks=[])
    ?(pattern=None)
    ?(time_cost=top_jterm_range)
    ?(space_cost=top_jterm_range)
    (cms:class_method_signature_int)  =
  let add_taint p =
    match p#get_predicate with
    | PostRelationalExpr (JEquals, JLocalVar x, JLocalVar (-1))
    | PostRelationalExpr (JEquals, JLocalVar (-1), JLocalVar x) ->
      begin
        taint#add_element (TTransfer (JLocalVar (-1), JLocalVar x)) ;
        taint#add_element (TTransfer (JLocalVar x, JLocalVar (-1)))
      end
    | _ -> () in
  begin
    List.iter add_taint post ;
    new function_summary_t
      ~cms
      ~is_static
      ~is_final
      ~is_abstract
      ~is_inherited
      ~is_default
      ~is_valid
      ~defining_method
      ~is_bridge
      ~visibility
      ~exception_infos
      ~post
      ~sideeffects
      ~taint
      ~virtual_calls
      ~interface_calls
      ~resource_sinks
      ~string_sinks
      ~pattern
      ~time_cost
      ~space_cost
  end
    

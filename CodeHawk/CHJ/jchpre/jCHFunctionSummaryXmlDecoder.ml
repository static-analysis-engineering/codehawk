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
open CHLogger
open CHStringIndexTable
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHDictionary
open JCHJTerm

(* jchpre *)
open JCHClassSummary
open JCHFieldInfo
open JCHFunctionSummary
open JCHPreAPI


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg;
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end


let class_is_final = ref false


let rec read_xml_type (node:xml_element_int) =
  match node#getChild#getTag with
  | "int" -> TBasic Int
  | "short" -> TBasic Short
  | "char"  -> TBasic Char
  | "byte"  -> TBasic Byte
  | "boolean" -> TBasic Bool
  | "long"    -> TBasic Long
  | "float"   -> TBasic Float
  | "double"  -> TBasic Double
  | "object"
  | "new-object" ->
    let class_name = node#getChild#getText in
    let class_name = make_cn class_name in
    TObject (TClass class_name)
  | "array"   -> TObject (TArray (read_xml_type node#getChild))
  | s ->
     raise_xml_error node
       (LBLOCK [STR "tag not recognized in decodeXmlType: "; STR s])


let arg_length_msg (info:string) (expected_len:int) args =
  let actual_len = List.length args in
  let arg_pretty = if expected_len = 1 then
      STR " one argument (no arguments found)"
    else
      LBLOCK [
          INT expected_len;
          STR " arguments (only ";
          INT actual_len;
          STR " found)"] in
  LBLOCK [STR info; STR " expects "; arg_pretty]


let read_xml_sinks (node:xml_element_int) (cms:class_method_signature_int) =
  let ms = cms#method_signature in
  List.fold_left (fun (sinks,resources) n ->
    let has = n#hasNamedAttribute in
    let get = n#getAttribute in
    let geti = n#getIntAttribute in
    let arg = geti "arg" in
    let arg = if ms#is_static then arg - 1 else arg in
    let _ =
      if arg < 0 || arg > (List.length ms#descriptor#arguments) then
	raise_xml_error
          n
          (LBLOCK [
               STR "Sink argument ";
               INT arg;
	       STR " is not part of the signature"]) in
    let sinkType = if has "type" then
	match get "type" with
	| "string" -> "string"
	| "rq" | "resource" -> "resource"
	| _ -> "string"
      else "string" in
    if sinkType = "string" then
      let exns =
        List.map  (fun n -> make_cn n#getText) (n#getTaggedChildren "throws") in
      let sink = make_string_sink arg (get "form") (get "dest") exns in
      (sink::sinks,resources)
    else
      let form = match get "form" with
	| "memory" -> RMemory
	| "time" | "waiting-time" -> RWaitingTime
	| "threads" -> RThreads
	| "filesize" -> RFileSize
	| s ->
	   raise_xml_error
             n (LBLOCK [STR "Resource form "; STR s; STR " not recognized"]) in
      let resource = make_resource_sink arg form in
      (sinks,resource::resources)) ([],[]) (node#getTaggedChildren "sink")


let read_xml_taint (node:xml_element_int) (cms:class_method_signature_int) =
  let get_term n = read_xmlx_simple_jterm n cms in
  let taintElements = List.map (fun n ->
    let args = n#getChildren in
    let arglen = List.length args in
    let get_arg i msg =
      if i < arglen then List.nth args i else	raise_xml_error n msg in
    match n#getTag with
    | "transfer" ->
       let msg = arg_length_msg "taint transfer" 2 args in
       TTransfer (get_term (get_arg 0 msg), get_term (get_arg 1 msg))
    | "put" ->
       let msg = arg_length_msg "taint put" 1 args in
       TDefPut (get_term (get_arg 0 msg))
    | "defput" ->
       let msg = arg_length_msg "taint defput" 1 args in
       TDefPut (get_term (get_arg 0 msg))
    | "remove" ->
       let msg = arg_length_msg "taint remove" 1 args in
       TRemove (get_term (get_arg 0 msg))
    | s ->
       raise_xml_error
         n (LBLOCK [STR "Taint element "; STR s; STR " not recognized"]))
    node#getChildren in
  make_taint taintElements


let read_xml_postcondition_predicate
      (node: xml_element_int) (cms: class_method_signature_int) =
  let getterm n = read_xmlx_jterm n cms in
  let cNodes = node#getChildren in
  match cNodes with
  | [] -> raise_xml_error node (STR "Postcondition predicate without arguments")
  | pNode :: argNodes ->
    let arglen = List.length argNodes in
    let getarg n =
      if n < arglen then
        List.nth argNodes n
      else
	raise_xml_error
          node (LBLOCK [STR "Expected "; INT (n+1); STR " arguments"]) in
    let get_object n = match n#getTag with
      | "object" -> make_cn n#getText
      | s ->
	 raise_xml_error
           n (LBLOCK [STR "Expected to see object in stead of "; STR s]) in
    if is_relational_op pNode#getTag then
      PostRelationalExpr (read_xmlx_relational_expr node cms)
    else
      match pNode#getTag with
      | "new-object" -> PostNewObject (get_object (getarg 0))
      | "object-class" -> PostObjectClass (get_object (getarg 0))
      | "wrapped" -> PostWrapped (getterm (getarg 0))
      | "element" -> PostElement (getterm (getarg 0))
      | "same-collection" -> PostSameCollection (getterm (getarg 0))
      | s ->
	 raise_xml_error
           pNode
           (LBLOCK [STR "Postcondition symbol "; STR s; STR " not recognized"])


let read_xml_precondition_predicate
      (node: xml_element_int) (cms: class_method_signature_int) =
  let getterm n = read_xmlx_jterm n cms in
  let cNodes = node#getChildren in
  match cNodes with
  | [] -> raise_xml_error node (STR "Precondition predicate without arguments")
  | pNode :: argNodes ->
    let arglen = List.length argNodes in
    let getarg n =
      if n < arglen then
        List.nth argNodes n
      else
	raise_xml_error
          node (LBLOCK [STR "Expected "; INT (n+1); STR " arguments"]) in
    if is_relational_op pNode#getTag then
      PreRelationalExpr (read_xmlx_relational_expr node cms)
    else
      match pNode#getTag with
      | "null" -> PreNull (getterm (getarg 0))
      | "not-null" -> PreNotNull (getterm (getarg 0))
      | "valid" -> PreValidString (getterm (getarg 0), pNode#getAttribute "format")
      | s ->
         raise_xml_error
           pNode (LBLOCK [STR "Precondition symbol "; STR s; STR " not recognized"])


let read_xml_post (node: xml_element_int) (cms: class_method_signature_int) =
  let ms = cms#method_signature in
  let _ = match ms#descriptor#return_value with
    | Some _ -> ()
    | _ ->
       raise_xml_error
         node
	 (LBLOCK [STR "Method without return value cannot have a postcondition"]) in
  let _ =
    if node#hasOneTaggedChild "math" then
      ()
    else
      raise_xml_error node (STR "Expected an element with tag math") in
  let mNode = node#getTaggedChild "math" in
  let pNode = mNode#getChild in
  match pNode#getTag with
  | "apply" -> read_xml_postcondition_predicate pNode cms
  | "true" -> PostTrue
  | "false" -> PostFalse
  | "null" -> PostNull
  | "not-null" -> PostNotNull
  | "element" -> PostElement (JLocalVar 0)
  | "empty-collection" -> PostEmptyCollection
  | "unwrapped" -> PostUnwrapped
  | "valid" -> PostValidString (pNode#getAttribute "format")
  | s ->
     raise_xml_error
       node (LBLOCK [STR "Postcondition tag "; STR s; STR " not recognized"])


let read_xml_postcondition
      (node: xml_element_int) (cms: class_method_signature_int) =
  let has = node#hasNamedAttribute in
  let get = node#getAttribute in
  let hasc = node#hasOneTaggedChild in
  let is_error = node#getTag = "error-post" in
  let name = if has "name" then get "name" else "none" in
  let pred =
    if hasc "math" then read_xml_post node cms else
      raise_xml_error
        node
        (LBLOCK [STR "Postcondition without predicate"]) in
  make_postcondition ~name is_error pred


let read_xml_safety_condition
      (node: xml_element_int) (cms: class_method_signature_int) =
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  if hasc "math" then
    let mNode = getc "math" in
    if mNode#hasOneTaggedChild "apply" then
      let aNode = mNode#getTaggedChild "apply" in
      read_xml_precondition_predicate aNode cms
    else
      raise_xml_error mNode (STR "Expected to see element with tag apply")
  else
    raise_xml_error node (STR "Expected to see element with tag math")


let read_xml_postconditions
      (node: xml_element_int) (cms: class_method_signature_int) =
  let ppNodes =
    (node#getTaggedChildren "post") @ (node#getTaggedChildren "error-post") in
  List.map (fun pNode -> read_xml_postcondition pNode cms) ppNodes


let read_xml_sideeffect_predicate
      (node: xml_element_int) (cms: class_method_signature_int) =
  let getterm n = read_xmlx_jterm n cms in
  let cNodes = node#getChildren in
  match cNodes with
  | [] -> raise_xml_error node (STR "Sideeffect predicate without arguments")
  | pNode :: argNodes ->
    let arglen = List.length argNodes in
    let getarg i =
      if i < arglen then
        List.nth argNodes i
      else
	raise_xml_error
          node (LBLOCK [STR "Expected "; INT (i+1); STR " arguments"]) in
    match pNode#getTag with
    | "numeric-join" ->
      NumericJoin (getterm (getarg 0), getterm (getarg 1), getterm (getarg 2))
    | "numeric-abstract" ->
      NumericAbstract (getterm (getarg 0))
    | "set-value" -> SetValue (getterm (getarg 0))
    | "wrap" -> Wrap (getterm (getarg 0), getterm (getarg 1))
    | s ->
       raise_xml_error
         pNode (LBLOCK [STR "Sideeffect symbol "; STR s; STR " not recognized"])


let read_xml_sideeffect (node:xml_element_int) (cms:class_method_signature_int) =
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  if hasc "math" then
    let mNode = getc "math" in
    let pNode = mNode#getChild in
    match pNode#getTag with
    | "apply" -> read_xml_sideeffect_predicate pNode cms
    | "wrap" -> Wrap (JLocalVar 1, JLocalVar 0)
    | s ->
      raise_xml_error pNode
	(LBLOCK [STR "Sideeffect symbol "; STR s; STR " not recognized"])
  else
    raise_xml_error node (STR "Expected to see element with tag math")


let read_xml_sideeffects (node:xml_element_int) (cms:class_method_signature_int) =
  let getcc = node#getTaggedChildren in
  List.map (fun sNode -> read_xml_sideeffect sNode cms) (getcc "side-effect")


let read_xmlx_timecost (node:xml_element_int) (cms:class_method_signature_int) =
  read_xmlx_jterm_range (node#getTaggedChild "cost") cms


let read_xml_method_summary
    ~(node:xml_element_int)
    ~(cms:class_method_signature_int)
    ~(exception_infos:exception_info_int list)
    ~(virtual_calls:class_method_signature_int list)
    ~(interface_calls:class_method_signature_int list)
    ~(is_static:bool)
    ~(is_final:bool)
    ~(is_abstract:bool)
    ~(is_default:bool)
    ~(is_bridge:bool)
    ~(visibility:access_t) =
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let post = if hasc "postconditions" then
      read_xml_postconditions (getc "postconditions") cms
    else
      [] in
  let sideeffects = if hasc "side-effects" then
      read_xml_sideeffects (getc "side-effects") cms
    else
      [] in
  let time_cost =
    if hasc "time-cost" then
      let cNode = getc "time-cost" in
      if cNode#hasNamedAttribute "src"
         && ((cNode#getAttribute "src") = "model"
             || (cNode#getAttribute "src") = "guess") then
        top_jterm_range
      else
        read_xmlx_timecost cNode cms
    else
      top_jterm_range in
  let _ =
    if time_cost#is_top then
      ()
    else
      chlog#add
        "time cost"
        (LBLOCK [cms#toPretty; STR ": "; time_cost#toPretty])  in
  let taint =
    if hasc "taint" then
      read_xml_taint (getc "taint") cms
    else
      make_taint [] in
  let (string_sinks,resource_sinks) =
    if hasc "sinks" then
      read_xml_sinks (getc "sinks") cms
    else
      ([],[]) in
  make_function_summary
    ~is_static
    ~is_final
    ~is_abstract
    ~is_bridge
    ~is_default
    ~visibility
    ~exception_infos
    ~virtual_calls
    ~interface_calls
    ~post
    ~sideeffects
    ~taint
    ~resource_sinks
    ~string_sinks
    ~time_cost
    cms


let read_xml_method_signature (node: xml_element_int) =
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let getcc = node#getTaggedChildren in
  let argTypes = List.map read_xml_type (getcc "arg") in
  let returnType =
    if hasc "return" then Some (read_xml_type (getc "return")) else None in
  (argTypes,returnType)


let read_xml_exceptions (node: xml_element_int) (cms: class_method_signature_int) =
  let ms = cms#method_signature in
  let getcc = node#getTaggedChildren in
  let exceptions =
    List.map (fun eNode ->
      make_exception_info (make_cn eNode#getText)) (getcc "throws") in
  let make_cnp (node:xml_element_int) =
    let getcc = node#getTaggedChildren in
    if List.for_all (fun x -> x#getTag = "cnp") node#getChildren then
      let exn = make_cn "java.lang.NullPointerException" in
      let args = List.map (fun n -> n#getIntAttribute "arg") (getcc "cnp") in
      let args = List.map (fun a ->
	let index = if ms#is_static then a-1 else a in
	let _ =
          if index > (List.length ms#descriptor#arguments) || index < 0 then
	    raise_xml_error
              node (LBLOCK [STR "Invalid argument in cnp: "; INT index]) in
	index) args in
      let safe = List.map (fun a -> PreNotNull (JLocalVar a)) args in
      let unsafe = List.map (fun a -> PreNull (JLocalVar a)) args in
      make_exception_info ~safe ~unsafe exn
    else
      raise_xml_error
        node (LBLOCK [STR "Invalid list of nullpointer conditions"]) in
  let cExceptions = List.map (fun cNode ->
    let getc = cNode#getTaggedChild in
    let getcc = cNode#getTaggedChildren in
    let has = cNode#hasNamedAttribute in
    let get = cNode#getAttribute in
    if cNode#hasTaggedChildren "cnp" then
      make_cnp cNode
    else
      let exn = make_cn (getc "exn")#getText in
      let descr = if has "descr" then get "descr" else "" in
      let safe =
        List.map
          (fun sNode -> read_xml_safety_condition sNode cms)
	  ((getcc "safety-condition") @ (getcc "safe")) in
      make_exception_info ~descr ~safe exn) (getcc "c-throws") in
  exceptions @ cExceptions


let read_xml_cms (node: xml_element_int) =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let name = get "name" in
  let (arguments,returnType) = read_xml_method_signature (getc "signature") in
  let methodDesc = match returnType with
    | Some return_value -> make_method_descriptor ~arguments ~return_value ()
    | _ -> make_method_descriptor ~arguments () in
  make_cms (make_cn (get "class")) (make_ms false name methodDesc)


let read_xml_calls (node: xml_element_int) =
  let getcc = node#getTaggedChildren in
  let vNodes = getcc "virtual-call" in
  let iNodes = getcc "interface-call" in
  (List.map read_xml_cms vNodes, List.map read_xml_cms iNodes)


let read_xml_access_modifier (node:xml_element_int) =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  if has "access" then
    match get "access" with
    | "public" -> Public
    | "default" -> Default
    | "private" -> Private
    | "protected" -> Protected
    | s ->
       raise_xml_error
         node (LBLOCK [STR "Access modifier "; STR s; STR " not recognized"])
  else
    Public


let read_xml_method (node: xml_element_int) (cn: class_name_int) =
  let has = node#hasNamedAttribute in
  let get = node#getAttribute in
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let is_yes tag = has tag && (get tag) = "yes" in
  try
    let name = get "name" in
    let is_static = is_yes "static" in
    let (arguments, returnType) = read_xml_method_signature (getc "signature") in
    let methodDescr = match returnType with
      | Some return_value -> make_method_descriptor ~arguments ~return_value ()
      | _ -> make_method_descriptor ~arguments () in
    let ms = make_ms is_static name methodDescr in
    let cms = make_cms cn ms in
    let inherited = has "inherited" && (get "inherited") = "yes" in
    if inherited then
      if has "from" then
	let fromCn = make_cn (get "from") in
	let fromCms = make_cms fromCn ms in
	(cms,
         [],
	 make_function_summary
	   ~is_inherited:true
	   ~defining_method:(Some fromCms) cms)
      else
	begin
	  chlog#add "missing defining method" cms#toPretty;
	  (cms, [], make_function_summary ~is_inherited:true cms)
	end
    else
      let isNotValid = has "valid" && (get "valid") = "no" in
      if isNotValid then
        let visibility =
          if has "access" then
            read_xml_access_modifier node
          else
            Public in
        let is_abstract = is_yes "abstract" in
        let is_final = !class_is_final || (is_yes "final") in
	(cms,
         [],
         make_function_summary
           ~is_final ~is_abstract ~visibility ~is_valid:false cms)
      else
	let is_final = !class_is_final || (is_yes "final") in
	let is_abstract = is_yes "abstract" in
	let is_bridge = is_yes "bridge" in
	let visibility = read_xml_access_modifier node in
        let is_default = is_yes "default" in
	let exception_infos = read_xml_exceptions (getc "exceptions") cms in
	let (virtual_calls, interface_calls) =
	  if hasc "calls" then read_xml_calls (getc "calls") else ([],[]) in
	let loops = (* if hasc "loops" then
	    read_xml_summary_loops (getc "loops") ms
	  else *)
	  [] in
	let summary =
          read_xml_method_summary
            ~node:(getc "summary")
            ~cms
            ~exception_infos
	    ~virtual_calls
            ~interface_calls
            ~is_static
            ~is_final
            ~is_abstract
	    ~is_default
            ~is_bridge
            ~visibility in
	(cms,loops,summary)
  with
  | XmlParseError (line,column,p)
  | XmlDocumentError (line,column,p) ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "Xml error at (";
               INT line;
               STR ",";
               INT column;
	       STR ") in method for ";
	       STR (get "name");
               STR " in class ";
               cn#toPretty;
	       STR ": ";
               p;
               NL]))


let read_xml_constructor (node: xml_element_int) (cn: class_name_int) =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  try
    let (arguments,_) = read_xml_method_signature (getc "signature") in
    let methodDescr = make_method_descriptor ~arguments () in
    let ms = make_ms false "<init>" methodDescr in
    let cms = make_cms cn ms in
    let isNotValid = has "valid" && (get "valid") = "no" in
    if isNotValid then
      let visibility =
        if has "access" then
          read_xml_access_modifier node
        else
          Public in
      (cms, [], make_function_summary ~visibility ~is_valid:false cms)
    else
      let exception_infos = read_xml_exceptions (getc "exceptions") cms in
      let (virtual_calls, interface_calls) =
	if hasc "calls" then read_xml_calls (getc "calls") else ([],[]) in
      let visibility = read_xml_access_modifier node in
      let loops = [] in
      let summary =
        read_xml_method_summary
          ~node:(getc "summary")
          ~cms
          ~exception_infos
	  ~virtual_calls
          ~interface_calls
          ~is_static:false
          ~is_final:false
	  ~is_default:false
          ~is_abstract:false
          ~is_bridge:false
          ~visibility in
      (cms,loops,summary)
  with
  | XmlParseError (line, column, p)
  | XmlDocumentError (line, column, p) ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "Xml error at (";
               INT line;
               STR ", ";
               INT column;
	       STR ") in constructor in class ";
	       cn#toPretty;
               STR ": ";
               p;
               NL]))


let read_xml_field_value (node:xml_element_int) =
  let vNode = node#getChild in
  let get = vNode#getAttribute in
  let getf tag = float_of_string (get tag) in
  let get32 tag = Int32.of_string (get tag) in
  let get64 tag = Int64.of_string (get tag) in
  let has = vNode#hasNamedAttribute in
  match node#getChild#getTag with
  | "byte" | "short" | "int" -> ConstInt (get32 "value")
  | "long" -> ConstLong (get64 "value")
  | "float" -> ConstFloat (getf "value")
  | "double" -> ConstDouble (getf "value")
  | "string" ->
     if has "value" then
       ConstString (get "value")
     else if has "hexvalue" then
       let s = decode_string (true,get "hexvalue") in
       ConstString s
     else
       ConstString vNode#getText
  | "object" -> ConstClass (TClass (make_cn vNode#getText))
  | s ->
     raise_xml_error
       node (LBLOCK [STR "Field value type "; STR s; STR " not recognized"])


let read_xml_field
      (node: xml_element_int) ?(is_interface_field=false) (cn: class_name_int) =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  let hasc = node#hasOneTaggedChild in
  let is_yes tag = has tag && (get tag) = "yes" in
  let fieldName = get "name" in
  let is_final = is_yes "final" in
  let is_static = is_yes "static" in
  let is_not_null = is_yes "not-null"  in
  let is_inherited = is_yes "inherited" in
  let fieldType = read_xml_type (getc "signature") in
  let fs = common_dictionary#make_field_signature fieldName fieldType in
  let cfs = common_dictionary#make_class_field_signature cn fs in
  let inherited_from =
    if is_inherited then
      let fromCn = make_cn (get "from") in
      Some (make_cfs fromCn fs)
    else
      None in
  let (is_constant, field_value) =
    if hasc "value" then
      (true, Some (read_xml_field_value (getc "value")))
    else
      (false,None) in
  let fieldStub =
    make_field_stub ~is_static ~is_final ~is_not_null ~is_interface_field
    ~is_constant ~field_value ~inherited_from cfs in
  (cfs, fieldStub)


let read_xml_class_property (node:xml_element_int) =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  match (get "name") with
  | "size" ->
     if has "method" then
       let methodname = get "method" in
       let (arguments,returnType) = read_xml_method_signature (getc "signature") in
       let methodDesc = match returnType with
         | Some return_value -> make_method_descriptor ~arguments ~return_value ()
         | _ -> make_method_descriptor ~arguments () in
       let ms = make_ms false methodname methodDesc in
       LogicalSize (MethodAccessor ms)
     else
       raise_xml_error
         node (LBLOCK [STR "accessor in size property not recognized"])
  | s ->
     raise_xml_error
       node (LBLOCK [STR "class property "; STR s; STR " not recognized"])


let read_xml_class_properties (node:xml_element_int) =
  List.map read_xml_class_property (node#getTaggedChildren "cprop")


let read_xml_methods (node:xml_element_int) (cn:class_name_int) =
  List.map (fun n -> read_xml_method n cn) (node#getTaggedChildren "method")


let read_xml_constructors (node:xml_element_int) (cn:class_name_int) =
  List.map
    (fun c -> read_xml_constructor c cn) (node#getTaggedChildren "constructor")


let read_xml_fields
      (node: xml_element_int) ?(is_interface_field=false) (cn: class_name_int) =
  let getcc = node#getTaggedChildren in
  List.map (fun f -> read_xml_field f ~is_interface_field cn) (getcc "field")


let read_xml_interfaces (node: xml_element_int) =
  let serializable = make_cn "java.io.Serializable" in
  let getcc = node#getTaggedChildren in
  serializable
  :: (List.map (fun xNode -> make_cn xNode#getText) (getcc "implements"))


let read_xml_class
      (node:xml_element_int) (date:string option) (package:string) =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  let hasc = node#hasOneTaggedChild in
  let is_yes tag = has tag && ((get tag) = "yes") in
  let name = get "name" in
  try
    let is_abstract = is_yes "abstract" in
    let is_final = is_yes "final" in
    let is_immutable = is_yes "immutable" in
    let _ = class_is_final := is_final in
    let cn = if package = "" then
	make_cn name
      else
	make_cn (package ^ "." ^ name) in
    let fields =
      if hasc "fields" then read_xml_fields (getc "fields") cn else [] in
    let interfaces =
      if hasc "interfaces" then read_xml_interfaces (getc "interfaces") else [] in
    let super_class = if hasc "superclass" then
	Some (make_cn (getc "superclass")#getText)
      else if cn#name = "java.lang.Object" then
	None
      else
	Some (make_cn "java.lang.Object") in
    let class_properties =
      if hasc "class-properties" then
        read_xml_class_properties (getc "class-properties")
      else
        [] in
    let method_summaries = read_xml_methods (getc "methods") cn in
    let constructor_summaries = read_xml_constructors (getc "constructors") cn in
    let method_summaries = constructor_summaries @ method_summaries in
    let method_signatures = List.map (fun (cms,_,_) -> cms#method_signature)
      (List.filter (fun (_, _, s) -> not s#is_inherited) method_summaries) in
    let field_signatures = List.map (fun (cfs,_) -> cfs#field_signature) fields in
    let class_summary =
      make_class_summary
        ~super_class
        ~is_abstract
        ~is_final
        ~is_immutable
        ~date
        ~interfaces
        ~class_properties
	~method_summaries:method_signatures
        ~fields:field_signatures cn in
    ((cn, class_summary), fields, method_summaries)
  with
  | XmlDocumentError (line, column, p) ->
     let msg =
       LBLOCK [
           STR "Xml error at (";
           INT line;
           STR ", ";
           INT column;
	   STR " in ";
           STR package;
           STR ".";
           STR name;
           STR ": ";
           p] in
    begin
      pr_debug [msg; NL];
      raise (JCH_failure msg)
    end


let read_xml_superinterfaces (node:xml_element_int) =
  let getcc = node#getTaggedChildren in
  List.map (fun sNode -> make_cn sNode#getText) (getcc "superinterface")


let read_xml_default_implementations (node:xml_element_int) =
  let getcc = node#getTaggedChildren in
  List.map (fun sNode -> make_cn sNode#getText) (getcc "class")


let read_xml_interface
      (node:xml_element_int) (date:string option) (package:string) =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let is_yes tag = has tag && ((get tag) = "yes") in
  let name = get "name" in
  try
    let interface_name = make_cn (package ^ "." ^ name) in
    let is_dispatch = is_yes "dispatch" in
    let super_interfaces =
      if hasc "superinterfaces" then
	read_xml_superinterfaces (getc "superinterfaces")
      else
	[] in
    let interface_fields =
      if hasc "fields" then
	read_xml_fields (getc "fields") ~is_interface_field:true interface_name
      else
	[] in
    let interface_methods =
      if hasc "methods" then
	read_xml_methods (getc "methods") interface_name
      else
	[] in
    let default_implementations =
      if hasc "default-implementations" then
	read_xml_default_implementations (getc "default-implementations")
      else
	[] in
    let class_properties =
      if hasc "class-properties" then
        read_xml_class_properties (getc "class-properties")
      else
        [] in
    let method_signatures =
      List.map
        (fun (cms, _, _) -> cms#method_signature)
        (List.filter (fun (_, _, s) -> not s#is_inherited) interface_methods) in
    let interface_summary =
      make_class_summary
	~is_interface:true
	~is_abstract:true
	~is_dispatch
        ~date
	~interfaces:super_interfaces
	~default_implementations
        ~class_properties
	~method_summaries:method_signatures interface_name in
    ((interface_name,interface_summary), interface_fields, interface_methods)
  with
  | XmlDocumentError (line, column, p) ->
     let msg =
       LBLOCK [
           STR "Xml error at (";
           INT line;
           STR ", ";
           INT column;
	   STR ") in ";
           STR package;
           STR ".";
           STR name;
           STR ": ";
           p] in
      begin
	pr_debug [msg; NL];
	raise (JCH_failure msg)
      end


let read_xml_class_file_from_string (name:string) (s:string) =
  try
    let doc = readXmlDocumentString s in
    let root = doc#getRoot in
    let hasc = root#hasOneTaggedChild in
    let date =
      if root#hasNamedAttribute "date" then
        Some (root#getAttribute "date")
      else
        None in
    if hasc "class" then
      let cNode = root#getTaggedChild "class" in
      read_xml_class cNode date (cNode#getAttribute "package")
    else if hasc "interface" then
      let iNode = root#getTaggedChild "interface" in
      read_xml_interface iNode date (iNode#getAttribute "package")
    else
      raise (JCH_failure (LBLOCK [STR "Unexpected type of summary file: "; STR s]))
  with
  | XmlDocumentError (line, column, p) ->
     raise
       (JCH_failure
          (LBLOCK [
               STR "Xml error at (";
               INT line;
               STR ", ";
               INT column;
	       STR ") in ";
               STR name;
               STR ": ";
               p]))
  | CHXmlReader.XmlParseError (l, c, p) ->
     let p = LBLOCK [STR "Error in class "; STR name; STR ": "; p] in
     raise (CHXmlReader.XmlParseError (l, c, p))

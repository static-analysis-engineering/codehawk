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
open CHLanguage
open CHNumerical
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument

(* xprlib *)
open Xprt
open XprToPretty
open CHPrettyUtil

(* bchlib *)
open BCHApiParameter
open BCHBasicTypes
open BCHBTerm
open BCHCallTarget
open BCHDemangler
open BCHDoubleword
open BCHCPURegisters
open BCHFunctionApi
open BCHLibTypes
open BCHPostcondition
open BCHPrecondition
open BCHSideeffect
open BCHSystemSettings
open BCHTypeDefinitions
open BCHUtilities
open BCHVariableType
open BCHXmlUtil

module P = Pervasives

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

let b3join b1 b2 =
  match (b1,b2) with
  | (Yes,_) -> Yes
  | (No,Yes) -> Yes
  | (No,Maybe) -> Maybe
  | (No,No) -> No
  | (Maybe,Yes) -> Yes
  | (Maybe,_) -> Maybe

let read_xml_bool3 (s:string) =
  match s with
  | "yes" | "true" -> Yes
  | "no" | "false" -> No
  | _ -> Maybe

let bool3_to_string (b:bool3) =
  match b with
  | Yes -> "yes"
  | No -> "no"
  | Maybe -> "maybe"

          

let make_xml_par_sideeffect (se:sideeffect_t) (par:api_parameter_t) =
  let is_par t = match t with
    | ArgValue a -> (api_parameter_compare a par) = 0 | _ -> false in
  let btype_tgt_compare ty party = match party with
    | TPtr (t,_) -> (btype_compare ty t) = 0
    | _ -> false in
  let is_tsize t = match t with
    | ArgSizeOf bty -> btype_tgt_compare bty par.apar_type  | _ -> false in
  match se with
  | BlockWrite (_,t,size) when is_par t && is_tsize size -> Some (xmlElement "block-write")
  | Modifies t when is_par t -> Some (xmlElement "modifies")
  | Invalidates t when is_par t -> Some (xmlElement "invalidates")
  | _ -> None

  	
let read_xml_io_action
    (node:xml_element_int)
    (parameters:api_parameter_t list):io_action_t =
  let get = node#getAttribute in
  { iox_cat = get "cat" ;
    iox_desc = get "desc" ;
    iox_pre = None ;
  }

let read_xml_io_actions (node:xml_element_int) (pars:api_parameter_t list) =
  List.map (fun n -> read_xml_io_action n pars) (node#getTaggedChildren "io-action")

let function_semantics_to_pretty (sem:function_semantics_t) =
  LBLOCK [ 
    (match sem.fsem_pre with [] -> STR "" | _ -> 
      LBLOCK [STR "preconditions: " ; NL ;
	      INDENT (3,LBLOCK [ 
		pretty_print_list sem.fsem_pre 
		  (fun p -> LBLOCK [ precondition_to_pretty p ; NL ]) "" "" "" ]) ; NL ]) ;
    (match sem.fsem_post with [] -> STR "" | _ -> 
      LBLOCK [ STR "postconditions: " ; NL ;
	       INDENT (3, LBLOCK [ 
		 pretty_print_list sem.fsem_post
		   (fun p -> LBLOCK [ postcondition_to_pretty p ; NL ]) "" "" ""] ) ; 
	       NL ]) ;
    (match sem.fsem_errorpost with [] -> STR "" | _ ->
      LBLOCK [ STR "errorpostconditions: " ; NL ;
	       INDENT (3, LBLOCK  [ 
		 pretty_print_list sem.fsem_errorpost
		   (fun p -> LBLOCK [ postcondition_to_pretty p ; NL ]) "" "" "" ]) ;
	       NL ]) ;
    (match sem.fsem_sideeffects with [] -> STR "" | _ ->
      LBLOCK [ STR "sideeffects: " ; NL ;
	       INDENT (3, LBLOCK [ 
		 pretty_print_list sem.fsem_sideeffects
		   (fun s -> LBLOCK [ sideeffect_to_pretty s ; NL ]) "" "" "" ] ) ; NL ])
  ]

let read_xml_function_semantics 
    (node:xml_element_int)
    (parameters:api_parameter_t list):function_semantics_t =
  let get = node#getAttribute in 
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let (post,errorpost) = if hasc "postconditions" then
      let pNode = getc "postconditions" in
      let (sc_post,sc_errorpost) = read_xml_shortcut_postconditions pNode in
      let post = read_xml_postconditions pNode parameters in
      let errorpost = read_xml_errorpostconditions pNode parameters in
      (post @ sc_post, errorpost @ sc_errorpost) 
    else
      ([],[]) in
  let io_actions = if hasc "io-actions" then
      read_xml_io_actions (getc "io-actions") parameters else [] in 
  { fsem_pre = if hasc "preconditions" then 
      read_xml_preconditions (getc "preconditions") parameters else [];
    fsem_post = post ;
    fsem_errorpost = errorpost ;
    fsem_sideeffects = if hasc "sideeffects" then
	read_xml_sideeffects (getc "sideeffects") parameters else [] ;
    fsem_throws = if has "throws" then [ get "throws" ] else
	if hasc "throws" then
	  List.map (fun n -> n#getAttribute "name")
	    ((getc "throws")#getTaggedChildren "exn")
	else
	  [] ;
    fsem_desc = (if has "desc" then get "desc" else "") ;
    fsem_io_actions = io_actions  
    (* fsem_interacts = io_interacts *)
	
  }

let read_xml_function_api_semantics
    (aNode:xml_element_int)
    (sNode:xml_element_int):(function_api_t * function_semantics_t) =
  let pNodes = aNode#getTaggedChildren "par" in
  let api = read_xml_function_api aNode in
  let parPre = List.concat (List.map read_xml_par_preconditions pNodes) in
  let parSE = List.concat (List.map read_xml_par_sideeffects pNodes) in
  let sem = read_xml_function_semantics sNode api.fapi_parameters in
  let sem = { sem with
    fsem_pre = sem.fsem_pre @ parPre ;
    fsem_sideeffects = sem.fsem_sideeffects @ parSE } in
  (api,sem)

let write_xml_function_documentation (node:xml_element_int) (doc:function_documentation_t) =
  let append = node#appendChildren in
  let write_xml_text  (tag:string) (s:string) =
    if s = "" then () else append[ xml_string tag s ] in
  begin
    write_xml_text "desc" doc.fdoc_desc ;
    write_xml_text "remarks" doc.fdoc_remarks ;
    write_xml_text "caution" doc.fdoc_caution ;
    append [ doc.fdoc_xapidoc ]
  end

let read_xml_apidoc (node:xml_element_int):pretty_t =
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  let getcc = node#getTaggedChildren in
  if node#isEmpty then STR "" else
    let read_xml_pt_par (pNode:xml_element_int) =
      LBLOCK [ STR "   " ; STR (pNode#getAttribute "name") ; STR ": " ; 
	       STR pNode#getText ; NL ] in
    let read_xml_pt_return (rNode:xml_element_int) =
      if rNode#hasText then
	LBLOCK [ STR "Return value " ; NL ; STR "   " ; STR rNode#getText ; NL ]
      else
	let read_xml_conditional (cNode:xml_element_int) =
	  LBLOCK [ STR (cNode#getAttribute "cond") ; STR ": " ; 
		   STR cNode#getText ; NL ] in
	LBLOCK [
	  STR "Return value " ; NL ;
	  LBLOCK (List.map (fun cNode -> 
	    LBLOCK [ STR "   " ; read_xml_conditional cNode ]) 
		    (rNode#getTaggedChildren "rc")) ] in
    let read_xml_prototype (pNode:xml_element_int) =
      if pNode#hasText then
	LBLOCK [ STR pNode#getText ; NL ]
      else
	let read_xml_component (cNode:xml_element_int) =
	  match cNode#getTag with
	    "ll" -> LBLOCK [ STR cNode#getText ; NL ]
	  | "ld" -> LBLOCK [ STR "  " ; STR cNode#getText ; NL ]
	  | _ ->
	    raise_xml_error cNode
	      (LBLOCK [ STR "Expected to see <ll> or <ld> but found " ; 
			STR cNode#getTag ]) in
	LBLOCK (List.map read_xml_component pNode#getChildren) in
    LBLOCK [
      read_xml_prototype (getc "pt") ; NL ; NL ;
      STR "Parameters " ; NL ;
      LBLOCK (List.map read_xml_pt_par (getcc "par")) ; NL ;
      if hasc "return" then read_xml_pt_return (getc "return") else STR "" ]


let read_xml_function_documentation (node:xml_element_int):function_documentation_t =
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  { fdoc_desc = if hasc "desc" then (getc "desc")#getText else "" ;
    fdoc_remarks = if hasc "remarks" then (getc "remarks")#getText else "" ;
    fdoc_caution = if hasc "caution" then (getc "caution")#getText else "" ;
    fdoc_apidoc = read_xml_apidoc (getc "apidoc") ;
    fdoc_xapidoc = getc "apidoc"
  }

let modify_types_semantics (f:type_transformer_t) (sem:function_semantics_t) =
  { sem with
    fsem_pre = List.map (modify_types_pre f) sem.fsem_pre ;
    fsem_post = List.map (modify_types_post f) sem.fsem_post ;
    fsem_errorpost = List.map (modify_types_post f) sem.fsem_errorpost ;
    fsem_sideeffects = List.map (modify_types_se f) sem.fsem_sideeffects
  }
	
class function_summary_t 
  ~(api:function_api_t)
  ~(sem:function_semantics_t)
  ~(doc:function_documentation_t):function_summary_int =
object (self:'a)

  val api = api
  val sem = sem
  val doc = doc

  method get_function_api = api
  method get_function_semantics = sem
  method get_function_documentation = doc
  
  method get_name = api.fapi_name
  method get_parameters = api.fapi_parameters
  method get_returntype = api.fapi_returntype
  method get_stack_adjustment = api.fapi_stack_adjustment

  method get_registers_preserved = api.fapi_registers_preserved

  method get_jni_index = 
    match api.fapi_jni_index with Some i -> i | _ ->
      begin
	ch_error_log#add "invocation error" 
	  (LBLOCK [ STR "function_summary#get_jni_index" ]) ;
	raise (Invocation_error "function_summary#get_jni_index")
      end

  method get_preconditions = sem.fsem_pre
  method get_postconditions = sem.fsem_post
  method get_errorpostconditions = sem.fsem_errorpost
  method get_sideeffects = sem.fsem_sideeffects
  method get_io_actions = sem.fsem_io_actions

  method get_enums_referenced =
    let l = ref [] in
    let add s = if List.mem s !l then () else l := s :: !l in
    let _ = List.iter (fun p -> 
      match p with PreEnum (_,s,_) -> add s | _ -> ()) self#get_preconditions in
    let _ = List.iter (fun p ->      
      match p with PostEnum (_,s) -> add s | _ -> ()) self#get_postconditions in
    !l

  method get_enum_type (par:api_parameter_t) =
    List.fold_left (fun acc pre ->
      match acc with Some _ -> acc | _ ->
	match pre with
	| PreEnum (ArgValue p,s,flags) ->
	  if api_parameter_compare p par = 0 then Some (t_named s,flags) else None
	| _ -> None) None self#get_preconditions
    

  method modify_types (name:string) (f:type_transformer_t) =
    {< api = modify_types_api f name api ;
       sem = modify_types_semantics f sem >}

  method has_unknown_sideeffects =
    List.exists (fun p -> match p with UnknownSideeffect -> true | _ -> false)
      sem.fsem_sideeffects

  method sets_errno =
    List.exists (fun p -> match p with SetsErrno -> true | _ -> false)
      sem.fsem_sideeffects

  method is_nonreturning =
    List.exists (fun p -> match p with PostFalse -> true | _ -> false) sem.fsem_post

  method is_jni_function =
    match api.fapi_jni_index with Some _ -> true | _ -> false

  method is_api_inferred = api.fapi_inferred

  method toPretty = 
    let name = self#get_name in
    let nameLen = String.length name in
    let headLen = if nameLen < 80 then (80 - nameLen) / 2 else 0 in
    LBLOCK [ STR (string_repeat "=" headLen) ; STR " " ; STR name ; STR " " ;
	     STR (string_repeat "=" headLen) ; NL ;
	     STR doc.fdoc_desc ; NL ; doc.fdoc_apidoc ; NL ; NL ;
	     function_api_to_pretty api ; NL ; 
	     function_semantics_to_pretty sem ; NL ; 
	     STR (string_repeat "~" 80) ; NL ]
      
end
  
let make_function_summary
  ~(api:function_api_t)
  ~(sem:function_semantics_t)
  ~(doc:function_documentation_t):function_summary_int =
  new function_summary_t ~api ~sem ~doc


let read_xml_function_summary (node:xml_element_int) =
  let getc = node#getTaggedChild in
  let (api,sem) = read_xml_function_api_semantics (getc "api") (getc "semantics") in
  let doc = read_xml_function_documentation (getc "documentation") in
  make_function_summary ~api ~sem ~doc


let default_function_semantics = {
    fsem_pre = [] ;
    fsem_post = [] ;
    fsem_errorpost = [] ;
    fsem_sideeffects = [] ;
    fsem_io_actions = [] ;
    fsem_throws = [] ;
    fsem_desc = ""
}

let default_function_documentation = {
    fdoc_desc = "" ;
    fdoc_remarks = "" ;
    fdoc_caution = "" ;
    fdoc_apidoc = STR "" ;
    fdoc_xapidoc = xmlElement "apidoc" 
}

let default_summary name =
  let api = {
    fapi_name = name ;
    fapi_parameters = [] ;
    fapi_returntype = t_unknown ;
    fapi_rv_roles = [] ;
    fapi_stack_adjustment = None ;
    fapi_jni_index = None ;
    fapi_calling_convention = "cdecl"  ;
    fapi_inferred = true ;
    fapi_registers_preserved = []
  } in
  let sem = default_function_semantics in
  let doc = default_function_documentation in
  make_function_summary ~api ~sem ~doc

let join_semantics (sem:function_semantics_t) (optsem:function_semantics_t option) =
  match optsem with
  | Some s -> {
    fsem_pre = sem.fsem_pre @ s.fsem_pre ;
    fsem_post = sem.fsem_post @ s.fsem_post ;
    fsem_errorpost = sem.fsem_errorpost @ s.fsem_errorpost ;
    fsem_sideeffects = sem.fsem_sideeffects @ s.fsem_sideeffects ;
    fsem_io_actions = sem.fsem_io_actions @ s.fsem_io_actions ;
    fsem_throws = sem.fsem_throws @ s.fsem_throws ;
    fsem_desc = sem.fsem_desc ^ "; " ^ s.fsem_desc
    }
  | _ -> sem


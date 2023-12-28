(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open BCHBasicTypes
open BCHBCTypePretty
open BCHBCTypes
open BCHBCTypeUtil
open BCHBTerm
open BCHCallTarget
open BCHCPURegisters
open BCHDemangler
open BCHDoubleword
open BCHFtsParameter
open BCHFunctionInterface
open BCHFunctionSemantics
open BCHLibTypes
open BCHPostcondition
open BCHPrecondition
open BCHSideeffect
open BCHSystemSettings
open BCHTypeDefinitions
open BCHUtilities
open BCHXmlUtil


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


let make_xml_par_sideeffect (se: xxpredicate_t) (par: fts_parameter_t) =
  let is_par t = match t with
    | ArgValue a -> (fts_parameter_compare a par) = 0 | _ -> false in
  let btype_tgt_compare ty party = match party with
    | TPtr (t,_) -> (btype_compare ty t) = 0
    | _ -> false in
  let is_tsize t =
    match t with
    | ArgSizeOf bty -> btype_tgt_compare bty par.apar_type
    | _ -> false in
  match se with
  | XXBlockWrite (_, t, size) when is_par t && is_tsize size ->
     Some (xmlElement "block-write")
  | XXModified t when is_par t -> Some (xmlElement "modifies")
  | XXInvalidated t when is_par t -> Some (xmlElement "invalidates")
  | _ -> None


let write_xml_function_documentation
      (node:xml_element_int) (doc:function_documentation_t) =
  let append = node#appendChildren in
  let write_xml_text (tag: string) (s: string) =
    if s = "" then () else append [xml_string tag s] in
  begin
    write_xml_text "desc" doc.fdoc_desc;
    write_xml_text "remarks" doc.fdoc_remarks;
    write_xml_text "caution" doc.fdoc_caution;
    append [doc.fdoc_xapidoc]
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


let read_xml_function_documentation
      (node:xml_element_int):function_documentation_t =
  let getc = node#getTaggedChild in
  let hasc = node#hasOneTaggedChild in
  { fdoc_desc = if hasc "desc" then (getc "desc")#getText else "" ;
    fdoc_remarks = if hasc "remarks" then (getc "remarks")#getText else "" ;
    fdoc_caution = if hasc "caution" then (getc "caution")#getText else "" ;
    fdoc_apidoc = read_xml_apidoc (getc "apidoc") ;
    fdoc_xapidoc = getc "apidoc"
  }


class function_summary_t
  ~(fintf: function_interface_t)
  ~(sem: function_semantics_t)
  ~(doc: function_documentation_t): function_summary_int =
object (self:'a)

  val finterface = fintf
  val fts = fintf.fintf_type_signature
  val sem = sem
  val doc = doc

  method get_function_interface = finterface

  method get_function_signature = get_fintf_fts self#get_function_interface

  method get_function_semantics = sem

  method get_function_documentation = doc

  method get_name = get_fintf_name self#get_function_interface

  method get_parameters = get_fts_parameters self#get_function_interface

  method get_parameter_for_register (reg: register_t): fts_parameter_t =
    let rpar = get_register_parameter_for_register self#get_function_interface reg in
    match rpar with
    | Some p -> p
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Internal error: get_parameter_for_register"]))

  method get_parameter_at_stack_offset (offset: int): fts_parameter_t =
    let spar = get_stack_parameter_at_offset self#get_function_interface offset in
    match spar with
    | Some p -> p
    | _ ->
       raise
         (BCH_failure
            (LBLOCK [STR "Internal error: get_parameter_at_stack_offset"]))

  method get_returntype = get_fts_returntype self#get_function_interface

  method get_stack_adjustment =
    get_fts_stack_adjustment self#get_function_interface

  method set_returntype (ty: btype_t): 'a =
    let fintf = self#get_function_interface in
    {< finterface = set_function_interface_returntype fintf ty >}

  method add_stack_parameter_location (offset: int) (ty: btype_t) (size: int) =
    let fintf = self#get_function_interface in
    {< finterface = add_function_stack_parameter_location fintf offset ty size >}

  method add_register_parameter_location
           (reg: register_t) (ty: btype_t) (size: int) =
    let fintf = self#get_function_interface in
    let _ =
      chlog#add
        "add-register-parameter-location"
        (LBLOCK [
             STR (get_fintf_name self#get_function_interface);
             STR ": ";
             STR (register_to_string reg)]) in
    {< finterface = add_function_register_parameter_location fintf reg ty size >}

  method get_registers_preserved = fts.fts_registers_preserved

  method get_jni_index =
    match finterface.fintf_jni_index with
    | Some i -> i
    | _ ->
      begin
	ch_error_log#add
          "invocation error"
	  (LBLOCK [STR "function_summary#get_jni_index"]);
	raise (BCH_failure (LBLOCK [STR "function_summary#get_jni_index"]))
      end

  method get_syscall_index =
    match finterface.fintf_syscall_index with
    | Some i -> i
    | _ ->
       begin
         ch_error_log#add
           "invocation error"
           (LBLOCK [STR "function_summary#get_syscall_index"]);
         raise
           (BCH_failure (LBLOCK [STR "function_summary#get_syscall_index"]))
       end

  method get_preconditions = sem.fsem_pre

  method add_precondition (pre: xxpredicate_t): 'a =
    let fsem = self#get_function_semantics in
    {< sem = add_function_precondition fsem pre >}

  method get_postconditions = sem.fsem_post
  method get_errorpostconditions = sem.fsem_errorpost

  method get_postrequests = sem.fsem_postrequests

  method add_postrequest (pr: xxpredicate_t): 'a =
    let fsem = self#get_function_semantics in
    {< sem = add_function_postrequest fsem pr >}

  method get_sideeffects = sem.fsem_sideeffects

  method add_sideeffect (se: xxpredicate_t): 'a =
    let fsem = self#get_function_semantics in
    {< sem = add_function_sideeffect fsem se >}

  method get_io_actions = sem.fsem_io_actions

  method get_enums_referenced =
    let l = ref [] in
    let add s = if List.mem s !l then () else l := s :: !l in
    begin
      List.iter (fun p ->
          match p with
          | XXEnum (_, s, _) -> add s | _ -> ()) self#get_preconditions;
      List.iter (fun p ->
          match p with
          | XXEnum (_, s, _) -> add s | _ -> ()) self#get_postconditions;
      !l
    end

  method get_enum_type (par: fts_parameter_t) =
    List.fold_left (fun acc pre ->
      match acc with Some _ -> acc | _ ->
	match pre with
	| XXEnum (ArgValue p, s, flags) ->
	   if fts_parameter_compare p par = 0 then
             Some (t_named s, flags)
           else
             None
	| _ -> None) None self#get_preconditions

  method modify_types (name:string) (f:type_transformer_t) =
    {< finterface = modify_function_interface f name finterface;
       sem = modify_types_semantics f sem >}

  method has_unknown_sideeffects =
    List.exists
      (fun p ->
        match p with
        | XXBlockWrite (_, RunTimeValue, _) -> true
        | _ -> false)
      sem.fsem_sideeffects

  method sets_errno =
    List.exists (fun p -> match p with XXSetsErrno -> true | _ -> false)
      sem.fsem_sideeffects

  method is_nonreturning =
    List.exists
      (fun p -> match p with XXFalse -> true | _ -> false)
      sem.fsem_post

  method is_jni_function =
    match finterface.fintf_jni_index with Some _ -> true | _ -> false


  method write_xml (node: xml_element_int) =
    let fintf = xmlElement "fintf" in
    let fsem = xmlElement "sem" in
    begin
      write_xml_function_interface fintf self#get_function_interface;
      write_xml_function_semantics fsem self#get_function_semantics;
      node#appendChildren [fintf; fsem];
    end

  method toPretty =
    let name = self#get_name in
    let nameLen = String.length name in
    let headLen = if nameLen < 80 then (80 - nameLen) / 2 else 0 in
    LBLOCK [
        STR (string_repeat "=" headLen);
        STR " ";
        STR name;
        STR " ";
	STR (string_repeat "=" headLen); NL;
	STR doc.fdoc_desc; NL;
        doc.fdoc_apidoc; NL; NL;
	function_interface_to_pretty finterface; NL;
	function_semantics_to_pretty sem; NL;
	STR (string_repeat "~" 80); NL]

end


let make_function_summary
  ~(fintf: function_interface_t)
  ~(sem: function_semantics_t)
  ~(doc: function_documentation_t): function_summary_int =
  new function_summary_t ~fintf ~sem ~doc


let default_function_documentation = {
    fdoc_desc = "";
    fdoc_remarks = "";
    fdoc_caution = "";
    fdoc_apidoc = STR "";
    fdoc_xapidoc = xmlElement "apidoc"
  }


let function_summary_of_bvarinfo (vinfo: bvarinfo_t): function_summary_int =
  let fintf = bvarinfo_to_function_interface vinfo in
  make_function_summary
    ~fintf
    ~sem:default_function_semantics
    ~doc:default_function_documentation


let read_xml_function_summary (node:xml_element_int) =
  let getc = node#getTaggedChild in
  let (fintf, sem) =
    read_xml_function_interface_and_semantics
      (getc "api")
      (getc "semantics") in
  let doc = read_xml_function_documentation (getc "documentation") in
  make_function_summary ~fintf ~sem ~doc


let default_summary name =
  let fintf = default_function_interface ~cc:"cdecl" name in
  let sem = default_function_semantics in
  let doc = default_function_documentation in
  make_function_summary ~fintf ~sem ~doc

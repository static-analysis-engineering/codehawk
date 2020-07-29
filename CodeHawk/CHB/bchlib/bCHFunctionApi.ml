(* =============================================================================
   CodeHawk Binary Analyzer 
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
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHApiParameter
open BCHCPURegisters
open BCHLibTypes
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

(* ----------------------------------------------------------------- printing *)

let function_api_to_prototype_string ?(fullname=None) (api:function_api_t) =
  let name = match fullname with Some n -> n | _ -> api.fapi_name in
  let stackPars = List.fold_left (fun a p ->
    match p.apar_location with 
    | StackParameter i -> (i,p.apar_name,p.apar_type)::a
    | _ -> a) [] api.fapi_parameters in
  let stackPars =
    List.sort (fun (i1,_,_) (i2,_,_) -> P.compare i1 i2) stackPars in
  let par_string (_,name,ty) = (btype_to_string ty) ^ " " ^ name in
  (btype_to_string api.fapi_returntype) ^ " " ^
    name ^ "(" ^ 
    (String.concat ", " (List.map par_string stackPars)) ^ ")"

let function_api_to_pretty (api:function_api_t) =
  LBLOCK [ STR api.fapi_name ;
           STR ": " ; btype_to_pretty api.fapi_returntype ; NL ;
	   INDENT (3, LBLOCK [ pretty_print_list api.fapi_parameters 
	     (fun p -> LBLOCK [ api_parameter_to_pretty p ; NL ]) "" "" "" ]) ]


(* --------------------------------------------------------------- comparison *)

let function_api_compare (api1:function_api_t) (api2:function_api_t) =
  let l1 = P.compare api1.fapi_name api2.fapi_name in
  if l1 = 0 then
    let l2 =
      list_compare
        api1.fapi_parameters api2.fapi_parameters api_parameter_compare in
    if l2 = 0 then
      btype_compare api1.fapi_returntype api2.fapi_returntype
    else l2
  else l1


(* ----------------------------------------------------------------- read xml *)

let read_xml_registers_preserved (node:xml_element_int) =
  List.map (fun n ->
    let get = n#getAttribute in
    (register_from_string (get "name"))) (node#getTaggedChildren "reg")

let get_stack_adjustment (calling_convention:string) (npars:int) =
  match calling_convention with
  | "stdcall" -> 4 * npars
  | "cdecl" -> 0
  | s -> raise (BCH_failure (LBLOCK [ STR "calling convention " ; STR s ;
				      STR " not recognized" ]))

let read_xml_function_api (node:xml_element_int):function_api_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let getcc = node#getTaggedChildren in
  let hasc = node#hasOneTaggedChild in
  let parameters = List.map read_xml_api_parameter (getcc "par") in
  let varargs = has "varargs" && ((get "varargs") = "yes") in
  let cc = get "cc" in
  let stackadj = if cc = "stdcall" || cc = "cdecl" then
      Some (get_stack_adjustment cc (List.length parameters))
    else
      None in
  let find l default = 
    List.fold_left (fun acc s -> 
      if hasc s then read_xml_returntype (getc s) else acc) default l in
  { fapi_name = get "name" ;
    fapi_parameters = parameters ;
    fapi_varargs = varargs ;
    fapi_va_list = None ;
    fapi_returntype = find [ "returntype" ; "returnbtype" ] t_void ;
    fapi_rv_roles =
      (if hasc "rv-roles" then read_xml_roles (getc "rv-roles") else []) ;
    fapi_calling_convention = cc ;
    fapi_inferred = (has "inferred" && (get "inferred") = "yes") ;
    fapi_jni_index = if has "jni" then Some (geti "jni") else None ;
    fapi_stack_adjustment = if has "adj" then Some (geti "adj") else stackadj ;
    fapi_registers_preserved = if hasc "registers-preserved" then
	read_xml_registers_preserved (getc "registers-preserved") else []
}

  
(* ---------------------------------------------------------------- operators *)

let modify_types_api (f:type_transformer_t) (name:string) (api:function_api_t) =
  { api with
    fapi_name = name ;
    fapi_parameters = List.map (modify_types_par f) api.fapi_parameters ;
    fapi_returntype = modify_type f api.fapi_returntype
  }

let get_stack_parameter (api:function_api_t) (index:int) =
  try
    List.find (fun p -> match p.apar_location with
    | StackParameter n -> n = index | _ -> false) api.fapi_parameters 
  with
    Not_found ->
      raise (BCH_failure
	       (LBLOCK [ STR "No stack parameter found with index: " ;
                         INT index ]))

let get_stack_parameter_name (api:function_api_t) (index:int) =
  (get_stack_parameter api index).apar_name

let get_stack_parameter_names (api:function_api_t) =
  List.sort (fun (i1,_) (i2,_) -> P.compare i1 i2)
    (List.fold_left (fun acc p ->
      match p.apar_location with
      | StackParameter i -> (i,p.apar_name) :: acc
      | _ -> acc) [] api.fapi_parameters)

let get_stack_parameter_count (api:function_api_t) =
  List.length (List.filter (fun p -> match p.apar_location with 
  | StackParameter _ -> true | _ -> false) api.fapi_parameters)

let is_stack_parameter (p:api_parameter_t) (n:int) =
  match p.apar_location with
  | StackParameter i -> i = n
  | _ -> false

let has_fmt_parameter (api:function_api_t) =
  List.exists is_formatstring_parameter api.fapi_parameters

let get_fmt_parameter_index (api:function_api_t) =
  let (result,_) =
    List.fold_left
      (fun (acc,c) p ->
        match acc with
        | Some _ -> (acc,0)
        | _ ->
           if is_formatstring_parameter p then (Some c,0) else (None,c+1))
      (None,0) api.fapi_parameters in
  match result with
  | Some c -> c
  | _ ->
     raise (BCH_failure
              (LBLOCK [ STR "no format argument found in function api" ]))

let demangled_name_to_function_api (dm:demangled_name_t) = 
  let stack_adjustment = match dm.dm_calling_convention with
    | "__cdecl" -> Some 0
    | "__thiscall"
    | "__stdcall" -> Some (4 * (List.length dm.dm_parameter_types))
    | _ -> None in
  let returntype =
    match dm.dm_returntype with Some t -> t | _ -> t_void in
  let make_parameter index ty = {
    apar_name = make_name_from_type ty (index + 1) ;
    apar_type = ty ;
    apar_desc = "" ;
    apar_roles = [] ;
    apar_io = ArgReadWrite ;
    apar_location = StackParameter (index + 1) ;
    apar_size = (match (get_size_of_btype ty) with Some s -> s | _ -> 4) ;
    apar_fmt = NoFormat
  } in
  { fapi_name = tname_to_string dm.dm_name ;
    fapi_parameters = List.mapi make_parameter dm.dm_parameter_types ;
    fapi_varargs = false ;   (* TBD: to be investigated *)
    fapi_va_list = None ;
    fapi_returntype = returntype ;
    fapi_rv_roles = [] ;
    fapi_stack_adjustment = stack_adjustment ;
    fapi_jni_index = None ;
    fapi_calling_convention = dm.dm_calling_convention ;
    fapi_inferred = false ;
    fapi_registers_preserved = []
  }

let default_function_api 
      ?(cc="cdecl")
      ?(adj=0)
      ?(returntype=t_unknown)
      (name:string)
      (pars:api_parameter_t list) =
  {
    fapi_name = name ;
    fapi_parameters = pars ;
    fapi_varargs = false ;
    fapi_va_list = None ;
    fapi_returntype = t_unknown ;
    fapi_rv_roles = [] ;
    fapi_stack_adjustment = Some adj ;
    fapi_jni_index = None ;
    fapi_calling_convention = cc ;
    fapi_registers_preserved = [] ;
    fapi_inferred = false
  }

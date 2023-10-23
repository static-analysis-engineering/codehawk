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
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHBCTypes
open BCHCPURegisters
open BCHFtsParameter
open BCHInterfaceDictionary
open BCHLibTypes
open BCHUtilities
open BCHVariableType
open BCHXmlUtil


let id = BCHInterfaceDictionary.interface_dictionary


let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

(* ----------------------------------------------------------------- printing *)

let function_interface_to_prototype_string
      ?(fullname=None) (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  let name =
    match fullname with
    | Some n -> n
    | _ -> fintf.fintf_name in
  let stackPars = List.fold_left (fun a p ->
    match p.apar_location with 
    | StackParameter i -> (i,p.apar_name,p.apar_type)::a
    | _ -> a) [] fts.fts_parameters in
  let stackPars =
    List.sort (fun (i1,_,_) (i2,_,_) -> Stdlib.compare i1 i2) stackPars in
  let par_string (_,name,ty) = (btype_to_string ty) ^ " " ^ name in
  (btype_to_string fts.fts_returntype)
  ^ " "
  ^ name
  ^ "("
  ^ (String.concat ", " (List.map par_string stackPars))
  ^ ")"

let function_interface_to_pretty (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  LBLOCK [
      STR fintf.fintf_name ;
      STR ": ";
      btype_to_pretty fts.fts_returntype;
      NL;
      INDENT (
          3,
          LBLOCK [pretty_print_list fts.fts_parameters 
	            (fun p ->
                      LBLOCK [
                          fts_parameter_to_pretty p; NL])
                    "" "" "" ])]

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

let read_xml_function_interface (node:xml_element_int):function_interface_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let getcc = node#getTaggedChildren in
  let hasc = node#hasOneTaggedChild in
  let parameters = List.map read_xml_fts_parameter (getcc "par") in
  let varargs = has "varargs" && ((get "varargs") = "yes") in
  let cc = get "cc" in
  let stackadj = if cc = "stdcall" || cc = "cdecl" then
      Some (get_stack_adjustment cc (List.length parameters))
    else
      None in
  let find l default = 
    List.fold_left (fun acc s -> 
        if hasc s then read_xml_returntype (getc s) else acc) default l in
  let fts = {
      fts_parameters = parameters;
      fts_varargs = varargs;
      fts_va_list = None;
      fts_returntype = find ["returntype"; "returnbtype"] t_void;
      fts_rv_roles =
        (if hasc "rv-roles" then read_xml_roles (getc "rv-roles") else []);
      fts_calling_convention = cc;
      fts_stack_adjustment = if has "adj" then Some (geti "adj") else stackadj;
      fts_registers_preserved =
        if hasc "registers-preserved" then
          read_xml_registers_preserved (getc "registers-preserved")
        else
          []
    } in
  { fintf_name = get "name";
    fintf_jni_index = if has "jni" then Some (geti "jni") else None;
    fintf_syscall_index = if has "syscall" then Some (geti "syscall") else None;
    fintf_type_signature = fts
  }


let write_xml_function_interface
      (node: xml_element_int) (fintf: function_interface_t) =
  id#write_xml_function_interface node fintf
  
(* ---------------------------------------------------------------- operators *)

let modify_function_interface
      (f: type_transformer_t) (name: string) (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  let newfts = {
      fts with
      fts_parameters = List.map (modify_types_par f) fts.fts_parameters;
      fts_returntype = modify_type f fts.fts_returntype
    } in
  { fintf with
    fintf_name = name ;
    fintf_type_signature = newfts
  }

let get_stack_parameter (fintf: function_interface_t) (index:int) =
  let fts = fintf.fintf_type_signature in
  try
    List.find (fun p ->
        match p.apar_location with
        | StackParameter n -> n = index
        | _ -> false) fts.fts_parameters 
  with
    Not_found ->
      raise (BCH_failure
	       (LBLOCK [
                    STR "No stack parameter found with index: ";
                    INT index]))

let get_stack_parameter_name (fintf: function_interface_t) (index:int) =
  (get_stack_parameter fintf index).apar_name


let get_stack_parameter_names (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2)
    (List.fold_left (fun acc p ->
      match p.apar_location with
      | StackParameter i -> (i,p.apar_name) :: acc
      | _ -> acc) [] fts.fts_parameters)


let get_stack_parameter_count (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  List.length (List.filter (fun p -> match p.apar_location with 
  | StackParameter _ -> true | _ -> false) fts.fts_parameters)


let is_stack_parameter (p: fts_parameter_t) (n: int) =
  match p.apar_location with
  | StackParameter i -> i = n
  | _ -> false


let has_fmt_parameter (fintf: function_interface_t) =
  List.exists is_formatstring_parameter fintf.fintf_type_signature.fts_parameters


let get_fmt_parameter_index (fintf: function_interface_t) =
  let fts = fintf.fintf_type_signature in
  let (result,_) =
    List.fold_left
      (fun (acc,c) p ->
        match acc with
        | Some _ -> (acc,0)
        | _ ->
           if is_formatstring_parameter p then (Some c, 0) else (None, c+1))
      (None, 0) fts.fts_parameters in
  match result with
  | Some c -> c
  | _ ->
     raise (BCH_failure
              (LBLOCK [STR "no format argument found in function signature"]))


let demangled_name_to_function_interface (dm: demangled_name_t) = 
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
  let fts =
    { fts_parameters = List.mapi make_parameter dm.dm_parameter_types;
      fts_varargs = false;   (* TBD: to be investigated *)
      fts_va_list = None;
      fts_returntype = returntype;
      fts_rv_roles = [];
      fts_stack_adjustment = stack_adjustment;
      fts_calling_convention = dm.dm_calling_convention;
      fts_registers_preserved = []
    } in
  {
    fintf_name = tname_to_string dm.dm_name;
    fintf_jni_index = None;
    fintf_syscall_index = None;
    fintf_type_signature = fts
  }

let default_function_interface 
      ?(cc="cdecl")
      ?(adj=0)
      ?(returntype=t_unknown)
      (name:string)
      (pars: fts_parameter_t list) =
  let fts = {
      fts_parameters = pars;
      fts_varargs = false;
      fts_va_list = None;
      fts_returntype = returntype;
      fts_rv_roles = [];
      fts_stack_adjustment = Some adj;
      fts_calling_convention = cc;
      fts_registers_preserved = [];
    } in
  {
    fintf_name = name;
    fintf_jni_index = None;
    fintf_syscall_index = None;
    fintf_type_signature = fts
  }
                       

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
open CHFormatStringParser
open CHLogger
open CHXmlDocument
open CHXmlReader

(* bchlib *)
open BCHBasicTypes
open BCHCPURegisters
open BCHDoubleword
open BCHLibTypes
open BCHUtilities
open BCHVariableType
open BCHVariableTypeUtil
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

(* ------------------------------------------------------------------- printing *)

let calling_convention_to_string = function StdCall -> "stdcall" | CDecl -> "cdecl"

let arg_io_to_string (i:arg_io_t) =
  match i with
  | ArgRead -> "r"
  | ArgWrite -> "w"
  | ArgReadWrite -> "rw"

let formatstring_type_to_string (t:formatstring_type_t) =
  match t with
  | NoFormat -> "no"
  | PrintFormat -> "print"
  | ScanFormat -> "scan"

let parameter_location_to_string = function
  | StackParameter i -> "s_arg " ^ (string_of_int i)
  | RegisterParameter r -> "r_arg " ^ (register_to_string r)
  | GlobalParameter g -> "g_arg " ^ g#to_hex_string
  | UnknownParameterLocation -> "unknown"

let api_parameter_to_pretty (p:api_parameter_t) =
  LBLOCK [ STR p.apar_name ; STR ": " ; btype_to_pretty p.apar_type ]

(* ----------------------------------------------------------------- comparison *)

let parameter_location_compare l1 l2 =
  match (l1,l2) with
  | (StackParameter i1, StackParameter i2) -> P.compare i1 i2
  | (StackParameter _, _) -> -1
  | (_, StackParameter _) -> 1
  | (RegisterParameter r1, RegisterParameter r2) -> P.compare r1 r2
  | (RegisterParameter _, _) -> -1
  | (_, RegisterParameter _) -> 1
  | (GlobalParameter dw1, GlobalParameter dw2) -> dw1#compare dw2
  | (GlobalParameter _, _) -> -1
  | (_, GlobalParameter _) -> 1
  | (UnknownParameterLocation, UnknownParameterLocation) -> 0 

let api_parameter_compare (p1:api_parameter_t) (p2:api_parameter_t) =
  parameter_location_compare p1.apar_location p2.apar_location


(* ------------------------------------------------------------------ write xml *)

let write_xml_parameter_location (node:xml_element_int) (loc:parameter_location_t) =
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  match loc with
  | StackParameter index -> 
    begin set "loc" "stack" ; seti "nr" index end
  | RegisterParameter reg ->
    begin set "loc" "register" ; set "reg" (register_to_string reg) end
  | GlobalParameter dw ->
    begin set "loc" "global" ; set "dw" dw#to_hex_string end
  | UnknownParameterLocation -> ()

let write_xml_roles (node:xml_element_int) (l:(string * string) list) =
  node#appendChildren (List.map (fun (rtype,rname) ->
    let rNode = xmlElement "role" in
    let set = rNode#setAttribute in
    begin set "rt" rtype ; set "rn" rname ; rNode end) l)


let write_xml_api_parameter (node:xml_element_int) (p:api_parameter_t) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let tNode = xmlElement "btype" in
  begin
    write_xml_btype tNode p.apar_type ;
    write_xml_parameter_location node p.apar_location ;
    append [ tNode ] ;
    (match p.apar_roles with [] -> () | l ->
      let rrNode = xmlElement "roles" in 
      begin write_xml_roles rrNode l ; append [ rrNode ] end) ;
    (match p.apar_desc with "" -> () | s -> set "desc" s) ;
    set "io" (arg_io_to_string p.apar_io) ;
    set "name" p.apar_name ;
    seti "size" p.apar_size ;
    set "fmt" (formatstring_type_to_string p.apar_fmt)
  end

(* ----------------------------------------------------------------- read xml *)

let read_xml_arg_io (s:string) =
  match s with
  | "r" -> ArgRead
  | "w" -> ArgWrite
  | "rw" -> ArgReadWrite
  | _ -> raise (BCH_failure (LBLOCK [ STR "Arg io " ; STR s ; STR " not recognized" ]))

let read_xml_formatstring_type (s:string) =
  match s with
  | "no" -> NoFormat
  | "print" -> PrintFormat
  | "scan" -> ScanFormat
  | _ ->
     raise
       (BCH_failure
          (LBLOCK [ STR "Formatstring type " ; STR s ; STR " not recognized" ]))

let read_xml_roles (node:xml_element_int) =
  List.map (fun n -> 
    let get = n#getAttribute in (get "rt", get "rn")) (node#getTaggedChildren "role")

let read_xml_parameter_location (node:xml_element_int):parameter_location_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  match get "loc" with
  | "stack" -> StackParameter (geti "nr") 
  | "register" -> RegisterParameter (register_from_string (get "reg"))
  | "global" -> GlobalParameter (string_to_doubleword (get "dw"))
  | "unknown" -> UnknownParameterLocation
  | s -> raise_xml_error node (LBLOCK [ STR "Parameter location not recognized: " ; STR s ])

(* Api parameters are numbered with two attributes:
   - nr : stack position (times 4, starting at 1)
   - ix : argument index number
   If ix is missing, it is assumed that the ix is the same as nr
*)
let read_xml_api_parameter (node:xml_element_int):api_parameter_t =
  let get = node#getAttribute in
  let geti = node#getIntAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  let hasc = node#hasOneTaggedChild in 
  let tNode = if hasc "type" then getc "type" else getc "btype" in
  { apar_name = get "name" ;
    apar_desc = (if has "desc" then get "desc" else "") ;
    apar_roles = (if hasc "roles" then read_xml_roles (getc "roles") else []) ;
    apar_io = (if has "io" then read_xml_arg_io (get "io") else ArgReadWrite) ;
    apar_size = (if has "size" then geti "size" else 4) ;
    apar_type = read_xml_type tNode ;
    apar_location = read_xml_parameter_location node ;
    apar_fmt =
      (if has "fmt" then read_xml_formatstring_type (get "fmt") else NoFormat)
  }

(* --------------------------------------------------------------- predicates *)

let is_global_parameter (p:api_parameter_t) =
  match p.apar_location with GlobalParameter _ -> true | _ -> false

let is_stack_parameter (p:api_parameter_t) =
  match p.apar_location with StackParameter _ -> true | _ -> false

let is_register_parameter (p:api_parameter_t) =
  match p.apar_location with RegisterParameter _ -> true | _ -> false

let is_arg_parameter (p:api_parameter_t) =
  is_register_parameter p || is_stack_parameter p

let is_formatstring_parameter (p:api_parameter_t) =
  match p.apar_fmt with
  | NoFormat -> false
  | _ -> true

(* ---------------------------------------------------------------- operators *)

let default_api_parameter = {
  apar_name = "unnknown-api-parameter" ;
  apar_type = t_unknown ;
  apar_roles = [] ;
  apar_desc = "" ;
  apar_io = ArgReadWrite;
  apar_size = 4 ;
  apar_location = UnknownParameterLocation ;
  apar_fmt = NoFormat
}

let modify_types_par (f:type_transformer_t) (p:api_parameter_t) =
  { p with apar_type = modify_type f p.apar_type }

let modify_name_par (name:string) (p:api_parameter_t) =
  { p with apar_name = name }

let mk_global_parameter
      ?(btype=t_unknown)
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      ?(fmt=NoFormat)
      (gaddr:doubleword_int) =
  {  apar_name = "gv_" ^ gaddr#to_hex_string ;
     apar_type = btype ;
     apar_desc = desc ;
     apar_roles = roles ;
     apar_io = io ;
     apar_size = size ;
     apar_location = GlobalParameter gaddr ;
     apar_fmt = fmt
  }

let mk_stack_parameter
      ?(btype=t_unknown)
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      ?(fmt=NoFormat)
      (arg_index:int) =
  { apar_name = "arg_" ^ (string_of_int arg_index) ;
    apar_type = btype ;
    apar_desc = desc ;
    apar_roles = roles ;
    apar_io = io ;
    apar_size = size ;
    apar_fmt = fmt ;
    apar_location = StackParameter arg_index
  }

let mk_register_parameter
      ?(btype=t_unknown)
      ?(desc="")
      ?(roles=[])
      ?(io=ArgReadWrite)
      ?(size=4)
      ?(fmt=NoFormat)
      (reg:register_t) =
  { apar_name = "reg_" ^ (register_to_string reg) ;
    apar_type = btype ;
    apar_desc = desc ;
    apar_roles = roles ;
    apar_io = io ;
    apar_size = size ;
    apar_fmt = fmt ;
    apar_location = RegisterParameter reg
  }

(* Convert a format string specification to an api_parameter *)
let convert_fmt_spec_arg
      (index:int)         (* index of argument, zero-based *)
      (spec:argspec_int):api_parameter_t =
  { apar_name = "vararg_" ^ (string_of_int index);
    apar_type = get_fmt_spec_type spec;
    apar_desc = "vararg";
    apar_roles = [];
    apar_io =
      (match spec#get_conversion with
      | OutputArgument -> ArgWrite
      | _ -> ArgRead);
    apar_fmt = NoFormat;
    apar_size = 4;
    apar_location = StackParameter index
  }

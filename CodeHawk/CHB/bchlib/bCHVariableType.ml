(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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
open CHCommon
open CHLanguage

(* chutil *)
open CHFileIO
open CHLogger
open CHPrettyUtil
open CHXmlDocument

(* xprlib *)
open Xprt

(* bchcil *)
open BCHBCFiles
open BCHBCSumTypeSerializer
open BCHBCUtil
open BCHCBasicTypes
open BCHCTypeUtil

(* bchlib *)
open BCHBasicTypes
(* open BCHLibTypes *)
open BCHXmlUtil

module H = Hashtbl


let raise_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [
        STR "(";
        INT node#getLineNumber;
        STR ",";
	INT node#getColumnNumber;
        STR ") ";
        msg] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end


let ikind_type_size = BCHCTypeUtil.ikind_type_size


let get_ikind_from_size ?(signed=true) (size:int) =
  match size with
  | 1 -> if signed then ISChar else IUChar
  | 2 -> if signed then IShort else IUShort
  | 4 -> if signed then IInt else IUInt
  | 8 -> if signed then ILongLong else IULongLong
  | _ -> INonStandard (signed,size)


let fkind_type_size = BCHCTypeUtil.fkind_type_size


let resolve_type = BCHCTypeUtil.resolve_type


let get_compinfo_by_key (key: int): bcompinfo_t =
  bcfiles#get_compinfo key


let get_struct_extractor (ty: btype_t): string list =
  match resolve_type ty with
  | TPtr (TPtr (TComp (ckey, _), _), _)
  | TPtr (TComp (ckey, _), _) ->
     let compinfo = get_compinfo_by_key ckey in
     List.map (fun f ->
         match f.bftype with
         | TInt _ -> "value"
         | TPtr (TInt _, _) -> "string"
         | TPtr (TFun _, _) -> "address"
         | _ -> "unknown") compinfo.bcfields

  | rty -> [btype_to_string ty; btype_to_string rty]


let get_struct_offset_extractor (ty: btype_t): (int * string) list =
  match resolve_type ty with
  | TPtr (TPtr (TComp (ckey, _), _), _)
    | TPtr (TComp (ckey, _), _) ->
     let compinfo = get_compinfo_by_key ckey in
     List.map (fun f ->
         match f.bfieldlayout with
         | Some (offset, _) ->
            (match f.bftype with
             | TInt _ -> (offset, "value")
             | TPtr (TInt _, _) -> (offset, "string-address")
             | TArray (TInt _, _, _) -> (offset, "string")
             | _ -> (offset, "unknown"))
         | _ ->
            raise
              (BCH_failure
                 (LBLOCK [
                      STR "Struct definition has no field layout: ";
                      STR (btype_to_string ty)]))) compinfo.bcfields
  | rty -> [(0, btype_to_string ty)]


(* Common types and type constructors *)

let t_unknown = TUnknown []
let t_void = TVoid []
let t_vararg = TVarArg []

let t_char = TInt (IChar, [])
let t_uchar = TInt (IUChar, [])
let t_wchar = TInt (IWChar, [])

let t_short = TInt (IShort, [])
let t_int = TInt (IInt, [])
let t_uint = TInt (IUInt, [])
let t_long = TInt (ILong, [])

let t_float = TFloat (FFloat,FScalar, [])
let t_double = TFloat (FDouble,FScalar, [])

let t_named name = TNamed (name, [])

let to_tname s = SimpleName s


let t_comp ?(name_space=[]) name =
  TCppComp (to_tname name, List.map to_tname name_space, [])


let t_enum ?(name_space=[]) name =
  TCppEnum (to_tname name, List.map to_tname name_space, [])


let t_class ?(name_space=[]) name =
  BCHCBasicTypes.TClass (to_tname name, List.map to_tname name_space, [])


let t_tcomp ?(name_space=[]) name = TCppComp (name, name_space, [])


let t_tenum ?(name_space=[]) name = TCppEnum (name, name_space, [])


let t_tclass ?(name_space=[]) name =
  BCHCBasicTypes.TClass (name, name_space, [])

let t_function (returntype:btype_t) (args:bfunarg_t list) =
  TFun (returntype, Some args, false, [])

let t_vararg_function (returntype:btype_t) (args:bfunarg_t list) =
  TFun (returntype, Some args, true, [])

let t_function_anon (returntype:btype_t) =
  TFun (returntype, None, false, [])

let t_voidptr = TPtr (TVoid [], [])


let t_refto t = TRef (t,[])
let t_ptrto t = TPtr (t,[])

let is_void t = match t with TVoid _ -> true | _ -> false

let is_pointer t = match t with TPtr _ -> true | _ -> false

let is_pointer_to_struct t = match t with TPtr (TComp _,_) -> true | _ -> false

let is_function_type t =
  match t with TFun _ | TPtr (TFun _,_) -> true | _ -> false

let is_unknown_type t = match t with TUnknown _ -> true | _ -> false

let is_known_type t = match t with TUnknown _ -> false | _ -> true

let is_unsigned t = match t with 
  | TInt (ik,_) ->
    begin
      match ik with
      |  IUChar | IUInt | IUShort | IULong | IULongLong -> true
      | _ -> false
    end

  | _ -> false


let t_add_attr (t:btype_t) (a:string) =
  let add l = (Attr (a, [])) :: l in
  match t with
  | TVoid attrs -> TVoid (add attrs)
  | TInt (ik, attrs) -> TInt (ik, add attrs)
  | TFloat (fk, rep, attrs) -> TFloat (fk, rep, add attrs)
  | TPtr (tt, attrs) -> TPtr (tt, add attrs)
  | TRef (tt, attrs) -> TRef (tt, add attrs)
  | THandle (s, attrs) -> THandle (s, add attrs)
  | TArray (tt, e, attrs) -> TArray (tt, e, add attrs)
  | TFun (tt, args, v, attrs) -> TFun (tt, args, v, add attrs)
  | TNamed (s, attrs) -> TNamed (s, add attrs)
  | TComp (ckey, attrs) -> TComp (ckey, add attrs)
  | TCppComp (tn, tns, attrs) -> TCppComp (tn, tns, add attrs)
  | TEnum (ename, attrs) -> TEnum (ename, add attrs)
  | TCppEnum (tn, tns, attrs) -> TCppEnum (tn, tns, add attrs)
  | TVarArg attrs -> TVarArg (add attrs)
  | TBuiltin_va_list attrs -> TBuiltin_va_list (add attrs)
  | TClass (s, ns, attrs) -> TClass (s, ns, add attrs)
  | TUnknown attrs -> TUnknown (add attrs)


let make_name_from_type ty index =
  let rec tn_string tn =
    match tn with 
    | SimpleName name -> name 
    | TemplatedName (base,_) -> "t" ^ (tn_string base) in
  let rec aux t = 
    match t with
    | TVoid _ -> "void"
    | TInt _ -> "i"
    | TFloat _ -> "f"
    | TPtr (t,_) -> "p" ^ (aux t)
    | TRef (t,_) -> "r" ^ (aux t)
    | THandle (s,_) -> "h" ^ s
    | TArray (t,_,_) -> "a" ^ (aux t)
    | TFun _ -> "fp"
    | TNamed (s,_) -> s
    | TComp (ckey, _) -> "struct" ^ (string_of_int ckey)
    | TCppComp (tn, _, _) -> "cpp-struct" ^ (tn_string tn)
    | TEnum (ename, _) -> "enum" ^ ename
    | TCppEnum (tn, _, _) -> "cpp-enum" ^ (tn_string tn)
    | TVarArg _ -> "vararg"
    | TBuiltin_va_list _ -> "builtin-va-list"
    | TClass (tn, _, _) -> "class" ^ (tn_string tn)
    | TUnknown _ -> "arg" in
  (aux ty) ^ "_" ^ (string_of_int index)


let tname_to_string = BCHBCUtil.tname_to_string
let btype_to_string = BCHBCUtil.btype_to_string
let btype_to_pretty = BCHBCUtil.btype_to_pretty
let btype_compare = BCHBCUtil.typ_compare


let get_size_of_ikind (i: ikind_t) = ikind_type_size i


let get_size_of_fkind (f: fkind_t) = fkind_type_size f


let get_size_of_btype (t: btype_t) =
  let baseSize = Some 4 in
  match t with
  | TInt (i,_) -> Some (get_size_of_ikind i)
  | TFloat (f,_,_) -> Some (get_size_of_fkind f)
  | TPtr _ | TRef _ | THandle _ | TFun _ -> baseSize
  | _ -> None


let rec modify_type (f: type_transformer_t) (t: btype_t) =
  let rec tf tname =
    match tname with
    | SimpleName name -> SimpleName (f name)
    | TemplatedName (base,args) ->
      TemplatedName (tf base,List.map (fun a -> modify_type f a) args) in
  match t with
  | TPtr (tt,attrs) -> TPtr (modify_type f tt,attrs)
  | TRef (tt,attrs) -> TRef (modify_type f tt,attrs)
  | TArray (tt,e,attrs) -> TArray (modify_type f tt, e, attrs)
  | TFun (tt,optArgs,b,attrs) ->
    TFun (modify_type f tt, modify_type_optargs f optArgs, b, attrs)
  | TNamed (s,attrs) -> TNamed (f s,attrs)
  | TComp (ckey, attrs) -> TComp (ckey, attrs)
  | TCppComp (tname, ns, attrs) ->
     TCppComp (tf tname, List.map tf ns, attrs)
  | _ -> t


and modify_type_optargs (f: type_transformer_t) (args: bfunarg_t list option) =
  match args with
  | Some l -> Some (List.map (fun (s, t, a) -> (s, modify_type f t, a)) l)
  | _ -> None


(* To be reimplemented ------------------------
let get_struct_field_enums (cinfo: bcompinfo_t) =
  List.fold_left (fun acc fld ->
    match fld.bfenum with Some (s,_) -> s::acc | _ -> acc) [] cinfo.bcfields
*)

exception Invalid_enumeration of string * string


let read_xml_summary_type (node: xml_element_int): btype_t =
  let rec aux n =
    if n#hasText then 
      TNamed (n#getText,[])
    else
      let nn = n#getChild in
      match nn#getTag with
      | "ptr" -> TPtr (aux nn,[])
      | "array" -> 
	 let size =
           if nn#hasNamedAttribute "size" then
	     Some
               (Const
                  (CInt64 (Int64.of_string (nn#getAttribute "size"), IInt, None)))
	  else
	    None in
	TArray (aux nn, size,[])
      | "vararg" -> TVarArg []
      | "struct" -> t_named (nn#getAttribute "name")
      | s ->
	raise_error node 
	  (LBLOCK [ STR s ; STR " not recognized as a summary type" ]) in
  aux node

let compinfo_key = ref 10000
let new_compinfo_key () =
  begin
    compinfo_key := !compinfo_key + 1;
    !compinfo_key
  end


let read_xml_summary_fieldinfo
      (ckey: int) (node: xml_element_int) : bfieldinfo_t =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let geti = node#getIntAttribute in
  let tNode = getc "type" in
  {
    bfckey = ckey;
    bfname = get "name";
    bftype = read_xml_summary_type tNode;
    bfbitfield = None;
    bfattr = [];
    bfloc = {line = 0; file = ""; byte = 0};
    bfieldlayout =
      if has "offset" && has "size" then
        Some (geti "offset", geti "size")
      else
        None
  }


let read_xml_summary_struct (node: xml_element_int): bcompinfo_t =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let ckey = new_compinfo_key () in
  {
    bcname = get "name";
    bckey = ckey;
    bcstruct = true;
    bcfields =
      List.map
        (read_xml_summary_fieldinfo ckey)
        ((getc "fields")#getTaggedChildren "field");
    bcattr = []
  }


let read_xml_int64 (node: xml_element_int): int64 =
  Int64.of_string (node#getAttribute "intValue")


let write_xml_int64_element (node: xml_element_int) (i :int64) =
  node#setAttribute "intValue" (Int64.to_string i)


let read_xml_int64_list (node: xml_element_int): int64 list =
  List.map read_xml_int64 (node#getTaggedChildren "int")


let write_xml_int64_list (node: xml_element_int) (l: int64 list) =
  node#appendChildren
    (List.map (fun i ->
         let inode = xmlElement "int" in
         begin write_xml_int64_element inode i; inode end) l)


let read_xml_restricted_btype (node: xml_element_int): btype_t =
  let get = node#getAttribute in
  match get "ttag" with
  | "tvoid" -> TVoid []
  | "tint" -> TInt (ikind_mfts#fs (get "ikind"), [])
  | "tnamed" -> TNamed (get "tname", [])
  | s -> raise_error node (LBLOCK [STR s; STR " no recognized as type tag"])


let read_xml_type (node: xml_element_int) =
  if node#getTag = "btype" || node#getTag = "typ" then 
    read_xml_restricted_btype node 
  else 
    read_xml_summary_type node


and read_xml_returntype (node: xml_element_int) =
  if node#getTag = "returnbtype" then
    read_xml_restricted_btype node
  else
    read_xml_summary_type node


let get_standard_char_type_replacements (char_type: string) =
  if char_type = "ansi" || char_type = "A" then
    [ ("LPCTSTR", "LPCSTR");
      ("LPTSTR", "LPSTR");
      ("TCHAR", "char")]
  else if char_type = "unicode" || char_type = "W" then
    [ ("LPCTSTR", "LPCWSTR");
      ("LPTSTR", "LPWSTR");
      ("TCHAR", "wchar_t")]
  else
    raise (BCH_failure
             (LBLOCK [
                  STR char_type;
		  STR " is not a valid ansi/unicode designation. ";
		  STR "Use A/W or ansi/unicode"]))


let read_xml_type_transformer (node: xml_element_int) =
  let get = node#getAttribute in
  let getcc = node#getTaggedChildren in
  let has = node#hasNamedAttribute in
  let replacements = List.map (fun n ->
    let get = n#getAttribute in (get "src", get "tgt")) (getcc "replace-type") in
  let replacements = if has "char-type" then 
      (get_standard_char_type_replacements (get "char-type")) @ replacements
    else
      replacements in
  let replace s = 
    try let (_,t) = List.find (fun (x,_) -> x = s) replacements in t with 
      Not_found -> s in
  replace

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

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes
open BCHXmlUtil

module H = Hashtbl
module P = Pervasives

let raise_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

let int_type_to_string (k:ikind) =
  match k with
  | IChar -> "char"
  | ISChar -> "signed char"
  | IUChar -> "unsigned char"
  | IWChar -> "wchar_t"
  | IBool -> "bool"
  | IInt -> "int"
  | IUInt -> "unsigned int"
  | IShort -> "short"
  | IUShort -> "unsigned short"
  | ILong -> "long"
  | IULong -> "unsigned long"
  | ILongLong -> "long long"
  | IULongLong -> "unsigned long long"
  | INonStandard _ -> "non-standard"

let ikind_type_size (k:ikind) =
  match k with
  | IChar | ISChar | IUChar -> 1
  | IWChar -> 2
  | IBool -> 4
  | IInt | IUInt -> 4
  | IShort | IUShort -> 2
  | ILong | IULong -> 4
  | ILongLong | IULongLong -> 8
  | INonStandard (_,s) -> s
    
let get_ikind_from_size ?(signed=true) (size:int) =
  match size with
  | 1 -> if signed then ISChar else IUChar
  | 2 -> if signed then IShort else IUShort
  | 4 -> if signed then IInt else IUInt
  | 8 -> if signed then ILongLong else IULongLong
  | _ -> INonStandard (signed,size)
      
let float_type_to_string (k:fkind) =
  match k with
  | FFloat -> "float"
  | FDouble -> "double"
  | FLongDouble -> "long double"
    
let float_representation_to_string (r:frepresentation) =
  match r with FScalar -> "scalar" | FPacked -> "packed"
    
let fkind_type_size (k:fkind) =
  match k with
  | FFloat -> 4
  | FDouble -> 8
  | FLongDouble -> 16

    
let list_compare (l1:'a list) (l2:'b list) (f:'a -> 'b -> int):int =
  let length = List.length in
  if (length l1) < (length l2) then -1
  else if (length l1) > (length l2) then 1 
  else List.fold_right2 (fun e1 e2 a -> if a = 0 then (f e1 e2) else a) l1 l2 0

let attribute_compare a1 a2 =
  match (a1,a2) with (Attr s1, Attr s2) -> P.compare s1 s2

(* Common types and type constructors *)

let t_unknown = TUnknown []
let t_void = TVoid []
let t_vararg = TVarArg []

let t_char = TInt (IChar,[])
let t_uchar = TInt (IUChar,[])
let t_wchar = TInt (IWChar,[])

let t_short = TInt (IShort,[])
let t_int = TInt (IInt,[])
let t_uint = TInt (IUInt,[])
let t_long = TInt (ILong,[])

let t_float = TFloat (FFloat,FScalar,[])
let t_double = TFloat (FDouble,FScalar,[])

let t_named name = TNamed (name,[])

let to_tname s = SimpleName s

let t_comp ?(name_space=[]) name = TComp (to_tname name,List.map to_tname name_space,[])
let t_enum ?(name_space=[]) name = TEnum (to_tname name,List.map to_tname name_space,[])
let t_class ?(name_space=[]) name = TClass (to_tname name,List.map to_tname name_space,[])

let t_tcomp ?(name_space=[]) name = TComp (name,name_space,[])
let t_tenum ?(name_space=[]) name = TEnum (name,name_space,[])
let t_tclass ?(name_space=[]) name = TClass (name,name_space,[])

let t_function (returntype:btype_t) (args:bfunarg_t list) =
  TFun (returntype,Some args,false,[])

let t_vararg_function (returntype:btype_t) (args:bfunarg_t list) =
  TFun (returntype,Some args,true,[])

let t_function_anon (returntype:btype_t) =
  TFun (returntype,None,false,[])

let t_voidptr = TPtr (TVoid [],[])


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
  let add l = (Attr a) :: l in
  match t with
  | TVoid attrs -> TVoid (add attrs)
  | TInt (ik,attrs) -> TInt (ik,add attrs)
  | TFloat (fk,rep,attrs) -> TFloat (fk,rep,add attrs)
  | TPtr (tt,attrs) -> TPtr (tt,add attrs)
  | TRef (tt,attrs) -> TRef (tt,add attrs)
  | THandle (s,attrs) -> THandle (s,add attrs)
  | TArray (tt,e,attrs) -> TArray (tt,e,add attrs)
  | TFun (tt,args,v,attrs) -> TFun (tt,args,v,add attrs)
  | TNamed (s,attrs) -> TNamed (s,add attrs)
  | TComp (s,ns,attrs) -> TComp (s,ns,add attrs)
  | TEnum (s,ns,attrs) -> TEnum (s,ns,add attrs)
  | TVarArg attrs -> TVarArg (add attrs)
  | TClass (s,ns,attrs) -> TClass (s,ns,add attrs)
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
    | TComp (tn,_,_) -> "str" ^ (tn_string tn)
    | TEnum (tn,_,_) -> "enum" ^ (tn_string tn)
    | TVarArg _ -> "vararg"
    | TClass (tn,_,_) -> "class" ^ (tn_string tn)
    | TUnknown _ -> "arg" in
  (aux ty) ^ "_" ^ (string_of_int index)

let attributes_compare l1 l2 = list_compare l1 l2 attribute_compare
    
let rec btype_compare t1 t2 =
  match (t1,t2) with
  | (TUnknown attrs1,TUnknown attrs2) -> attributes_compare attrs1 attrs2
  | (TUnknown _,_) -> -1
  | (_, TUnknown _) -> 1
  | (TVoid attrs1,TVoid attrs2) -> attributes_compare attrs1 attrs2
  | (TVoid _,_) -> -1
  | (_, TVoid _) -> 1
  | (TInt (i1,attrs1), TInt (i2,attrs2)) -> 
    let l0 = P.compare i1 i2 in if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TInt _, _) -> -1
  | (_, TInt _) -> 1
  | (TFloat (f1,r1,attrs1), TFloat (f2,r2,attrs2)) -> 
    let l0 = P.compare f1 f2 in 
    if l0 = 0 then 
      let l1 = P.compare r1 r2 in
      if l1 = 0 then
	attributes_compare attrs1 attrs2 
      else l1
    else l0
  | (TFloat _, _) -> -1
  | (_, TFloat _) -> 1
  | (TPtr (tt1,attrs1), TPtr (tt2,attrs2)) -> 
    let l0 = btype_compare tt1 tt2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TPtr _, _) -> -1
  | (_, TPtr _) -> 1
  | (TRef (tt1,attrs1), TRef (tt2,attrs2)) ->
    let l0 = btype_compare tt1 tt2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TRef _,_) -> -1
  | (_, TRef _) -> 1
  | (THandle (s1,attrs1),THandle (s2,attrs2)) -> 
    let l0 = P.compare s1 s2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (THandle _,_) -> -1
  | (_, THandle _) -> 1
  | (TArray (tt1,x1,attrs1), TArray (tt2,x2,attrs2)) ->
    let l0 = btype_compare tt1 tt2 in	
    if l0 = 0 then 
      let l1 = opt_exp_compare x1 x2 in
      if l1 = 0 then 
	attributes_compare attrs1 attrs2 
      else l1
    else l0
  | (TArray _, _) -> -1
  | (_, TArray _) -> 1
  | (TFun (tt1,args1,_,attrs1), TFun (tt2,args2,_,attrs2)) ->
    let l0 = btype_compare tt1 tt2 in 
    if l0 = 0 then 
      let l1 = opt_arg_list_compare args1 args2 in
      if l1 = 0 then 
	attributes_compare attrs1 attrs2
      else l1 
    else l0
  | (TFun _, _) -> -1
  | (_, TFun _) -> 1
  | (TNamed (n1,attrs1), TNamed (n2,attrs2)) -> 
    let l0 = P.compare n1 n2 in
    if l0 = 0 then attributes_compare attrs1 attrs2 else l0
  | (TNamed _,_) -> -1
  | (_, TNamed _) -> 1
  | (TComp (n1,ns1,attrs1), TComp (n2,ns2,attrs2)) -> 
    let l0 = tname_compare n1 n2 in
    if l0 = 0 then 
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TComp _,_) -> -1
  | (_,TComp _) -> 1
  | (TEnum (n1,ns1,attrs1), TEnum (n2,ns2,attrs2)) -> 
    let l0 = tname_compare n1 n2 in 
    if l0 = 0 then 
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TEnum _, _) -> -1
  | (_, TEnum _) -> 1
  | (TClass (n1,ns1,attrs1), TClass (n2,ns2,attrs2)) ->
    let l0 = tname_compare n1 n2 in
    if l0 = 0 then 
      let l1 = list_compare ns1 ns2 tname_compare in
      if l1 = 0 then attributes_compare attrs1 attrs2 else l1
    else l0
  | (TClass _, _) -> -1
  | (_, TClass _) -> 1
  | (TVarArg attrs1, TVarArg attrs2) -> attributes_compare attrs1 attrs2

and tname_compare t1 t2 =
  match (t1,t2) with
  | (SimpleName n1, SimpleName n2) -> P.compare n1 n2
  | (SimpleName _,_) -> -1
  | (_, SimpleName _) -> 1
  | (TemplatedName (b1,args1), TemplatedName (b2,args2)) ->
    let l0 = tname_compare b1 b2 in
    if l0 = 0 then list_compare args1 args2 btype_compare else l0
    
and opt_arg_list_compare a1 a2 =
  match (a1,a2) with
  | (Some l1, Some l2) ->
     list_compare l1 l2 (fun (_,t1) (_,t2) -> btype_compare t1 t2)
  | (Some _, _) -> -1
  | (_, Some _) -> 1
  | _ -> 0
    
and opt_exp_compare x1 x2 =
  match (x1,x2) with
  | (Some e1, Some e2) -> exp_compare e1 e2
  | (Some _,_) -> -1
  | (_, Some _) -> 1
  | _ -> 0
    
and exp_compare e1 e2 =
  match (e1,e2) with
    (Const c1, Const c2) -> constant_compare c1 c2
      
and constant_compare c1 c2 =
  match (c1,c2) with
  | (CInt64 (i1,k1,_), CInt64 (i2,k2,_)) ->
    let l0 = Int64.compare i1 i2 in if l0 = 0 then P.compare k1 k2 else l0
  | (CInt64 _, _) -> -1
  | (_, CInt64 _) -> 1
  | (CStr s1, CStr s2) -> P.compare s1 s2
  | (CStr _, _) -> -1
  | (_, CStr _) -> 1
  | (CWStr l1, CWStr l2) ->  list_compare l1 l2 Int64.compare
  | (CWStr _, _) -> -1
  | (_, CWStr _) -> 1
  | (CChr c1, CChr c2) -> Char.compare c1 c2
  | (CChr _, _) -> -1
  | (_, CChr _) -> 1
  | (CReal (f1,_,_), CReal (f2,_,_)) -> P.compare f1 f2
  | (CReal _, _) -> -1
  | (_, CReal _) -> 1
  | (CEnum (e1,iname1,ename1), CEnum (e2,iname2,ename2)) ->
    let l0 = P.compare iname1 iname2 in
    if l0 = 0 then 
      let l1 = P.compare ename1 ename2 in
      if l1 = 0 then
	exp_compare e1 e2
      else l1
    else l0

let get_size_of_ikind (i:ikind) =
  match i with
  | IChar | ISChar | IUChar -> 1
  | IWChar -> 2
  | IBool -> 4
  | IInt | IUInt -> 4
  | IShort | IUShort -> 4
  | ILong | IULong -> 4
  | ILongLong | IULongLong -> 8
  | INonStandard (_,s) -> s

let get_size_of_fkind (f:fkind) =
  match f with
  | FFloat -> 4
  | FDouble -> 8
  | FLongDouble -> 16

let get_size_of_btype (t:btype_t) =
  let baseSize = Some 4 in
  match t with
  | TInt (i,_) -> Some (get_size_of_ikind i)
  | TFloat (f,_,_) -> Some (get_size_of_fkind f)
  | TPtr _ | TRef _ | THandle _ | TFun _ -> baseSize
  | _ -> None
      
let constant_to_string (c:constant) =
  match c with
  | CInt64 (_,_,Some t) -> t
  | CInt64 (i64,_,_) -> Int64.to_string i64
  | CStr s -> s
  | CWStr l64 -> String.concat " " (List.map Int64.to_string l64)
  | CChr c -> Char.escaped c
  | CReal (_,_,Some t) -> t
  | CReal (f,_,_)  -> string_of_float f
  | CEnum (_,s,_) -> s
    
let exp_to_string (x:exp) =
  match x with
  | Const c -> constant_to_string c

let attributes_to_string attrs =
  match attrs with 
  | [] -> ""
  | l ->
     (String.concat
        "," (List.map (fun attr -> match attr with Attr s -> s) l)) ^ " "
    
let rec btype_to_string (t:btype_t) =
  let ns_to_string ns =
    String.concat "" (List.map (fun n -> (tname_to_string n) ^ "::") ns) in
  let a = attributes_to_string in
  match t with
  | TVoid attrs -> (a attrs) ^ "void"
  | TInt (ikind,attrs) -> (a attrs) ^ int_type_to_string ikind
  | TFloat (fkind,frep,attrs) -> 
    (a attrs) ^ 
      (float_type_to_string fkind) ^ (match frep with FPacked -> ":packed" | _ -> "")
  | TPtr (tt,attrs) -> (a attrs) ^ "(" ^ (btype_to_string tt) ^ "*)"
  | TRef (tt,attrs) -> (a attrs) ^ "(" ^ (btype_to_string tt) ^ "&)"
  | THandle (s,attrs) -> (a attrs) ^ "H" ^ s
  | TArray (tt,Some x,attrs) -> 
    (a attrs) ^ (btype_to_string tt) ^ "[" ^ (exp_to_string x) ^ "]"
  | TArray (tt,None,attrs) -> 
    (a attrs) ^ (btype_to_string tt) ^ "[]"
  | TFun (tt,optArgs,vararg,attrs) -> 
    (a attrs) ^ "(" ^ (btype_to_string tt) ^ " (" ^
    (String.concat "," (match optArgs with None -> [] | Some args ->
      (List.map (fun (name,ty) -> name ^ ":" ^ (btype_to_string ty)) args))) ^ ") )"
  | TNamed (name,attrs) -> (a attrs) ^ name
  | TComp (name,ns,attrs) -> 
    (a attrs) ^ "struct " ^ (ns_to_string ns)  ^ (tname_to_string name)
  | TEnum (name,ns,attrs) -> 
    (a attrs) ^ "enum " ^ (ns_to_string ns) ^ (tname_to_string name)
  | TVarArg attrs -> (a attrs) ^ "vararg"
  | TClass (name,ns,attrs) -> 
    (a attrs) ^ "class " ^ (ns_to_string ns) ^ (tname_to_string name)
  | TUnknown attrs -> (a attrs) ^ "unknown"

and tname_to_string t =
  match t with
  | SimpleName s -> s
  | TemplatedName (base,args) ->
     (tname_to_string base) ^ "<"
     ^ (String.concat "," (List.map btype_to_string args)) ^ ">"


let rec modify_type (f:type_transformer_t) (t:btype_t) =
  let rec tf tname =
    match tname with
    | SimpleName name -> SimpleName (f name)
    | TemplatedName (base,args) ->
      TemplatedName (tf base,List.map (fun a -> modify_type f a) args) in
  match t with
  | TPtr (tt,attrs) -> TPtr (modify_type f tt,attrs)
  | TRef (tt,attrs) -> TRef (modify_type f tt,attrs)
  | TArray (tt,e,attrs) -> TArray (modify_type f tt, e,attrs)
  | TFun (tt,optArgs,b,attrs) ->
    TFun (modify_type f tt, modify_type_optargs f optArgs,b,attrs)
  | TNamed (s,attrs) -> TNamed (f s,attrs)
  | TComp (s,ns,attrs) -> TComp (tf s,ns,attrs)
  | _ -> t

and modify_type_optargs (f:type_transformer_t) (args:bfunarg_t list option) =
  match args with
  | Some l -> Some (List.map (fun (s,t) -> (s, modify_type f t)) l)
  | _ -> None
    
let btype_to_pretty t = STR (btype_to_string t)

let get_struct_field_enums (cinfo:bcompinfo_t) =
  List.fold_left (fun acc fld ->
    match fld.bfenum with Some (s,_) -> s::acc | _ -> acc) [] cinfo.bcfields
    
exception Invalid_enumeration of string * string
    
(* ------------------------------------------------------------------------------ *
 * implements simpleType:ikindSelectorType                                        *
 * ------------------------------------------------------------------------------ *) 
let ikind_of_string s =
  match s with
  | "ichar" -> IChar
  | "ischar" -> ISChar
  | "iuchar" -> IUChar
  | "iwchar" -> IWChar
  | "ibool" -> IBool
  | "iint" -> IInt
  | "iuint" -> IUInt
  | "ishort" -> IShort
  | "iushort" -> IUShort
  | "ilong" -> ILong
  | "iulong" -> IULong
  | "ilonglong" -> ILongLong
  | "iulonglong" -> IULongLong
  | _ -> raise (Invalid_enumeration ("ikind", s))
    
(* ------------------------------------------------------------------------------ *
 * implements simpleType:ikindSelectorType                                        *
 * ------------------------------------------------------------------------------ *) 
let ikind_to_string (kind:ikind) =
  match kind with
    IChar -> "ichar"
  | ISChar -> "ischar"
  | IUChar -> "iuchar"
  | IWChar -> "iwchar"
  | IBool -> "ibool"
  | IInt -> "iint"
  | IUInt -> "iuint"
  | IShort -> "ishort"
  | IUShort -> "iushort"
  | ILong -> "ilong"
  | IULong -> "iulong"
  | ILongLong -> "ilonglong"
  | IULongLong -> "iulonglong"
  | _ -> raise (Invalid_enumeration ("ikind","INonStandard"))
    
(* ------------------------------------------------------------------------------ *
 * implements simpleType:fkindSelectorType                                        *
 * ------------------------------------------------------------------------------ *) 
let fkind_of_string s =
  match s with
  | "ffloat" -> FFloat
  | "fdouble" -> FDouble
  | "flongdouble" -> FLongDouble
  | _ -> raise (Invalid_enumeration ("fkind",s))
    
let frep_of_string s =
  match s with
  | "scalar" -> FScalar
  | "packed" -> FPacked
  | _ -> raise (Invalid_enumeration ("frep",s))
    
(* ------------------------------------------------------------------------------ *
 * implements simpleType:fkindSelectorType                                        *
 * ------------------------------------------------------------------------------ *) 
let fkind_to_string (kind:fkind) =
  match kind with
    FFloat -> "ffloat"
  | FDouble -> "fdouble"
  | FLongDouble -> "flongdouble"
    
(* ------------------------------------------------------------------------------ *
 * implements simpleType:typSelectorType                                          *
 * ------------------------------------------------------------------------------ *) 
let typ_tag_to_string (t:btype_t) =
  match t with
    TVoid _ -> "tvoid"
  | TInt _ -> "tint"
  | TFloat _ -> "tfloat"
  | TPtr _ -> "tptr"
  | TRef _ -> "tref"
  | THandle _ -> "thandle"
  | TArray _ -> "tarray"
  | TFun _ -> "tfun"
  | TNamed _ -> "tnamed"
  | TComp _ -> "tcomp"
  | TEnum _ -> "tenum"
  | TVarArg _ -> "tvararg"
  | TClass _ -> "class"
  | TUnknown _ -> "tunknown"
    
(* ------------------------------------------------------------------------------ *
 * implements simpleType:constantSelectorType                                     *
 * ------------------------------------------------------------------------------ *) 
let constant_tag_to_string (c:constant) =
  match c with
    CInt64 _ -> "cint64"
  | CStr _ -> "cstr"
  | CWStr _ -> "cwstr"
  | CChr _ -> "cchr"
  | CReal _ -> "creal"
  | CEnum _ -> "cenum"
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:intElementType                                          *
 * ------------------------------------------------------------------------------ *) 
let read_xml_int64 (node:xml_element_int) : int64 =
  Int64.of_string (node#getAttribute "intValue")
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:intElementType                                          *
 * ------------------------------------------------------------------------------ *) 
let write_xml_int64_element (node:xml_element_int) (i:int64) =	
  node#setAttribute "intValue" (Int64.to_string i)
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:intListType                                             *
 * ------------------------------------------------------------------------------ *) 
let read_xml_int64_list (node:xml_element_int) : int64 list =
  List.map read_xml_int64 (node#getTaggedChildren "int")
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:intListType                                             *
 * ------------------------------------------------------------------------------ *) 
let write_xml_int64_list (node:xml_element_int) (l:int64 list) =
  node#appendChildren 
    (List.map (fun i -> 
         let inode = xmlElement "int" in
         begin write_xml_int64_element inode i ; inode end) l)
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:constantType                                            *
 * ------------------------------------------------------------------------------ *) 				
let rec read_xml_constant (node:xml_element_int) : constant =
  let has = node#hasNamedAttribute in
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let get_int = node#getIntAttribute in
  let get_text () = if has "textrep" then Some (get "textrep") else None in
  match get "ctag" with
  | "cint64" ->
    CInt64 (Int64.of_string (get "intValue"),ikind_of_string (get "ikind"),get_text ())
  | "cstr" -> CStr (get "strValue")
  | "cwstr" -> CWStr (read_xml_int64_list (getc "wlist"))
  | "cchr" -> CChr (Char.chr (get_int "charValue"))
  | "creal" -> 
    CReal (float_of_string (get "floatValue"),fkind_of_string (get "fkind"),get_text ())
  | "cenum" -> CEnum (read_xml_exp (getc "exp"),get "eitem",get "ename")
  | s -> raise_error node (LBLOCK [ STR s ; STR " not recognized as a constant type" ])
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:expressionType                                          *
 * ------------------------------------------------------------------------------ *) 				
and read_xml_exp (node:xml_element_int) : exp =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  match get "etag" with
  | "const" -> Const (read_xml_constant (getc "const"))
  | s -> raise_error node (LBLOCK [ STR s ; STR " not recognized as an exp tag" ])
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:eitemType                                               *
 * ------------------------------------------------------------------------------ *) 
let read_xml_eitem (node:xml_element_int) : (string * exp) =
  (node#getAttribute "eitemname", read_xml_exp (node#getTaggedChild "exp"))
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:eitemListType                                           *
 * ------------------------------------------------------------------------------ *) 
let read_xml_eitem_list (node:xml_element_int) : (string * exp) list =
  List.map read_xml_eitem (node#getTaggedChildren "eitem")
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:enumInfoType                                            *
 * ------------------------------------------------------------------------------ *) 
let read_xml_enuminfo (node:xml_element_int) : benuminfo_t = 
  let getc = node#getTaggedChild in
  {	bename = node#getAttribute "ename" ;
	beitems = read_xml_eitem_list (getc "eitems") ;
	bekind = ikind_of_string (node#getAttribute "ekind") ;
  }
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:fieldInfoType                                           *
 * ------------------------------------------------------------------------------ *) 			
let rec read_xml_fieldinfo (node:xml_element_int) : bfieldinfo_t =
  let getc = node#getTaggedChild in
  let geti = node#getIntAttribute in
  let hasc = node#hasTaggedChild in
  let tNode = if hasc "type" then getc "type" else getc "btype" in
  let get_enum n = Some (n#getAttribute "name", 
			 if n#hasNamedAttribute "flags" then 
			   n#getBoolAttribute "flags" else false) in
  { bfname = node#getAttribute "name" ;
    bftype = read_xml_type tNode ;
    bfenum = if hasc "enum" then get_enum (getc "enum") else None ;
    bfoffset = geti "offset" ;
    bfsize = geti "size" 
  }
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:fieldInfoListType                                       *
 * ------------------------------------------------------------------------------ *) 			
and read_xml_fieldinfo_list (node:xml_element_int) : bfieldinfo_t list =
  List.map read_xml_fieldinfo (node#getTaggedChildren "field")
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:compInfoType                                            *
 * ------------------------------------------------------------------------------ *) 			
and read_xml_compinfo (node:xml_element_int) : bcompinfo_t =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  let get_bool = node#getBoolAttribute in
  { bcname = get "name" ;
    bcstruct = if has "cstruct" then get_bool "cstruct" else true ;
    bcfields = read_xml_fieldinfo_list (getc "fields") ;
  }
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:argType                                                 *
 * ------------------------------------------------------------------------------ *) 				
and read_xml_arg (node:xml_element_int) : (string * btype_t) =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let hasc = node#hasTaggedChild in
  let tynode = if hasc "type" then getc "type" else getc "typ" in
  (get "aname", read_xml_type tynode )
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:argListType                                             *
 * ------------------------------------------------------------------------------ *) 				
and read_xml_arg_list (node:xml_element_int) : (string * btype_t) list =
  List.map read_xml_arg (node#getTaggedChildren "arg")
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:btype                                                   *
 * ------------------------------------------------------------------------------ *) 				
and read_xml_btype (node:xml_element_int) : btype_t =
  let get = node#getAttribute in
  let getb = node#getBoolAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  let hasc = node#hasTaggedChild in
  let get_vararg () = if has "vararg" then getb "vararg" else false in
  let gettname () =
    if has "name" then SimpleName (get "name") else read_xml_tname (getc "templated-name") in
  let read_typ () = 
    let tNode = if hasc "type" then 
	getc "type" 
      else if hasc "typ" then
	getc "typ"
      else getc "btype" in
    read_xml_type tNode in
  let read_exp () = read_xml_exp (getc "exp") in
  let read_opt_exp () = if hasc "exp" then Some (read_exp ()) else None in
  let read_opt_args () = 
    if hasc "args" then Some (read_xml_arg_list (getc "args")) else None in
  let read_attributes () = 
    if hasc "attrs" then 
      List.map (fun n -> Attr (n#getAttribute "name")) 
	((getc "attrs")#getTaggedChildren "attr")
    else
      [] in
  let read_name_space () =
    if hasc "name-space" then
      List.map read_xml_tname ((getc "name-space")#getTaggedChildren "ns")
    else
      [] in
  match get "ttag" with
  | "tvoid" -> TVoid (read_attributes ())
  | "tint" -> TInt (ikind_of_string (get "ikind"),read_attributes ())
  | "tfloat" -> 
    TFloat (fkind_of_string (get "fkind"),frep_of_string (get "frep"),read_attributes ())
  | "tptr" -> TPtr (read_typ (),read_attributes ())
  | "tref" -> TRef (read_typ (),read_attributes ())
  | "thandle" -> THandle (get "device",read_attributes ())
  | "tarray" -> TArray (read_typ (), read_opt_exp (),read_attributes ())
  | "tfun" -> TFun (read_typ (), read_opt_args (), get_vararg (),read_attributes ())
  | "tnamed" -> TNamed (get "tname",read_attributes ())
  | "tcomp" -> TComp (gettname (),read_name_space () , read_attributes ())
  | "tenum" -> TEnum (gettname (),read_name_space () , read_attributes ())
  | "tvararg" -> TVarArg (read_attributes ())
  | "tclass" -> TClass (gettname (), read_name_space () , read_attributes ())
  | "tunknown" -> TUnknown (read_attributes ())
  | s -> raise_error node (LBLOCK [ STR s ; STR " not recognized as a type tag"])

and read_xml_tname (node:xml_element_int) =
  let get = node#getAttribute in
  let getc = node#getTaggedChild in
  let has = node#hasNamedAttribute in
  if has "name" then SimpleName (get "name") else
    TemplatedName (read_xml_tname (getc "base"), 
		   List.map read_xml_btype ((getc "args")#getTaggedChildren "arg"))

and read_xml_summary_type (node:xml_element_int) =
  let rec aux n =
    if n#hasText then 
      TNamed (n#getText,[])
    else
      let nn = n#getChild in
      match nn#getTag with
      | "ptr" -> TPtr (aux nn,[])
      | "array" -> 
	let size = if nn#hasNamedAttribute "size" then
	    Some (Const (CInt64 (Int64.of_string (nn#getAttribute "size"),IInt,None)))
	  else
	    None in
	TArray (aux nn, size,[])
      | "vararg" -> TVarArg []
      | "struct" -> t_comp (nn#getAttribute "name")
      | s ->
	raise_error node 
	  (LBLOCK [ STR s ; STR " not recognized as a summary type" ]) in
  aux node

and read_xml_type (node:xml_element_int) =
  if node#getTag = "btype" || node#getTag = "typ" then 
    read_xml_btype node 
  else 
    read_xml_summary_type node

and read_xml_returntype (node:xml_element_int) =
  if node#getTag = "returnbtype" then
    read_xml_btype node
  else
    read_xml_summary_type node


let get_standard_char_type_replacements (char_type:string) =
  if char_type = "ansi" || char_type = "A" then
    [ ("LPCTSTR", "LPCSTR") ;
      ("LPTSTR", "LPSTR") ;
      ("TCHAR", "char") ]
  else if char_type = "unicode" || char_type = "W" then
    [ ("LPCTSTR", "LPCWSTR") ;
      ("LPTSTR", "LPWSTR") ;
      ("TCHAR", "wchar_t") ]
  else
    raise (BCH_failure
             (LBLOCK [ STR char_type ; 
		       STR " is not a valid ansi/unicode designation. " ;
		       STR "Use A/W or ansi/unicode" ]))
  
let read_xml_type_transformer (node:xml_element_int) =
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
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:btypeInfoType                                           *
 * ------------------------------------------------------------------------------ *) 				
let read_xml_btypeinfo (node:xml_element_int) : btypeinfo_t = 
  let getc = node#getTaggedChild in
  { btname = node#getAttribute "tname" ;
    bttype = read_xml_btype (getc "ttype") ;
  }
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:constantType                                            *
 * ------------------------------------------------------------------------------ *) 				
let rec write_xml_constant (node:xml_element_int) (c:constant) =
  let set = node#setAttribute in
  let set_int = node#setIntAttribute in
  let append = node#appendChildren in
  let _ = set "ctag" (constant_tag_to_string c) in
  let set_text optRep = match optRep with Some rep -> set "textrep" rep | _ -> () in
  match c with
  | CInt64 (i64,ikind,optRep) ->
    begin	
      set "intValue" (Int64.to_string i64) ; 
      set "ikind" (ikind_to_string ikind) ;
      set_text optRep	
    end
  | CStr s -> set "strValue" s 
  | CWStr l ->
     let wNode = xmlElement "wlist" in
     begin write_xml_int64_list wNode l ; append [ wNode ] end
  | CChr ch -> set_int "charValue" (Char.code ch) ;
  | CReal (f,fkind,optRep) ->
    begin	
      set "floatValue" (string_of_float f) ; 
      set "fkind" (fkind_to_string fkind) ; 
      set_text optRep 
    end
  | CEnum (e,eitem,ename) ->
    let eNode = xmlElement "exp" in
    begin	
      write_xml_exp eNode e ;	
      append [ eNode ] ;	
      set "eitem" eitem ;	
      set "ename" ename	
    end
      
(* ------------------------------------------------------------------------------ *
 * implements complexType:expressionType                                          *
 * ------------------------------------------------------------------------------ *) 				
and write_xml_exp (node:xml_element_int) (x:exp) =
  let set = node#setAttribute in
  let append = node#appendChildren in
  match x with
  | Const c -> 
    let cNode = xmlElement "const" in
    begin write_xml_constant cNode c ; append [ cNode ] ; set "etag" "const" end
      
(* ------------------------------------------------------------------------------ *
 * implements complexType:eitemType                                               *
 * ------------------------------------------------------------------------------ *) 			
and write_xml_eitem (node:xml_element_int) ((name,x):string * exp) =
  let set = node#setAttribute in
  let append = node#appendChildren in
  let expNode = xmlElement "exp" in
  begin
    write_xml_exp expNode x ;
    append [ expNode ] ; set "eitemname" name
  end
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:eitemListType                                           *
 * ------------------------------------------------------------------------------ *) 			
and write_xml_eitem_list (node:xml_element_int) (l:(string * exp) list) =
  node#appendChildren
    (List.map (fun e ->
         let enode = xmlElement "eitem" in
         begin write_xml_eitem enode e ; enode end) l)
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:enumInfoType                                            *
 * ------------------------------------------------------------------------------ *) 			
and write_xml_enuminfo (node:xml_element_int) (einfo:benuminfo_t) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let eitemsNode = xmlElement "eitems" in
  begin
    write_xml_eitem_list eitemsNode einfo.beitems ;
    append [ eitemsNode ] ;
    set "ename" einfo.bename ;
    set "ekind" (ikind_to_string einfo.bekind) ;
  end
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:fieldInfoType                                           *
 * ------------------------------------------------------------------------------ *) 			
and write_xml_fieldinfo (node:xml_element_int) (fld:bfieldinfo_t) =
  let typNode = xmlElement "ftyp" in
  let set = node#setAttribute in
  let seti = node#setIntAttribute in
  let append = node#appendChildren in
  begin
    write_xml_btype typNode fld.bftype ;
    (match fld.bfenum with
    | Some (name,flags) ->
      let eNode = xmlElement "enum" in
      begin 
	eNode#setAttribute "name" name ;
	(if flags then eNode#setAttribute "flags" "true") ;
	append [ eNode ]
      end
    | _ -> ()) ;
    append [ typNode ] ;
    set "fname" fld.bfname ;
    seti "offset" fld.bfoffset ;
    seti "size" fld.bfsize 
  end
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:fieldInfoListType                                       *
 * ------------------------------------------------------------------------------ *) 			
and write_xml_fieldinfo_list (node:xml_element_int) (l:bfieldinfo_t list) =
  node#appendChildren
    (List.map (fun f ->
         let fnode = xmlElement "fieldinfo" in
         begin write_xml_fieldinfo fnode f ; fnode end) l)
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:compInfoType                                            *
 * ------------------------------------------------------------------------------ *) 			
and write_xml_compinfo (node:xml_element_int) (cinfo:bcompinfo_t) =
  let fnode = xmlElement "bcfields" in
  let append = node#appendChildren in
  let set = node#setAttribute in
  let setb = node#setBoolAttribute in
  begin
    write_xml_fieldinfo_list fnode cinfo.bcfields ;
    append [ fnode ] ;
    set "cname" cinfo.bcname ;
    setb "cstruct" cinfo.bcstruct ;
  end
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:argType                                                 *
 * ------------------------------------------------------------------------------ *) 				
and write_xml_arg (node:xml_element_int) ((name,typ):(string * btype_t)) =
  let tNode = xmlElement "typ" in
  let append = node#appendChildren in
  let set = node#setAttribute in
  begin	write_xml_btype tNode typ ; append [ tNode ] ; set "aname" name end
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:argListType                                             *
 * ------------------------------------------------------------------------------ *) 				
and write_xml_arg_list (node:xml_element_int) (l:(string * btype_t) list) =
  node#appendChildren
    (List.map (fun arg ->
         let argNode = xmlElement "arg" in
         begin write_xml_arg argNode arg ; argNode end) l)
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:typSpecType                                             *
 * ------------------------------------------------------------------------------ *) 				
and write_xml_btype (node:xml_element_int) (typ:btype_t) = 
  let set = node#setAttribute in
  let setb = node#setBoolAttribute in
  let append = node#appendChildren in
  let _ = set "ttag" (typ_tag_to_string typ) in
  let add_len optLen = 
    match optLen with None -> () | Some len ->
      let expNode = xmlElement "exp" in 
      begin write_xml_exp expNode len ; append [ expNode ] end in
  let add_args optArgs = 
    match optArgs with None -> () | Some args ->
    let argsNode = xmlElement "args" in 
    begin write_xml_arg_list argsNode args ; append [ argsNode ] end in
  let write_xml_attrs l =
    match l with
    | [] -> ()
    | l ->
      let aaNode = xmlElement "attrs" in
      begin
	aaNode#appendChildren ( List.map (fun a ->
	  match a with Attr s ->
	    let aNode = xmlElement "attr" in
            begin aNode#setAttribute "value" s  ; aNode end) l) ;
	append [ aaNode ]
      end in
  let write_xml_name_space l =
    match l with
    | [] -> ()
    | l ->
      let nsNode = xmlElement "name-space" in
      begin
	nsNode#appendChildren
          (List.map (fun n ->
	       let nNode = xmlElement "ns" in
               begin write_xml_tname nNode n ; nNode end) l) ;
	append [ nsNode ]
      end in
  match typ with
    TVoid attrs -> write_xml_attrs attrs
  | TInt (ikind,attrs) -> 
    begin write_xml_attrs attrs ; set "ikind" (ikind_to_string ikind) end
  | TFloat (fkind,frep,attrs) -> 
    begin 
      write_xml_attrs attrs ;
      set "fkind" (fkind_to_string fkind) ; 
      set "frep" (float_representation_to_string frep) ;
    end
  | TPtr (ttyp,attrs) | TRef (ttyp,attrs) ->
    let typNode = xmlElement "typ" in	
    begin 
      write_xml_attrs attrs ;
      write_xml_btype typNode ttyp ; 
      append [ typNode ] 
    end
  | THandle (s,attrs) -> begin write_xml_attrs attrs ; set "device" s end
  | TArray (ttyp,optLength,attrs) ->
    let typNode = xmlElement "typ" in
    begin 
      write_xml_attrs attrs ;
      write_xml_btype typNode ttyp ; 
      append [ typNode ] ; 
      add_len optLength 
    end
  | TFun (ttyp,optArgs,varArg,attrs) ->
    let typNode = xmlElement "typ" in
    begin
      write_xml_attrs attrs ;
      write_xml_btype typNode ttyp ;
      append [ typNode ] ;
      add_args optArgs ;
      setb "vararg" varArg ;
    end
  | TNamed (tname,attrs) ->
     begin write_xml_attrs attrs ; set "tname" tname end
  | TComp (name,ns,attrs) -> 
     begin
       write_xml_tname node name ;
       write_xml_attrs attrs ;
       write_xml_name_space ns
     end
  | TEnum (name,ns,attrs) -> 
     begin
       write_xml_tname node name ;
       write_xml_attrs attrs ;
       write_xml_name_space ns
     end
  | TVarArg attrs -> write_xml_attrs attrs
  | TClass (name,ns,attrs) -> 
     begin
       write_xml_tname node name ;
       write_xml_attrs attrs ;
       write_xml_name_space ns
     end
  | TUnknown attrs -> write_xml_attrs attrs 

and write_xml_tname (node:xml_element_int) (tname:tname_t) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  match tname with
  | SimpleName name -> set "name" name 
  | TemplatedName (base,args) ->
    let bNode = xmlElement "base" in
    let aaNode = xmlElement "args" in
    begin
      write_xml_tname bNode base ;
      aaNode#appendChildren
        (List.map (fun a -> 
	     let aNode = xmlElement "arg" in
             begin write_xml_btype aNode a ; aNode end) args) ;
      append [ bNode ; aaNode ]
    end
    
(* ------------------------------------------------------------------------------ *
 * implements complexType:typeInfoType                                            *
 * ------------------------------------------------------------------------------ *) 				
and write_xml_btypeinfo (node:xml_element_int) (tinfo:btypeinfo_t) =
  let append = node#appendChildren in
  let set = node#setAttribute in
  let typNode = xmlElement "ttype" in
  begin
    write_xml_btype typNode tinfo.bttype ;
    append  [ typNode ] ;
    set "tname" tinfo.btname ;
  end
    
 


(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet
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

open IO
open IO.BigEndian

(* chlib *)
open CHPretty

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHRawClass
open JCHSignature

(* Descriptors and classname encoding *)
(************************************)

let encode_class_name cs =
  let cn = cs#name in
    ExtString.String.map
      (fun c -> if c = '.' then '/' else c) cn

let unparse_basic_type = function
  | Byte -> "B"
  | Char -> "C"
  | Double -> "D"
  | Float -> "F"
  | Int -> "I"
  | Long -> "J"
  | Short -> "S"
  | Bool -> "Z"
  | _ -> raise (JCH_failure (STR "Unexpected type"))

let rec unparse_object_type = function
  | TClass c -> "L" ^ encode_class_name c ^ ";"
  | TArray s -> "[" ^ unparse_value_type s

and unparse_value_type = function
  | TBasic b -> unparse_basic_type b
  | TObject o -> unparse_object_type o

let rec unparse_method_descriptor desc =
  let sigs = desc#arguments in
  let s = desc#return_value in
    List.fold_left
      (fun desc s -> desc ^ unparse_value_type s)
      "("
      sigs
    ^ ")"
    ^ (match s with
	 | Some s -> unparse_value_type s
	 | None -> "V")
      
let rec unparse_descriptor = function
  | SValue v -> unparse_value_type v
  | SMethod m -> unparse_method_descriptor m

(* Unparse a type that must be an object. Therefore, there is no 'L'
   and ';' around the class name (if this is a class). *)
let unparse_objectType = function
  | TClass c -> encode_class_name c
  | TArray _ as s -> unparse_object_type s


(** (generic) Signatures encoding as describe in the JVMS of Java 5
    (chapter 4.4.4). *)

(** *)

let unparse_TypeVariableSignature : type_variable_int -> string =
  function s -> "T" ^ s#name ^ ";"

let unparse_package : string list -> string = function
  | [] -> ""
  | pl -> String.concat "/" pl ^ "/"

let rec unparse_TypeArgument : type_argument_int -> string = function ta ->
  match ta#kind with
  | ArgumentExtends -> "+"^unparse_FieldTypeSignature (ta#field_type_signature)
  | ArgumentInherits -> "-"^unparse_FieldTypeSignature (ta#field_type_signature)
  | ArgumentIs -> unparse_FieldTypeSignature (ta#field_type_signature)
  | ArgumentIsAny -> "*"

and unparse_TypeArguments : type_argument_int list -> string = function
  | [] -> ""
  | l -> "<" ^ String.concat "" (List.map unparse_TypeArgument l) ^ ">"

and unparse_ArrayTypeSignature (ts:type_signature_int) : string =
  "[" ^ unparse_TypeSignature ts

and unparse_TypeSignature : type_signature_int -> string = function ts ->
  match ts#kind with
  | ObjectType -> unparse_FieldTypeSignature ts#object_type
  | BasicType -> unparse_basic_type ts#basic_type

and unparse_SimpleClassTypeSignature (scts: simple_class_type_signature_int) : string =
  scts#name ^ unparse_TypeArguments scts#type_arguments

and unparse_ClassTypeSignature (cts:class_type_signature_int) : string =
  "L"
  ^ unparse_package cts#package
  ^ String.concat "."
    (List.map
       unparse_SimpleClassTypeSignature
       (cts#enclosing_classes @ [cts#simple_class_type_signature]))
  ^ ";"

and unparse_FieldTypeSignature : field_type_signature_int -> string = function fts ->
  match fts#kind with
  | ClassType -> unparse_ClassTypeSignature fts#class_type
  | ArrayType -> unparse_ArrayTypeSignature fts#array_type
  | TypeVariable -> unparse_TypeVariableSignature fts#type_variable

and unparse_ClassBound : field_type_signature_int option -> string = function
  | None -> ":"
  | Some cb -> ":" ^ unparse_FieldTypeSignature cb

and unparse_InterfaceBounds (ibs:field_type_signature_int list) : string =
  String.concat "" (List.map (fun ib -> ":" ^ unparse_FieldTypeSignature ib) ibs)

and unparse_FormalTypeParameter (ftp:formal_type_parameter_int) : string =
  ftp#name
  ^ unparse_ClassBound ftp#class_bound
  ^ unparse_InterfaceBounds ftp#interface_bounds

and unparse_FormalTypeParameters :formal_type_parameter_int list -> string = function
  | [] -> ""
  | ftp -> "<" ^ String.concat "" (List.map unparse_FormalTypeParameter ftp) ^ ">"

let unparse_SuperclassSignature = unparse_ClassTypeSignature

let unparse_SuperinterfaceSignatures sis =
  String.concat "" (List.map unparse_ClassTypeSignature sis)

let unparse_ClassSignature (cs:class_signature_int) : string =
  unparse_FormalTypeParameters cs#formal_type_parameters
  ^ unparse_SuperclassSignature cs#super_class
  ^ unparse_SuperinterfaceSignatures cs#super_interfaces


let unparse_MethodTypeSignature (mts:method_type_signature_int) : string =
  let unparse_ReturnType :type_signature_int option -> string = function
    | None -> "V"
    | Some ts -> unparse_TypeSignature ts
  and unparse_ThrowsSignature (tsl:throws_signature_int list) : string =
    String.concat ""
      (List.map
	 (function ts ->
	    match ts#kind with
	    | ThrowsClass -> "^" ^ unparse_ClassTypeSignature ts#class_type_signature
	    | ThrowsTypeVariable -> "^" ^ unparse_TypeVariableSignature ts#type_variable)
	 tsl)
  in
     unparse_FormalTypeParameters mts#formal_type_parameters
    ^ "("
    ^ String.concat "" (List.map unparse_TypeSignature mts#type_signature)
    ^ ")"
    ^ unparse_ReturnType mts#return_type
    ^ unparse_ThrowsSignature mts#throws


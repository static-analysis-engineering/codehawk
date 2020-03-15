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

(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHStringIndexTable
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypesAPI

module P = Pervasives

exception JCH_failure of pretty_t
exception JCH_not_implemented of string
exception JCH_runtime_type_error of pretty_t
exception JCH_class_structure_error of pretty_t

(* --------------------------------------------------------------------- xml ---
 * Two xml formats are used to save and retrieve data:
 * - external: classes are identified by package name and classname,
 *             methods are identified by method name and signature
 *      this representation is used for artifacts that are to be shared 
 *      between applications and/or users, such as library summaries,
 *      user data for cost models, etc. Expression format in this representation
 *      follows the w3c mathml standard.
 *      functions that read and write this represenation are named
 *      read_xmlx_... and write_xmlx_... resp.
 * - internal: classes and methods are identified by ids that are unique to the
 *             application and provided in the dictionary. These will remain
 *             unchanged after initial analysis. These, may, however, not be
 *             the same from one initial analysis to the next, or between users,
 *             and thus this representation is not suitable to exchange data
 *             between users.
 *      this representation is used for intermediate results produced by
 *      initial analysis or subsequent experiments off the initial analysis,
 *      such as invariants, loopbounds, bytecode info, etc.
 *      function that read and write this representation are named
 *      read_xml_... and write_xml_... resp.
 * ----------------------------------------------------------------------------- *)

let raise_jch_failure (p:pretty_t) = 
  begin pr_debug [ p ; NL ] ; raise (JCH_failure p) end

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ; 
	     INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end


let abbreviatedpackages = 
  [ "java.lang" ; "java.util" ; "java.io" ; "java.math" ]

let byte_to_string (b:int) =
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l
    
let hex_string s =
  let ch = IO.input_string s in
  let h = ref "" in
  let len = String.length s in
  begin
    for i = 0 to len-1 do h := !h ^ (byte_to_string (IO.read_byte ch)) done ;
    !h
  end

class class_name_t ~(index: int) ~(name: string):class_name_int =
object (self: 'a)
  
  method index = index

  method name = name

  method toPretty = STR self#name

  method equal (cn:'a) = self#index = cn#index

  method compare (cn: 'a) = 
    P.compare (self#index, self#name) (cn#index, cn#name)

  method private split_package_class =
    let l =  ExtString.String.nsplit self#name "." in
      match l with
	| [] -> raise (JCH_failure (STR "Error in split_package_class"))
	| _ -> 
	    let rl = List.rev l in
	    let cn = List.hd rl in
	    let p = List.rev (List.tl rl) 
	    in 
	      (p, cn)
		
  method package = fst (self#split_package_class)

  method package_name = String.concat "." self#package

  method abbreviated_package_name =
    try
      if List.mem self#package_name abbreviatedpackages then "" else
        String.concat "" (List.map (fun s -> String.sub s 0 1) self#package)
    with
    | Invalid_argument _ ->
       raise (JCH_failure (LBLOCK [ STR "Error in abbreviated_package_name: " ;
                                    STR self#package_name ]))

  method abbreviated_name = 
    let pname = self#abbreviated_package_name in
    if pname = "" then 
      self#simple_name
    else
      pname ^ "." ^ self#simple_name

  method simple_name = snd (self#split_package_class)

end

let make_class_name = new class_name_t 
                    
class stackmap_t 
  (stack: int * verification_type_t list * verification_type_t list):stackmap_int =
object (self: _)
  
  method stack = stack
  
end

let make_stackmap = new stackmap_t
      
let rec compare_value_types t1 t2 =
  match (t1, t2) with
  | (TBasic _, TObject _) -> -1
  | (TObject _, TBasic _) -> 1
  | (TBasic b1, TBasic b2) -> P.compare b1 b2
  | (TObject o1, TObject o2) -> compare_object_types o1 o2

and compare_object_types t1 t2 =
  match (t1, t2) with
  | (TClass _, TArray _) -> -1
  | (TArray _, TClass _) -> 1
  | (TClass c1, TClass c2) -> c1#compare c2
  | (TArray v1, TArray v2) -> compare_value_types v1 v2

let size_of_java_basic_type (t:java_basic_type_t) =
  match t with
  | Int | Short | Char | Byte | Bool | Int2Bool | ByteBool -> 4
  | Float | Object | Void -> 4
  | Long | Double -> 8

let size_of_value_type (t:value_type_t) =
  match t with
  | TBasic bt -> size_of_java_basic_type bt
  | TObject ot -> 4
      
let java_basic_type_to_string t =
  match t with
  | Int -> "int"
  | Short -> "short"
  | Char -> "char"
  | Byte -> "byte"
  | Bool -> "boolean"
  | Long -> "long"
  | Float -> "float"
  | Double -> "double"
  | Int2Bool -> "Int2Bool"
  | ByteBool -> "ByteBool"
  | Object -> "Object"
  | Void -> "void"

let java_basic_type_of_string s =
  match s with
  | "int" -> Int
  | "short" -> Short
  | "char" -> Char
  | "byte" -> Byte
  | "boolean" -> Bool
  | "long" -> Long
  | "float" -> Float
  | "double" -> Double
  | "Int2Bool" -> Int2Bool
  | "ByteBool" -> ByteBool
  | "object" -> Object
  | "void" -> Void
  | _ -> raise (JCH_failure (LBLOCK [ STR s ; STR " not recognized as a java_basic_type" ]))


let java_basic_type_to_signature_string t =
  match t with
  | Bool -> "Z"
  | Byte -> "B"
  | Char -> "C"
  | Double -> "D"
  | Float -> "F"
  | Int -> "I"
  | Long -> "J"
  | Short -> "S"
  | Void -> "V"
  | _ -> "invalid"

let java_basic_type_of_signature_string s =
  match s with
  | "Z" -> Bool
  | "B" -> Byte
  | "C" -> Char
  | "D" -> Double
  | "F" -> Float
  | "I" -> Int
  | "J" -> Long
  | "S" -> Short
  | "V" -> Void
  | _ -> 
    raise (JCH_failure 
	     (LBLOCK [ STR s ; 
		       STR " not recognized as a java_basic_type in signature form" ]))

let java_basic_type_to_pretty t = STR (java_basic_type_to_string t)

let access_to_string = function
  | Default -> "default"
  | Public -> "public"
  | Private -> "private"
  | Protected -> "protected"

let string_to_access (s:string) = 
  match s with
  | "default" -> Default
  | "public" -> Public
  | "private" -> Private
  | "protected" -> Protected
  | _ -> 
    raise (JCH_failure (LBLOCK [ STR "access type " ; STR s ; STR " not recognized" ]))

let access_to_pretty = function
  | Default -> STR ""
  | Public  -> STR "public"
  | Private -> STR "private"
  | Protected -> STR "protected"

let rec value_type_to_pretty t =
  match t with
  | TBasic b -> java_basic_type_to_pretty b
  | TObject o -> object_type_to_pretty o

and value_type_to_string t =
  match t with
  | TBasic b -> java_basic_type_to_string b
  | TObject o -> object_type_to_string o

and object_type_to_string o =
  match o with
  | TClass c -> c#name
  | TArray v -> (value_type_to_string v) ^ "[]"

and object_type_to_pretty o =
  match o with
  | TClass c -> c#toPretty
  | TArray v -> LBLOCK [value_type_to_pretty v; STR "[]"]

let rec object_type_to_abbreviated_pretty o =
  match o with
  | TClass c -> STR c#abbreviated_name
  | TArray v -> LBLOCK [ value_type_to_abbreviated_pretty v ; STR "[]" ]

and value_type_to_abbreviated_pretty v =
  match v with
  | TBasic b -> java_basic_type_to_pretty b
  | TObject o -> object_type_to_abbreviated_pretty o

let rec value_type_to_signature_string t =
  match t with
  | TBasic b -> java_basic_type_to_signature_string b
  | TObject o -> object_type_to_signature_string o

and object_type_to_signature_string o =
  let replace_dots s = String.concat "/" (ExtString.String.nsplit s ".") in
  match o with
  | TClass c -> "L" ^ (replace_dots c#name) ^ ";"
  | TArray v -> "[" ^ (value_type_to_signature_string v)

let write_xml_visibility (node:xml_element_int) (access:access_t) =
  node#setAttribute "access" (access_to_string access)
  
let write_xmlx_basic_type (node:xml_element_int) (v:java_basic_type_t) =
  node#appendChildren [ xmlElement (java_basic_type_to_string v) ]

let write_xmlx_object (node:xml_element_int) (cn:class_name_int) =
  node#appendChildren [ xml_string "object" cn#name ]

let rec write_xmlx_value_type (node:xml_element_int) (v:value_type_t) =
  match v with
  | TBasic bt -> write_xmlx_basic_type node bt
  | TObject ot -> write_xmlx_object_type node ot

and write_xmlx_object_type (node:xml_element_int) (v:object_type_t) =
  let append = node#appendChildren in
  match v with
  | TClass cn -> write_xmlx_object node cn
  | TArray vt ->
    let aNode = xmlElement "array" in
    begin write_xmlx_value_type aNode vt ; append [ aNode ] end

let write_xmlx_constant_value (node:xml_element_int) (v:constant_value_t) =
  let append = node#appendChildren in
  let app tag key v = append [ xml_attr_string tag key v ] in
  match v with
  | ConstString s ->
     let (ishex,newstring) = encode_string s in
     if ishex then
       app "string" "hexvalue" newstring
     else
       app "string" "value" s 
  | ConstInt i    -> app "int" "value" (Int32.to_string i)
  | ConstFloat f  -> app "float" "value" (Printf.sprintf "%f" f) 
  | ConstLong l   -> app "long" "value" (Int64.to_string l)
  | ConstDouble d -> app "double" "value" (Printf.sprintf "%f" d)
  | ConstClass ot -> write_xmlx_object_type node ot

class field_signature_data_t 
  ~(name: string) 
  ~(field_descriptor: value_type_t):field_signature_data_int 
  =
object (self: 'a)

  method name = name

  method descriptor = field_descriptor

  method compare (f: 'a) =
    let c = P.compare self#name f#name in
      if c = 0 then
	compare_value_types self#descriptor f#descriptor
      else
	c

  method to_string = self#name ^ ":" ^ (value_type_to_string self#descriptor)

  method toPretty = STR (self#to_string)

    
end

let make_field_signature_data
  ~(name: string) 
  ~(field_descriptor: value_type_t) =
  new field_signature_data_t ~name ~field_descriptor


class field_signature_t 
  ~(index: int) 
  ~(field_signature_data: field_signature_data_int):field_signature_int 
  =
object (self: 'a)

  method index = index

  method field_signature_data = field_signature_data

  method name = self#field_signature_data#name

  method descriptor = self#field_signature_data#descriptor

  method equal (fs: 'a) = self#index = fs#index

  method compare (fs: 'a) = P.compare self#index fs#index

  method to_signature_string = value_type_to_signature_string self#descriptor

  method to_string = self#field_signature_data#to_string

  method toPretty: pretty_t = self#field_signature_data#toPretty

  method to_abbreviated_pretty = 
    LBLOCK [ STR self#name ; STR ":" ; value_type_to_abbreviated_pretty self#descriptor ]

end

let make_field_signature
  ~(index: int) 
  ~(field_signature_data: field_signature_data_int) =
  new field_signature_t ~index ~field_signature_data
  
let rec compare_value_type_lists l1 l2 =
  match (l1, l2) with
    | ([], []) -> 0
    | ([], _) -> -1
    | (_, []) -> 1
    | (v1 :: l1, v2 :: l2) ->
	let c = compare_value_types v1 v2 in
	  if c = 0 then
	    compare_value_type_lists l1 l2
	  else
	    c

class method_descriptor_t 
  ~(arguments: value_type_t list) 
  ~(return_value: value_type_t option) 
  ():method_descriptor_int =
object (self: 'a)
  
  method arguments = arguments

  method return_value = return_value  

  method compare (d: 'a): int =
    match (self#return_value, d#return_value) with
    | (None, Some _) -> -1
    | (Some _, None) -> 1
    | (Some r1, Some r2) ->
      let c = compare_value_types r1 r2 in
      if c = 0 then
	compare_value_type_lists self#arguments d#arguments
      else
	c
    | (None, None) ->
	  compare_value_type_lists self#arguments d#arguments

  method to_string = 
    "(" ^ (String.concat "," 
	     (List.map (fun a -> value_type_to_string a) arguments)) ^ ")"

  method toPretty: pretty_t = 
    LBLOCK [ pretty_print_list arguments value_type_to_pretty "(" "," ")" ]

end

let make_method_descriptor
    ~(arguments: value_type_t list) 
    ?(return_value: value_type_t option) 
    () =
  new method_descriptor_t ~arguments ~return_value:return_value ()

class method_signature_data_t 
  ~(is_static: bool)
  ~(name: string) 
  ~(method_descriptor: method_descriptor_int):method_signature_data_int
  =
object (self: 'a)

  method name = name

  method descriptor = method_descriptor
    
  method compare (m: 'a): int =
    match (self#is_static,m#is_static) with
    | (true,true) | (false,false) ->
      let c = Pervasives.compare self#name m#name in
      if c = 0 then
	self#descriptor#compare m#descriptor
      else
	c
    | (false,true) -> -1
    | (true,false) -> 1

  method is_static = is_static

  method to_string = 
    (match method_descriptor#return_value with 
	Some v -> (value_type_to_string v) ^ " "
      | _ -> "") ^ name ^ method_descriptor#to_string

  method toPretty: pretty_t = 
    let ret_pretty = match method_descriptor#return_value with
      Some v -> LBLOCK [ value_type_to_pretty v ; STR " " ]
    | None -> STR "" in
    LBLOCK [ ret_pretty ; STR name ; method_descriptor#toPretty ]
    
end

let make_method_signature_data
    ~(is_static: bool)
    ~(name:string)
    ~(method_descriptor: method_descriptor_int) =
  new method_signature_data_t ~is_static ~name ~method_descriptor


class method_signature_t 
  ~(index: int) 
  ~(method_signature_data: method_signature_data_int):method_signature_int 
  =
object (self: 'a)

  method index = index

  method method_signature_data = method_signature_data

  method name = self#method_signature_data#name

  method descriptor = self#method_signature_data#descriptor

  method equal (ms: 'a) = self#index = ms#index

  method compare (ms: 'a) = P.compare self#index ms#index

  method is_static = method_signature_data#is_static

  method has_return_value =
    match self#descriptor#return_value with Some _ -> true | _ -> false

  method has_object_return_value =
    match self#descriptor#return_value with
    | Some (TObject _) -> true
    | _ -> false

  method has_basic_return_value =
    match self#descriptor#return_value with
    | Some (TBasic _) -> true
    | _ -> false

  method argcount = List.length self#descriptor#arguments

  method to_signature_string = 
    let args = List.map value_type_to_signature_string self#descriptor#arguments in
    let rv = match self#descriptor#return_value with
      | Some v -> value_type_to_signature_string v
      | _ -> "V" in
    let args = "(" ^ (String.concat "" args) ^ ")" in
    args ^ rv

  method to_string:string = method_signature_data#to_string

  method to_abbreviated_pretty =
    let args = pretty_print_list self#descriptor#arguments value_type_to_abbreviated_pretty
      "(" "," ")" in
    let rv = match self#descriptor#return_value with
      | Some v -> LBLOCK [ STR ":" ; value_type_to_abbreviated_pretty v ]
      | _ -> STR "" in
    LBLOCK [ STR self#name ; args ; rv ]

  method toPretty: pretty_t = LBLOCK [ method_signature_data#toPretty ]

  method write_xmlx ?(varnamemapping=None) (node:xml_element_int) =
    let append = node#appendChildren in
    begin
      List.iteri (fun i a ->
          let par = if self#is_static then i else i+1 in
	  let pNode = xmlElement "arg" in
	  let _ = match varnamemapping with
	    | Some f -> pNode#setAttribute "name" (f par) 
	    | _ -> () in
          begin
	    write_xmlx_value_type pNode a ;
	    pNode#setIntAttribute "nr" (i+1) ;
	    append [ pNode] 
          end) self#descriptor#arguments ;
      (match self#descriptor#return_value with
       | Some r ->
	  let rNode = xmlElement "return" in
	  begin 
	    write_xmlx_value_type rNode r ; 
	    append [ rNode ]
	  end
       | _ -> ())
    end

end

let make_method_signature
    ~(index:int)
    ~(method_signature_data:method_signature_data_int) =
  new method_signature_t ~index ~method_signature_data
  
let clinit_signature_data = 
  new method_signature_data_t 
    ~is_static:true
    ~name:"<clinit>"
    ~method_descriptor:(new method_descriptor_t ~arguments:[] ~return_value:None ())
    
let clinit_signature =
  new method_signature_t
    ~index:0
    ~method_signature_data:clinit_signature_data


class class_field_signature_data_t 
  ~(class_name: class_name_int) 
  ~(field_signature: field_signature_int):class_field_signature_data_int
  =
object (self: 'a)

  method class_name = class_name

  method name = field_signature#name

  method field_signature = field_signature

  method compare (f: 'a) =
    let c = Pervasives.compare self#class_name f#class_name in
      if c = 0 then
	self#field_signature#compare f#field_signature
      else
	c

  method toPretty: pretty_t = 
    LBLOCK [ class_name#toPretty ; STR "." ; field_signature#toPretty ]

end

let make_class_field_signature_data 
    ~(class_name:class_name_int)
    ~(field_signature:field_signature_int) =
  new class_field_signature_data_t ~class_name ~field_signature

class class_method_signature_data_t 
  ~(class_name: class_name_int) 
  ~(method_signature: method_signature_int):class_method_signature_data_int 
  =
object (self: 'a)

  method class_name = class_name

  method method_signature = method_signature

  method name = method_signature#name

  method compare (m: 'a) =
    let c = P.compare self#class_name m#class_name in
      if c = 0 then
	self#method_signature#compare m#method_signature
      else
	c

  method is_static = method_signature#is_static

  method toPretty:pretty_t =
    LBLOCK [ class_name#toPretty ; STR "." ; method_signature#toPretty ]

  method to_abbreviated_pretty:pretty_t =
    LBLOCK [ STR class_name#abbreviated_name ; STR "." ; method_signature#to_abbreviated_pretty ]

end

let make_class_method_signature_data
    ~(class_name:class_name_int)
    ~(method_signature:method_signature_int) =
  new class_method_signature_data_t ~class_name ~method_signature

class class_field_signature_t 
  ~(index: int) 
  ~(class_field_signature_data: class_field_signature_data_int):class_field_signature_int 
  =
object (self: 'a)

  method index = index

  method class_field_signature_data = class_field_signature_data

  method class_name = self#class_field_signature_data#class_name

  method name = self#class_field_signature_data#name

  method field_signature = self#class_field_signature_data#field_signature

  method equal (cfs: 'a) = self#index = cfs#index

  method compare (cfs: 'a) = Pervasives.compare self#index cfs#index

  method to_string: string =
    class_field_signature_data#class_name#name ^ "." ^
      class_field_signature_data#field_signature#to_string

  method toPretty: pretty_t = 
    LBLOCK [ class_field_signature_data#class_name#toPretty ; STR ":" ; 
	     class_field_signature_data#field_signature#toPretty ]

end

let make_class_field_signature
    ~(index:int)
    ~(class_field_signature_data:class_field_signature_data_int) =
  new class_field_signature_t ~index ~class_field_signature_data

  
class class_method_signature_t 
  ~(index: int) 
  ~(class_method_signature_data: class_method_signature_data_int):class_method_signature_int
  =
object (self: 'a)

  method index = index

  method class_name = class_method_signature_data#class_name

  method method_signature = class_method_signature_data#method_signature

  method class_method_signature_data = class_method_signature_data

  method name = class_method_signature_data#name

  method equal (cms: 'a) = self#index = cms#index

  method compare (cms: 'a) = Pervasives.compare self#index cms#index

  method is_static = class_method_signature_data#is_static

  method toPretty: pretty_t = 
    LBLOCK [ class_method_signature_data#toPretty ]

  method to_abbreviated_pretty: pretty_t =
    class_method_signature_data#to_abbreviated_pretty

  method class_method_signature_string:string =
    self#class_name#name ^ "." ^ self#method_signature#to_string

  method class_method_signature_string_md5:string =
    hex_string (Digest.string self#class_method_signature_string)

  method method_signature_string:string = self#method_signature#to_string

  method method_name_string:string = self#method_signature#name

end

let make_class_method_signature
    ~(index:int)
    ~(class_method_signature_data:class_method_signature_data_int) =
  new class_method_signature_t ~index ~class_method_signature_data

 
let descriptor_to_pretty d =
  match d with
  | SValue vt -> value_type_to_pretty vt
  | SMethod md -> md#toPretty

let constant_value_to_pretty v =
  match v with
  | ConstString s -> STR s
  | ConstInt i -> STR (Int32.to_string i)
  | ConstFloat f -> STR (Printf.sprintf "%f" f)
  | ConstLong l -> STR (Int64.to_string l)
  | ConstDouble f -> LBLOCK [ STR (Printf.sprintf "%f" f) ; STR " (double)" ]
  | ConstClass ot -> object_type_to_pretty ot

let reference_kind_to_string k =
  match k with
  | REFGetField -> "REF_getField"
  | REFGetStatic -> "REF_getStatic"
  | REFPutField -> "REF_putField"
  | REFPutStatic -> "REF_putStatic"
  | REFInvokeVirtual -> "REF_invokeVirtual"
  | REFInvokeStatic -> "REF_invokeStatic"
  | REFInvokeSpecial -> "REF_invokeSpecial"
  | REFNewInvokeSpecial -> "REF_newInvokeSpecial"
  | REFInvokeInterface -> "REF_invokeInterface"

let method_handle_to_pretty h =
  match h with
  | FieldHandle (cn,fs) -> LBLOCK [ cn#toPretty ; STR ":" ; fs#toPretty ]
  | MethodHandle (ot,ms) -> LBLOCK [ object_type_to_pretty ot ; STR ":" ; ms#toPretty ]
  | InterfaceHandle (cn,ms) -> LBLOCK [ cn#toPretty ; STR ":" ; ms#toPretty ]

let constant_to_pretty c =
  match c with
  | ConstValue cv -> LBLOCK [ STR "ConstValue: " ; constant_value_to_pretty cv ]
  | ConstField (cn,fs) ->
     LBLOCK [ STR "ConstField: " ; cn#toPretty ; STR ":" ; fs#toPretty ]
  | ConstMethod (ot,ms) ->
     LBLOCK [ STR "ConstMethod: " ; object_type_to_pretty ot ; STR ", " ; ms#toPretty ]
  | ConstInterfaceMethod (cn,ms) ->
     LBLOCK [ STR "ConstInterfaceMethod: " ; cn#toPretty ; STR ":" ; ms#toPretty ]
  | ConstDynamicMethod (index,ms) ->
     LBLOCK [ STR "ConstDynamicMethod: " ; INT index ; STR ", " ; ms#toPretty ]
  | ConstNameAndType (s,d) ->
     LBLOCK [ STR "ConstNameAndType: " ; STR s ; descriptor_to_pretty d ]
  | ConstStringUTF8 s -> LBLOCK [ STR "ConstStringUTF8: " ; STR s ]
  | ConstMethodHandle (k,h) ->
     LBLOCK [ STR "ConstMethodHandle: " ; STR (reference_kind_to_string k) ; STR ", " ;
              method_handle_to_pretty h ]
  | ConstMethodType d -> LBLOCK [ STR "ConstMethodType: " ; d#toPretty ]
  | ConstUnusable -> LBLOCK [ STR "ConstUnusable" ]

let bootstrap_argument_to_pretty a =
  match a with
  | BootstrapArgConstantValue c -> LBLOCK [ STR "CV:" ; constant_value_to_pretty c ]
  | BootstrapArgMethodHandle (kind,h) ->
     LBLOCK [ STR "MH:" ; method_handle_to_pretty h ; STR ":" ;
              STR (reference_kind_to_string kind) ]
  | BootstrapArgMethodType d -> LBLOCK [ STR "MT:" ; d#toPretty ]


class bootstrap_method_t (data:bootstrap_method_data_t):bootstrap_method_int =
object (self)

  method get_kind = data.bm_kind
  method get_method_ref = data.bm_handle
  method get_arguments = data.bm_args
  method get_data = data

  method get_lambda_function =
    match self#get_method_ref with
    | MethodHandle (TClass cn,ms)
         when (cn#name = "java.lang.invoke.LambdaMetafactory")
              && ms#name = "metafactory" && (List.length self#get_arguments) > 2 ->
       let arg2 = List.nth self#get_arguments 1 in
       begin
         match arg2 with
         | BootstrapArgMethodHandle (REFInvokeStatic, MethodHandle (ot,ms)) -> Some (ot,ms)
         | BootstrapArgMethodHandle (REFInvokeVirtual, MethodHandle (ot,ms)) -> Some (ot,ms)
         | _ -> None
       end
    | _ -> None

  method toPretty =
    LBLOCK [ method_handle_to_pretty self#get_method_ref ; STR ":" ;
             STR (reference_kind_to_string self#get_kind) ; NL ;
             LBLOCK (List.map (fun a ->
                         LBLOCK [ INDENT(3, bootstrap_argument_to_pretty a) ; NL ])
                              self#get_arguments) ]
end

let make_bootstrap_method = new bootstrap_method_t
                        
let jch_permissive = ref false
let set_permissive b = jch_permissive := b
let is_permissive () = !jch_permissive

let make_procname (seqnr:int) = new symbol_t ~seqnr "procname"

let default_varname_mapping = fun i -> "var" ^ (string_of_int i)
            
let default_argname_mapping = fun i -> "arg" ^ (string_of_int i)

(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Arnaud Venet and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
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
open CHUtils

(* chutil *)
open CHLogger
open CHPrettyUtil
open CHXmlReader
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHBCTypeUtil
open BCHLibTypes
open BCHSystemSettings
open BCHUtilities
open BCHXmlUtil

module H = Hashtbl


let c_atsign       = 0x0040   (* @ *)
let c_dollarsign   = 0x0024   (* $ *)
let c_ampersand    = 0x0026   (* & *)
let c_semicolon    = 0x003B   (* ; *)
let c_questionmark = 0x003F   (* ? *)
let c_leftbracket  = 0x005B   (* [ *)
let c_underscore   = 0x005F   (* _ *)

let c_A            = 0x0041   (* A *)
let c_B            = 0x0042   (* B *)
let c_C            = 0x0043   (* C *)
let c_D            = 0x0044   (* D *)
let c_E            = 0x0045   (* E *)
let c_F            = 0x0046   (* F *)
let c_G            = 0x0047   (* G *)
let c_H            = 0x0048   (* H *)
let c_I            = 0x0049   (* I *)
let c_J            = 0x004A   (* J *)
let c_K            = 0x004B   (* K *)
let c_L            = 0x004C   (* L *)
let c_M            = 0x004D   (* M *)
let c_N            = 0x004E   (* N *)
let c_O            = 0x004F   (* O *)
let c_P            = 0x0050   (* P *)
let c_Q            = 0x0051   (* Q *)
let c_R            = 0x0052   (* R *)
let c_S            = 0x0053   (* S *)
let c_U            = 0x0055   (* U *)
let c_V            = 0x0056   (* V *)
let c_W            = 0x0057   (* W *)
let c_X            = 0x0058   (* X *)
let c_Y            = 0x0059   (* Y *)
let c_Z            = 0x005A   (* Z *)

let c_zero         = 0x0030   (* 0 *)
let c_one          = 0x0031   (* 1 *)
let c_two          = 0x0032   (* 2 *)
let c_three        = 0x0033   (* 3 *)
let c_four         = 0x0034   (* 4 *)
let c_five         = 0x0035   (* 5 *)
let c_six          = 0x0036   (* 6 *)
let c_seven        = 0x0037   (* 7 *)
let c_eight        = 0x0038   (* 8 *)
let c_nine         = 0x0039   (* 9 *)

let in_range c lower_bound upper_bound = c >= lower_bound && c <= upper_bound

let is_name_start_char c =
  (in_range c 0x0061 0x007A) ||    (* a-z *) 
  (in_range c 0x0041 0x005A) ||    (* A-Z *)
  (c = 0x005F)                     (*  _  *)

let is_name_char c =
  (is_name_start_char c)     ||    
  (c = 0x002D)               ||     (*  -  *)
  (c = 0x002E)               ||     (*  .  *)
  (c = 0x00B7)               ||
  (in_range c 0x0030 0x0039) ||     (* 0-9 *)
  (in_range c 0x0300 0x036F) ||
  (in_range c 0x203F 0x2040)

let replace_dot s =
  let s = Bytes.copy (Bytes.of_string s) in
    for i = 0 to Bytes.length s - 1 do
      if (Bytes.get s i) = '.' then
        Bytes.set s i '/'
    done;
    Bytes.to_string s

let raise_xml_error (node:xml_element_int) (msg:pretty_t) =
  let error_msg =
    LBLOCK [ STR "(" ; INT node#getLineNumber ; STR "," ;
             INT node#getColumnNumber ; STR ") " ; msg ] in
  begin
    ch_error_log#add "xml parse error" error_msg ;
    raise (XmlReaderError (node#getLineNumber, node#getColumnNumber, msg))
  end

class class_name_t ~(index:int) ~(name:string):class_name_int =
object (self:'a)

  method index = index

  method name = name 

  method toPretty = STR self#name

  method equal (cn:'a) = self#index = cn#index

  method compare (cn:'a) = Stdlib.compare (self#index, self#name) (cn#index, cn#name)

  method package = fst self#split_package_class

  method package_name = String.concat "." self#package

  method simple_name = snd self#split_package_class

  method private split_package_class =
    let l = ExtString.String.nsplit self#name "." in
    match l with
    | [] -> raise (BCH_failure (STR "Error in split_package_class"))
    | _ -> 
      let revlist = List.rev l in (List.rev (List.tl revlist), List.hd revlist)

end

let rec compare_value_types t1 t2 =
  match (t1, t2) with
  | (TBasic _, TObject _) -> -1
  | (TObject _, TBasic _) -> 1
  | (TBasic b1, TBasic b2) -> Stdlib.compare b1 b2
  | (TObject o1, TObject o2) -> compare_object_types o1 o2

and compare_object_types t1 t2 =
  match (t1, t2) with
  | (TClass _, TArray _) -> -1
  | (TArray _, TClass _) -> 1
  | (TClass c1, TClass c2) -> c1#compare c2
  | (TArray v1, TArray v2) -> compare_value_types v1 v2

let rec compare_value_type_lists l1 l2 =
  match (l1, l2) with
  | ([], []) -> 0
  | ([], _) -> -1
  | (_, []) -> 1
  | (v1 :: l1, v2 :: l2) ->
    let c = compare_value_types v1 v2 in
    if c = 0 then compare_value_type_lists l1 l2 else c
    
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

let string_to_java_basic_type s =
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
  | _ -> raise (BCH_failure (LBLOCK [ STR s ; STR " not recognized as a java_basic_type" ]))

let java_basic_type_to_pretty t = STR (java_basic_type_to_string t)

let access_to_string = function
    Default -> "default"
  | Public -> "public"
  | Private -> "private"
  | Protected -> "protected"

let string_to_access (s:string) = 
  match s with
    "default" -> Default
  | "public" -> Public
  | "private" -> Private
  | "protected" -> Protected
  | _ -> raise (BCH_failure (LBLOCK [ STR "access type " ; STR s ; STR " not recognized" ]))

let access_to_pretty = function
    Default -> STR ""
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

let get_java_basic_type_name_prefix (ty:java_basic_type_t) =
  match ty with
  | Int -> "int"
  | Short -> "short"
  | Char -> "char"
  | Byte -> "byte"
  | Bool -> "bool"
  | Long -> "long"
  | Float -> "float"
  | Double -> "double"
  | Int2Bool -> "int"
  | ByteBool -> "byte"
  | Object -> "obj"
  | Void -> "void"

let rec get_java_type_name_prefix (ty:value_type_t) =
  match ty with
  | TBasic b -> get_java_basic_type_name_prefix b
  | TObject (TClass cn) -> cn#simple_name ^ "$obj"
  | TObject (TArray v) -> "A$" ^ (get_java_type_name_prefix v)

let get_java_basic_type_length (ty:java_basic_type_t) =
  match ty with | Long | Double -> 8 | _ -> 4

let get_java_type_length (ty:value_type_t) =
  match ty with
  | TBasic b -> get_java_basic_type_length b
  | TObject _ -> 4

let get_java_basic_type_btype (ty:java_basic_type_t) =
  match ty with
  | Long -> t_long
  | Float -> t_float
  | Double -> t_double
  | Int | Short | Byte | Bool -> t_int
  | Void -> t_void
  | _ -> t_unknown

let get_java_type_btype (ty:value_type_t) =
  match ty with
  | TBasic b -> get_java_basic_type_btype b
  | TObject _ -> t_voidptr

class field_signature_data_t 
  ~(name:string) 
  ~(field_descriptor:value_type_t):field_signature_data_int =
object (self:'a)

  method name = name

  method descriptor = field_descriptor

  method compare (f:'a) =
    let c = Stdlib.compare self#name f#name in
    if c = 0 then compare_value_types self#descriptor f#descriptor else c

  method to_string = self#name ^ ":" ^ (value_type_to_string self#descriptor)

  method toPretty = STR self#to_string
end

class field_signature_t
  ~(index:int)
  ~(field_signature_data:field_signature_data_int): field_signature_int =
object (self:'a)

  method index = index

  method field_signature_data = field_signature_data

  method name = self#field_signature_data#name 

  method descriptor = self#field_signature_data#descriptor

  method equal (f:'a) = self#index = f#index

  method compare (f:'a) = Stdlib.compare self#index f#index

  method to_string = self#field_signature_data#to_string

  method toPretty = self#field_signature_data#toPretty
end 

class method_descriptor_t
  ~(arguments: value_type_t list)
  ~(return_value: value_type_t option) =
object (self:'a)

  method arguments = arguments

  method return_value = return_value

  method compare (d:'a) =
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

  method to_string = "(" ^ 
    (String.concat "," (List.map value_type_to_string arguments)) ^ ")"

  method toPretty = 
    LBLOCK [ pretty_print_list arguments value_type_to_pretty "(" "," ")" ]

end

class method_signature_data_t
  ~(name:string)
  ~(method_descriptor: method_descriptor_int):method_signature_data_int =
object (self:'a)

  method name = name 

  method descriptor = method_descriptor

  method compare (m:'a) =
    let c = Stdlib.compare self#name m#name in
    if c = 0 then self#descriptor#compare m#descriptor else c

  method to_string =
    (match method_descriptor#return_value with
    | Some v -> (value_type_to_string v) ^ " " | _ -> "") ^
      name ^ method_descriptor#to_string

  method toPretty =
    let rt = match method_descriptor#return_value with
      | Some v -> LBLOCK [ value_type_to_pretty v ; STR " " ] | _ -> STR "" in
    LBLOCK [ rt ; STR name  ; method_descriptor#toPretty ]

end

class method_signature_t
  ~(index:int)
  ~(method_signature_data:method_signature_data_int):method_signature_int =
object (self:'a)

  method index = index

  method method_signature_data = method_signature_data

  method name = self#method_signature_data#name 

  method descriptor = self#method_signature_data#descriptor

  method equal (ms:'a) = self#index = ms#index

  method compare (ms:'a) = Stdlib.compare self#index ms#index

  method to_string = method_signature_data#to_string

  method toPretty = method_signature_data#toPretty

end

let java_native_method_api_to_pretty api =
  LBLOCK [ STR (access_to_string api.jnm_access) ; STR " " ;
	   api.jnm_signature#toPretty ; 
	   if api.jnm_static then STR " (static)" else STR "" ]

let java_native_method_class_to_pretty nmc =
  LBLOCK [ STR "class " ; nmc.jnmc_class#toPretty ; NL ;
	   pretty_print_list nmc.jnmc_native_methods
	     (fun m -> LBLOCK [ STR "  " ; 
				java_native_method_api_to_pretty m ; NL ]) "" "" "" ]
	   

let clinit_signature_data = 
  new method_signature_data_t 
    ~name:"<clinit>"
    ~method_descriptor:(new method_descriptor_t ~arguments:[] ~return_value:None)
    
let clinit_signature =
  new method_signature_t
    ~index:0
    ~method_signature_data:clinit_signature_data


module FieldSignatureCollections = CHCollections.Make (
  struct
    type t = field_signature_data_int
    let compare x y = x#compare y
    let toPretty f = f#toPretty
  end)

module MethodSignatureCollections = CHCollections.Make (
  struct
    type t = method_signature_data_int
    let compare x y = x#compare y
    let toPretty m = m#toPretty
  end)

class virtual ['a,'b] indexed_table_t =
object (self: _)

  val mutable next = 0
  val table = Hashtbl.create 13

  method virtual lookup: 'a -> 'b option

  method virtual insert: 'a -> 'b -> unit

  method retrieve (i:int) = Hashtbl.find table i

  method add (k: 'a) (mk: int -> 'b) =
    match self#lookup k with
    | Some e -> e
    | None ->
      let e = mk next in
      let _ = Hashtbl.add table next e in
      let _ = next <- next + 1 in
      let _ = self#insert k e in
      e
end

class class_name_table_t =
object (self: _)

  inherit [string, class_name_t] indexed_table_t as super
    
  val map = new StringCollections.table_t
    
  method insert = map#set
  method lookup = map#get

  method toPretty = map#toPretty
  method listOfValues = map#listOfValues

end

class field_signature_table_t = 
object (self: _)
  
  inherit [field_signature_data_t, field_signature_t] indexed_table_t

  val map = new FieldSignatureCollections.table_t
  
  method insert = map#set
  method lookup = map#get
    
end

class method_signature_table_t =
object (self: _)
  
  inherit [method_signature_data_t, method_signature_t] indexed_table_t

  val map = new MethodSignatureCollections.table_t
  
  initializer
  let _ = self#add clinit_signature_data 
    (fun i -> 
       new method_signature_t 
	 ~index:i 
	 ~method_signature_data:clinit_signature_data) 
  in
    ()
    
  method insert = map#set
  method lookup = map#get
    
end

class java_dictionary_t:java_dictionary_int =
object (self)

  val class_name_table = new class_name_table_t
  val field_signature_table = new field_signature_table_t
  val method_signature_table = new method_signature_table_t

  method make_class_name name =
    class_name_table#add name (fun index -> new class_name_t ~index ~name)

  method make_field_signature name field_descriptor =
    let field_signature_data = new field_signature_data_t ~name ~field_descriptor in
    field_signature_table#add field_signature_data
      (fun index -> new field_signature_t ~index ~field_signature_data)

  method make_method_signature name method_descriptor =
    let method_signature_data = new method_signature_data_t ~name ~method_descriptor in
    method_signature_table#add method_signature_data
      (fun index -> new method_signature_t ~index ~method_signature_data)

end

let java_dictionary = new java_dictionary_t

let make_class_name = java_dictionary#make_class_name 
let make_method_signature = java_dictionary#make_method_signature

let make_method_descriptor arguments return_value =
  new method_descriptor_t ~arguments ~return_value

let write_xml_object (node:xml_element_int) (cn:class_name_int) =
  node#appendChildren [ xml_string "object" cn#name ]

let write_xml_basic_type (node:xml_element_int) (v:java_basic_type_t) =
  node#appendChildren [ xmlElement (java_basic_type_to_string v) ]

let rec write_xml_value_type (node:xml_element_int) (v:value_type_t) =
  match v with
  | TBasic bt -> write_xml_basic_type node bt
  | TObject ot -> write_xml_object_type node ot

and write_xml_object_type (node:xml_element_int) (v:object_type_t) =
  let append = node#appendChildren in
  match v with
  | TClass cn -> write_xml_object node cn
  | TArray vt ->
    let aNode = xmlElement "array" in
    begin write_xml_value_type aNode vt ; append [ aNode ] end

let rec read_xml_value_type (node:xml_element_int):value_type_t =
  match node#getChild#getTag with
  | "array" -> TObject (TArray (read_xml_value_type node#getChild))
  | "object" -> TObject (TClass (make_class_name node#getChild#getText))
  | s -> try TBasic  (string_to_java_basic_type s) with
    BCH_failure p ->
      raise_xml_error node (LBLOCK [ STR "Error in reading value type: " ; p ])

let write_xml_visibility (node:xml_element_int) (access:access_t) =
  let set = node#setAttribute "access" in
  match access with
  | Default -> set "default"
  | Public -> set "public"
  | Private -> set "private"
  | Protected -> set "protected"

let write_xml_parameter (node:xml_element_int) (index:int) (v:value_type_t) =
  let seti = node#setIntAttribute in
  begin
    write_xml_value_type node v ;
    seti "nr" index
  end

let write_xml_method_signature (node:xml_element_int) (ms:method_signature_int) =
  let append = node#appendChildren in
  begin
    append
      (List.mapi (fun i a ->
	let pNode = xmlElement "arg" in
	begin write_xml_parameter pNode (i+1) a ; pNode end) ms#descriptor#arguments) ;
    (match ms#descriptor#return_value with
    | Some r -> 
      let rNode = xmlElement "return" in
      begin write_xml_value_type rNode r ; append [ rNode ] end
    | _ -> ())
  end

let read_xml_method_args (node:xml_element_int) =
  let args = List.map (fun n -> 
    let geti = n#getIntAttribute in
    let nr = geti "nr" in
    let ty = read_xml_value_type n in
    (nr,ty)) (node#getTaggedChildren "arg") in
  List.map (fun (_,t) -> t) (List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) args)

let read_xml_method_signature (node:xml_element_int) (name:string): method_signature_t =
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let argTypes = read_xml_method_args node in
  let returnType = if hasc "return" then
      Some (read_xml_value_type (getc "return"))
    else
      None in
  make_method_signature name (make_method_descriptor argTypes returnType)

let read_xml_java_native_method_api (node:xml_element_int):java_native_method_api_t =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let name = get "name" in
  { jnm_signature = read_xml_method_signature node name ;
    jnm_access = (try (string_to_access (get "access")) with
      BCH_failure p -> raise_xml_error node 
	(LBLOCK [ STR "Error in reading java_native_method: " ; p ])) ;
    jnm_static = if has "static" then (get "static") = "yes" else false
  }

let write_xml_java_native_method_api (node:xml_element_int) (jnm:java_native_method_api_t) =
  begin
    write_xml_method_signature node jnm.jnm_signature ;
    node#setAttribute "name" jnm.jnm_signature#name ;
    node#setAttribute "access" (access_to_string jnm.jnm_access) ;
    if jnm.jnm_static then node#setAttribute "static" "yes"
  end

let read_xml_java_native_method_class (node:xml_element_int):java_native_method_class_t =
  let get = node#getAttribute in
  let name = get "name" in
  let package = get "package" in
  let fullname = package ^ "." ^ name in
  { jnmc_class = make_class_name fullname ;
    jnmc_native_methods = List.map read_xml_java_native_method_api
      ((node#getTaggedChild "native-methods")#getTaggedChildren "method")
  }

let write_xml_java_native_method_class (node:xml_element_int) (jnmc:java_native_method_class_t) =
  let set = node#setAttribute in
  let mmNode = xmlElement "native-methods" in
  begin
    mmNode#appendChildren (List.map (fun ms ->
      let mNode = xmlElement "method" in
      begin write_xml_java_native_method_api mNode ms ; mNode end) jnmc.jnmc_native_methods) ;
    node#appendChildren [ mmNode ] ;
    set "name" jnmc.jnmc_class#simple_name ;
    set "package" jnmc.jnmc_class#package_name 
  end
  
let read_xml_java_class_string (s:string) =
  let doc = readXmlDocumentString s in
  let root = doc#getRoot in
  read_xml_java_native_method_class (root#getTaggedChild "class")


(* -----------------------------------------------------------------------------
   Conversion of java native method signatures to exported names;
   source: Sheng Liang, The Java Native Interface, 1999

   - prefix Java_
   - an encoded fully qualified class name
   - an underscore separator
   - an encoded method name
   - for overloaded native methods, two underscores followd by the encoded
       argument descriptor

   Encoding scheme:
   _0XXXX    Unicode character XXXX
   _1        the character '_'
   _2        the character ';' in descriptors
   _3        the character '[' in descriptors

   Field/Method type descriptors:
   Z  boolean
   B  byte
   C  char
   S  short
   I  int
   J  long
   F  float
   D  double
   V  void
   [  array
   L<fully qualified name>;  class
   ----------------------------------------------------------------------------- *)

let is_start_type_encoding_char c =
  List.mem c [ c_B ; c_C ; c_D ; c_F ; c_I ; c_J ; c_L ; c_S ; c_V ; c_Z ; c_leftbracket ]

let basic_types = 
  [ (c_B, Byte) ;
    (c_C, Char) ;
    (c_D, Double) ;
    (c_F, Float) ;
    (c_I, Int) ;
    (c_J, Long) ;
    (c_S, Short) ;
    (c_Z, Bool) ;
    (c_V, Void) ]

let is_basic_type_encoding_char c = List.mem c (List.map fst basic_types)

let get_basic_type c =
  try
    let (_,ty) =  List.find (fun (k,v) -> k = c) basic_types in ty
  with
  | Not_found ->
    raise (BCH_failure (LBLOCK [ STR "No type found for character " ; INT c ]))

let is_java_native_method_name (name:string) =
  ((String.length name) > 6 && (String.sub name 0 6) = "_Java_") ||
  ((String.length name) > 5 && (String.sub name 0 5) = "Java_")

let rec decode s =
  try
    let i = String.index s '_' in
    let prefix = String.sub s 0 i in
    let rest k = String.sub s (i+k) ((String.length s) - (i+k)) in
    if (String.length s) = (i+1)  then s else
      if s.[i+1] = '1' then prefix ^ "_" ^ (decode (rest 2))
      else if s.[i+1] = '2' then prefix ^ ";" ^ (decode (rest 2))
      else if s.[i+1] = '3' then prefix ^ "[" ^ (decode (rest 2))
      else if s.[i+1] = '_' then
	if (String.length s) = (i+2) then s else
	  if s.[i+2] = '1' then prefix ^ "._" ^ (decode (rest 3))
	  else if s.[i+2] = '2' then prefix ^ ".;" ^ (decode (rest 3))
	  else if s.[i+2] = '3' then prefix ^ ".[" ^ (decode (rest 3))
	  else prefix ^ "&&" ^ (decode (rest 2))
	  else prefix ^ "." ^ (decode (rest 1))
  with Not_found -> s

let convert_to_native_method_name (name:string) =
  try
    let nSuffix = if (String.sub name 0 5) = "Java_" then 5 else 6 in
    (try
      let name = string_suffix name nSuffix in
      let name = decode name in
      try 
	let nIndex = String.index name '@' in Some (String.sub name 0 nIndex)
      with
	Not_found -> Some name					   
    with
      Invocation_error s ->
	begin
	  ch_error_log#add "java native method name" 
	    (LBLOCK [ STR name ; STR ": " ; STR s ]) ;
	  None
	end)
  with
    _ -> 
      begin
	ch_error_log#add "java native method name" (LBLOCK [ STR name ]) ;
	None
      end


(* takes decoded name *)
let get_java_class_name (name:string) =
  let rindex = 
    try
      String.index name '&'
    with Not_found -> (String.length name) - 1 in
  let index = 
    try
      String.rindex_from name rindex '.' 
    with Not_found -> 0 in
  if index = 0 then None else Some (String.sub name 0 index)

(* takes decoded name *)
let get_java_method_name (name:string) =
  let hasArguments = String.contains name '&' in
  try
    if hasArguments then
      let rindex = String.index name '&' in
      let index = String.rindex_from name rindex '.' in
      Some (String.sub name (index+1) ((rindex - index)-1))
  else
      let index = String.rindex name '.' in
      Some (String.sub name (index+1) (((String.length name) - index)-1))
  with 
    Not_found -> None

class java_method_name_t:java_method_name_int =
object (self)

  val mutable classname = ""
  val mutable methodname = ""
  val mutable arguments = []

  method set_class_name (name:string) = classname <- name
  method set_method_name (name:string) = methodname <- name

  method get_class_name = classname

  method get_method_name = methodname

  method add_argument_type (ty:value_type_t) = arguments <- ty :: arguments

  method get_arguments = List.rev arguments

  method has_arguments = match arguments with [] -> false | _ -> true

  method toPretty = LBLOCK [ 
    STR "Classname     : " ; STR classname ; NL ;
    STR "Method name   : " ; STR methodname ; NL ;
    STR "Argument types: " ; 
    pretty_print_list (List.rev arguments) value_type_to_pretty "(" "," ")" ; NL]

end

class java_encoded_name_decoder_t (s:string) =
object (self)

  val len = String.length s
  val mutable ch = IO.input_string s
  val mutable pos = 0 
  val mutable char_la = 0
  val name_buffer = Buffer.create 17
  val cms = new java_method_name_t

  method get_name = cms

  method private stop msg =
    let unparsed = String.sub s (pos-1) (((String.length s) - pos) + 1) in
    raise (BCH_failure (LBLOCK [
      STR "Current name: " ; cms#toPretty ; NL ;
      STR "Stop at position " ; INT pos ; STR " while reading " ; STR msg ; NL ;
      STR "Unprocessed: " ; STR unparsed ]))

  method private read = begin pos <- pos + 1 ; Char.code (IO.read ch) end

  method private next_char = 
    if pos = len then 
      char_la <- 0
      (* raise (BCH_failure (LBLOCK [ STR "End of string encountered. Current name: " ; 
				   cms#toPretty ] ))  *)
    else
      char_la <- self#read

  method private read_char expected_char =
    if char_la = expected_char then
      self#next_char
    else
      raise (BCH_failure (LBLOCK [ STR "Expected to see " ; INT expected_char ;
				   STR ", but found " ; INT char_la ]))

  method private check_char_la predicate msg =
    if predicate char_la then () else raise (BCH_failure msg)

  method private fill_name_buffer c = Buffer.add_char name_buffer (Char.chr c)

  method private check_end_of_string =
     if pos = len then () else 
       let unparsed = String.sub s pos ((String.length s) - pos) in
       self#stop ("leaving \"" ^ unparsed ^ "\" unparsed")

  method private read_name =
    begin
      Buffer.clear name_buffer ;
      self#check_char_la is_name_start_char
	(LBLOCK [ INT char_la ; STR " is not a valid starting character of a name "]) ;
      self#fill_name_buffer char_la ;
      self#next_char ;
      while is_name_char char_la do
	begin
	  self#fill_name_buffer char_la ;
	  self#next_char 
	end
      done;
      Buffer.contents name_buffer
    end

  method private read_class_method_name =
    let name = self#read_name in
    if String.contains name '.' then
      let index = String.rindex name '.' in
      let cname = String.sub name 0 index in
      let mname = String.sub name (index+1) (((String.length name) - index)  - 1) in
      begin
	cms#set_class_name cname ;
	cms#set_method_name mname
      end
    else
      cms#set_method_name name  

  method private read_object_name =
    let name = self#read_name in
    begin
      self#read_char c_semicolon ;
      make_class_name name
    end    

  method private read_value_type =
    if is_basic_type_encoding_char char_la then 
      let c = char_la in
      begin self#next_char ; TBasic (get_basic_type c) end
    else if char_la = c_L then
      begin self#next_char ; TObject (TClass self#read_object_name) end
    else if char_la = c_leftbracket then
      begin self#next_char ; TObject (TArray self#read_value_type) end
    else
      begin
	self#stop "Error in read_value_type" ;
	raise (BCH_failure (LBLOCK [ STR "Error in read_value_type"]))
      end

  method private read_arguments = 
    while is_start_type_encoding_char char_la do
      cms#add_argument_type self#read_value_type
    done

  method decode =
    begin
      self#next_char ;
      self#read_class_method_name ;
      if pos = len then
	() 
      else
	begin
	  self#read_char c_ampersand ;
	  self#read_char c_ampersand ;
	  self#read_arguments
	end
    end
      
end


let get_java_class_method_name (name:string) =
  let optName = convert_to_native_method_name name in
  match optName with
  | Some s -> 
    let decoder = new java_encoded_name_decoder_t s in
    begin
      decoder#decode ;
      Some decoder#get_name
    end
  | _ -> None

let noclasses = ref []
let nomethods = ref []
let classes = H.create 3

let get_java_classes_not_found () = List.sort Stdlib.compare !noclasses
let get_java_methods_not_found () = List.sort Stdlib.compare !nomethods

let get_java_classes_loaded () = 
  let l = ref [] in
  let _ = H.iter (fun _ v -> l := v :: !l) classes in
  !l

let write_xml_java_classes_loaded
      (node:xml_element_int) (jclasses:java_native_method_class_t list) =
  node#appendChildren (List.map (fun c ->
    let cNode = xmlElement "class" in
    begin write_xml_java_native_method_class cNode c ; cNode end) jclasses)

let get_java_class (name:string) =
  if H.mem classes name then 
    Some (H.find classes name )
  else if List.mem name !noclasses then 
    None
  else
    let filename = (replace_dot name) ^ ".xml" in
    let path = system_settings#get_jsignature_paths in
    match get_file_from_jar path filename with
    | Some jfile ->
      let jclass = read_xml_java_class_string jfile in
      begin
	chlog#add "load java class file" (LBLOCK [ STR name ]) ;
	H.add classes name jclass ;
	Some jclass
      end
    | _ -> 
      begin
	chlog#add "java class not found" (LBLOCK [ STR name ]) ;
	noclasses := name :: !noclasses ;
	None
      end

let arguments_match (api:java_native_method_api_t) (cms:java_method_name_int) =
  let sigArgs = api.jnm_signature#descriptor#arguments in
  let cmsArgs = cms#get_arguments in
  ((List.length sigArgs) = (List.length cmsArgs))  &&
    (List.for_all2 (fun t1 t2 -> (compare_value_types t1 t2) = 0) sigArgs cmsArgs)
  

let get_java_method_api (jclass:java_native_method_class_t) (cms:java_method_name_int) =
  let apis = List.filter (fun m -> m.jnm_signature#name = cms#get_method_name) 
    jclass.jnmc_native_methods in
  match apis with
  | [] ->
    begin
      chlog#add "java native method not found" (STR cms#get_method_name) ;
      nomethods := cms#get_method_name :: !nomethods ;
      None
    end
  | [ api ] when (not cms#has_arguments)  -> Some api
  | l when (not cms#has_arguments) ->
    begin
      chlog#add "multiple java native methods found" (STR cms#get_method_name) ;
      None
    end
  | _ -> 
    try
      Some (List.find (fun api -> arguments_match api cms) apis)
    with
      Not_found ->
	begin
	  chlog#add "no matching java native method" (STR cms#get_method_name) ;
	  None
	end
    
let get_java_native_method_signature (faddr:string) (names:string list) =
  let cmsList = List.fold_left (fun acc n ->
    match get_java_class_method_name n with
    | Some cms -> cms :: acc
    | _ -> acc) [] names in
  match cmsList with
  | [] -> 
    begin
      chlog#add "java native method signature" 
	(LBLOCK [ STR faddr ; STR ": " ; 
		  STR "Unable to extract signatures from " ; 
		  pretty_print_list names (fun s -> STR s) " " "," "" ]) ;
      None
    end
  | [ cms ] ->
    begin
      match get_java_class cms#get_class_name with
      | Some jclass ->	get_java_method_api jclass cms
      | _ -> None
    end
  | cms :: tl  -> 
    begin
      chlog#add "multiple names for function"
	(LBLOCK [ STR faddr ; STR " (" ; INT (List.length cmsList) ; STR " names): " ;
		  pretty_print_list names (fun s -> STR s) " " "," "" ]) ;
      match get_java_class cms#get_class_name with
      | Some jclass -> get_java_method_api jclass cms
      | _ -> None 
    end

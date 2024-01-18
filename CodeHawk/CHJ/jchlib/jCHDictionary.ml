(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet and Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny Sipma

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
open CHCommon
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHUtil
open CHXmlDocument
open CHXmlReader

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHSumTypeSerializer

module H = Hashtbl


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
    raise (XmlParseError (node#getLineNumber, node#getColumnNumber, msg))
  end


let byte_to_string (b:int) =
  let l = b mod 16 in
  let h = b lsr 4 in
  Printf.sprintf "%x%x" h l


let hex_string s =
  let ch = IO.input_string s in
  let h = ref "" in
  let len = String.length s in
  begin
    for i = 0 to len-1 do h := !h ^ (byte_to_string (IO.read_byte ch)) done;
    !h
  end


let has_control_characters s =
  let found = ref false in
  let _ = String.iter (fun c ->
              if ((Char.code c) < 32) || (Char.code c) > 126 then
      found  := true) s in
  !found


let mk_constantstring (s:string):constantstring =
  if has_control_characters s then
    (hex_string s, true, String.length s)
  else
    (s, false, String.length s)


let rec value_type_to_asm_string (v:value_type_t) =
  match v with
  | TBasic t -> java_basic_type_serializer#to_string t
  | TObject t -> object_type_to_asm_string t


and object_type_to_asm_string (v:object_type_t) =
  match v with
  | TClass cn -> "L" ^ (string_replace '.' "/" cn#name) ^ ";"
  | TArray vt -> "[" ^ (value_type_to_asm_string vt)


let method_descriptor_to_asm_string (md:method_descriptor_int) =
  String.concat "_" (List.map value_type_to_asm_string md#arguments)


class dictionary_t:dictionary_int =
object (self: _)

  val unrecognizedclassnames = H.create 3
  val convertedmethodnames = H.create 3
  val cached_classnames = H.create 3
  val cached_fieldsignatures = H.create 3
  val cached_methodsignatures = H.create 3
  val cached_classfieldsignatures = H.create 3
  val cached_classmethodsignatures = H.create 3

  val mutable unrecognizedclassindex = 0

  val string_table = mk_index_table "string-table"

  val class_name_table = mk_index_table "class-name-table"

  val field_signature_data_table =
    mk_index_table "field-signature-data-table"

  val method_signature_data_table =
    mk_index_table "method-signature-data-table"

  val class_field_signature_data_table =
    mk_index_table "class-field-signature-data-table"

  val class_method_signature_data_table =
    mk_index_table "class-method-signature-data-table"

  val object_type_table = mk_index_table "object-type-table"

  val value_type_table = mk_index_table "value-type-table"

  val method_descriptor_table = mk_index_table "method-descriptor-table"

  val descriptor_table = mk_index_table "descriptor-table"

  val constant_value_table = mk_index_table "constant-value-table"

  val method_handle_type_table = mk_index_table "method-handle-type-table"

  val constant_table = mk_index_table "constant-table"

  val bootstrap_argument_table = mk_index_table "bootstrap-argument-table"

  val bootstrap_method_data_table =
    mk_index_table "bootstrap-method-data-table"

  val mutable tables = []

  initializer
    tables <- [
      string_table;
      class_name_table;
      object_type_table;
      value_type_table;
      method_descriptor_table;
      descriptor_table;
      field_signature_data_table;
      method_signature_data_table;
      class_field_signature_data_table;
      class_method_signature_data_table;
      constant_value_table;
      method_handle_type_table;
      constant_table;
      bootstrap_argument_table;
      bootstrap_method_data_table
   ]

  method index_class_name (name:string) =
    let l =  ExtString.String.nsplit name "." in
    match l with
    | [] ->
       raise (JCH_failure (LBLOCK [STR "Error in split package: "; STR name]))
    | l -> class_name_table#add ([],List.map self#index_string l)

  method get_class_name (index:int) =
    let (_,args) = class_name_table#retrieve index in
    String.concat "." (List.map self#get_string args)

  method index_field_signature_data (d:field_signature_data_int) =
    let args = [self#index_string d#name; self#index_value_type d#descriptor] in
    field_signature_data_table#add ([],args)

  method get_field_signature_data (index:int) =
    let (_,args) = field_signature_data_table#retrieve index in
    let a = a "field-signature-data" args in
    let name = self#get_string (a 0) in
    let field_descriptor = self#get_value_type (a 1) in
    make_field_signature_data ~name ~field_descriptor

  method index_class_field_signature_data (d:class_field_signature_data_int) =
    let args = [d#class_name#index; d#field_signature#index] in
    class_field_signature_data_table#add ([],args)

  method get_class_field_signature_data (index:int) =
    let (_,args) = class_field_signature_data_table#retrieve index in
    let a = a "class-field-signature-data" args in
    let class_name = self#retrieve_class_name (a 0) in
    let field_signature = self#retrieve_field_signature (a 1) in
    make_class_field_signature_data ~class_name ~field_signature

  method index_method_signature_data (d:method_signature_data_int) =
    let args = [
        self#index_string d#name;
        self#index_method_descriptor d#descriptor;
        if d#is_static then 1 else 0]  in
    method_signature_data_table#add ([],args)

  method get_method_signature_data (index:int) =
    let (_,args) = method_signature_data_table#retrieve index in
    let a = a "method-signature-data" args in
    let name = self#get_string (a 0) in
    let method_descriptor = self#get_method_descriptor (a 1) in
    let is_static = (a 2) = 1 in
    make_method_signature_data ~is_static ~name ~method_descriptor

  method index_class_method_signature_data (d:class_method_signature_data_int) =
    let args = [d#class_name#index; d#method_signature#index] in
    class_method_signature_data_table#add ([],args)

  method get_class_method_signature_data (index:int) =
    let (_,args) = class_method_signature_data_table#retrieve index in
    let a  = a "class-method-signature-data" args in
    let class_name = self#retrieve_class_name (a 0) in
    let method_signature = self#retrieve_method_signature (a 1) in
    make_class_method_signature_data ~class_name ~method_signature

  method index_object_type (t:object_type_t) =
    let tags = [object_type_serializer#to_string t] in
    let key = match t with
      | TClass cn -> (tags,[cn#index])
      | TArray vt -> (tags,[self#index_value_type vt]) in
    object_type_table#add key

  method get_object_type (index:int) =
    let (tags,args) = object_type_table#retrieve index in
    let t = t "object-type" tags in
    let a = a "object-type" args in
    match (t 0) with
    | "c" -> TClass (self#retrieve_class_name (a 0))
    | "a" -> TArray (self#get_value_type (a 0))
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "object-type tag "; STR s; STR " not recognized"]))

  method write_xml_object_type
           ?(tag="iobj") (node:xml_element_int) (t:object_type_t) =
    node#setIntAttribute tag (self#index_object_type t)

  method read_xml_object_type
           ?(tag="iobj") (node:xml_element_int):object_type_t =
    self#get_object_type (node#getIntAttribute tag)

  method index_value_type (t:value_type_t) =
    let tags = [value_type_serializer#to_string t] in
    let key = match t with
      | TBasic b -> (tags @ [java_basic_type_serializer#to_string b],[])
      | TObject o -> (tags,[self#index_object_type o]) in
    value_type_table#add key

  method get_value_type (index:int) =
    let (tags,args) = value_type_table#retrieve index in
    let t = t "value-type" tags in
    let a = a "value-type" args in
    match (t 0) with
    | "b" -> TBasic (java_basic_type_serializer#from_string (t 1))
    | "o" -> TObject (self#get_object_type (a 0))
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "value-type tag "; STR s; STR " not recognized"]))

  method write_xml_value_type
           ?(tag="ivty") (node:xml_element_int) (t:value_type_t) =
    node#setIntAttribute tag (self#index_value_type t)

  method read_xml_value_type
           ?(tag="ivty") (node:xml_element_int):value_type_t =
    self#get_value_type (node#getIntAttribute tag)

  method index_method_descriptor (d:method_descriptor_int) =
    let rv = match d#return_value with
      | Some vt -> [1; self#index_value_type vt]
      | _ -> [0] in
    let args = List.map self#index_value_type d#arguments in
    method_descriptor_table#add ([],rv @ args)

  method get_method_descriptor (index:int) =
    let (_,args) = method_descriptor_table#retrieve index in
    let a = a "object-type" args in
    let (rv,argixs) =
      if (a 0) = 0 then (None, List.tl args)
      else
        (Some (self#get_value_type (a 1)), List.tl (List.tl args)) in
    let arguments = List.map self#get_value_type argixs in
    match rv with
    | Some return_value -> make_method_descriptor ~arguments ~return_value ()
    | _ -> make_method_descriptor ~arguments ()

  method write_xml_method_descriptor
           ?(tag="imd") (node:xml_element_int) (d:method_descriptor_int) =
    node#setIntAttribute tag (self#index_method_descriptor d)

  method read_xml_method_descriptor
           ?(tag="imd") (node:xml_element_int):method_descriptor_int =
    self#get_method_descriptor (node#getIntAttribute tag)

  method index_descriptor (d:descriptor_t) =
    let tags = [descriptor_serializer#to_string d] in
    let key = match d with
      | SValue vt -> (tags,[self#index_value_type vt])
      | SMethod md -> (tags,[self#index_method_descriptor md]) in
    descriptor_table#add key

  method get_descriptor (index:int):descriptor_t =
    let (tags,args) = descriptor_table#retrieve index in
    let t = t "descriptor" tags in
    let a = a "descriptor" args in
    match (t 0) with
    | "v" -> SValue (self#get_value_type (a 0))
    | "m" -> SMethod (self#get_method_descriptor (a 0))
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "descriptor tag "; STR s; STR " not recognized"]))

  method write_xml_descriptor
           ?(tag="id") (node:xml_element_int) (d:descriptor_t) =
    node#setIntAttribute tag (self#index_descriptor d)

  method read_xml_descriptor ?(tag="id") (node:xml_element_int):descriptor_t =
    self#get_descriptor (node#getIntAttribute tag)

  method index_constant_value (cv:constant_value_t) =
    let tags = [constant_value_serializer#to_string cv] in
    let key = match cv with
      | ConstString s -> (tags, [self#index_string s])
      | ConstInt i32 -> (tags, [Int32.to_int i32])
      | ConstFloat f -> (tags @ [string_of_float f], [])
      | ConstLong i64 -> (tags @ [Int64.to_string i64], [])
      | ConstDouble d -> (tags @ [string_of_float d], [])
      | ConstClass ot -> (tags, [self#index_object_type ot]) in
    constant_value_table#add key

  method get_constant_value (index:int) =
    let (tags,args) = constant_value_table#retrieve index in
    let t = t "constant-value" tags in
    let a = a "constant-value" args in
    match (t 0) with
    | "s" -> ConstString (self#get_string (a 0))
    | "i" -> ConstInt (Int32.of_int (a 0))
    | "f" -> ConstFloat (float_of_string (t 1))
    | "l" -> ConstLong (Int64.of_string (t 1))
    | "d" -> ConstDouble (float_of_string (t 1))
    | "c" -> ConstClass (self#get_object_type (a 0))
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "Constant value tag "; STR s; STR " not recognized"]))

  method write_xml_constant_value
           ?(tag="icv") (node:xml_element_int) (cv:constant_value_t) =
    node#setIntAttribute tag (self#index_constant_value cv)

  method read_xml_constant_value
           ?(tag="icv") (node:xml_element_int):constant_value_t =
    self#get_constant_value (node#getIntAttribute tag)

  method index_method_handle_type (h:method_handle_type_t) =
    let tags = [method_handle_type_serializer#to_string h] in
    let key = match h with
      | FieldHandle (cn,fs) -> (tags,[cn#index; fs#index])
      | MethodHandle (ot,ms) -> (tags,[self#index_object_type ot; ms#index])
      | InterfaceHandle (cn,ms) -> (tags,[cn#index; ms#index]) in
    method_handle_type_table#add key

  method get_method_handle_type (index:int):method_handle_type_t =
    let (tags,args) = method_handle_type_table#retrieve index in
    let t = t "method-handle-type" tags in
    let a = a "method-handle-type" args in
    match (t 0) with
    | "f" ->
       FieldHandle(
           self#retrieve_class_name (a 0),
           self#retrieve_field_signature (a 1))
    | "m" ->
       MethodHandle(
           self#get_object_type (a 0),
           self#retrieve_method_signature (a 1))
    | "i" ->
       InterfaceHandle(
           self#retrieve_class_name (a 0),
           self#retrieve_method_signature (a 1))
    | s ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "Method handle type tag ";
                 STR s;
                 STR " not recognized"]))

  method write_xml_method_handle_type
           ?(tag="imh") (node:xml_element_int) (h:method_handle_type_t) =
    node#setIntAttribute tag (self#index_method_handle_type h)

  method read_xml_method_handle_type
           ?(tag="imh") (node:xml_element_int):method_handle_type_t =
    self#get_method_handle_type (node#getIntAttribute tag)

  method index_constant (c:constant_t) =
    let tags = [constant_serializer#to_string c] in
    let key = match c with
      | ConstValue cv -> (tags, [self#index_constant_value cv])
      | ConstField (cn,fs) -> (tags, [cn#index; fs#index])
      | ConstMethod (ot,ms)-> (tags, [self#index_object_type ot; ms#index])
      | ConstInterfaceMethod (cn,ms) -> (tags, [cn#index; ms#index])
      | ConstDynamicMethod (index,ms) -> (tags, [index; ms#index])
      | ConstNameAndType (s,d) ->
         (tags, [self#index_string s; self#index_descriptor d])
      | ConstStringUTF8 s -> (tags,[self#index_string s])
      | ConstMethodHandle (k,h) ->
         (tags @ [reference_kind_serializer#to_string k],
          [self#index_method_handle_type h])
      | ConstMethodType md -> (tags, [self#index_method_descriptor md])
      | ConstUnusable -> (tags,[]) in
    constant_table#add key

  method get_constant (index:int):constant_t =
    let (tags,args) = constant_table#retrieve index in
    let t = t "constant" tags in
    let a = a "constant" args in
    match (t 0) with
    | "v" -> ConstValue (self#get_constant_value (a 0))
    | "f" ->
       ConstField (self#retrieve_class_name (a 0),
                   self#retrieve_field_signature (a 1))
    | "m" ->
       ConstMethod (self#get_object_type (a 0),
                    self#retrieve_method_signature (a 1))
    | "i" ->
       ConstInterfaceMethod (self#retrieve_class_name (a 0),
                             self#retrieve_method_signature (a 1))
    | "d" -> ConstDynamicMethod (a 0, self#retrieve_method_signature (a 1))
    | "n" -> ConstNameAndType (self#get_string (a 0), self#get_descriptor (a 1))
    | "s" -> ConstStringUTF8 (self#get_string (a 0))
    | "h" -> ConstMethodHandle (reference_kind_serializer#from_string (t 1),
                                self#get_method_handle_type (a 0))
    | "t" -> ConstMethodType (self#get_method_descriptor (a 0))
    | "u" -> ConstUnusable
    | s ->
       raise
         (JCH_failure
            (LBLOCK [STR "Constant tag "; STR s; STR " not recognized"]))

  method write_xml_constant ?(tag="ict") (node:xml_element_int) (c:constant_t) =
    node#setIntAttribute tag (self#index_constant c)

  method read_xml_constant ?(tag="ict") (node:xml_element_int):constant_t =
    self#get_constant (node#getIntAttribute tag)

  method index_bootstrap_argument (a:bootstrap_argument_t) =
    let tags = [bootstrap_argument_serializer#to_string a] in
    let key = match a with
      | BootstrapArgConstantValue cv -> (tags,[self#index_constant_value cv])
      | BootstrapArgMethodHandle (k,h) ->
         (tags @ [reference_kind_serializer#to_string k],
          [self#index_method_handle_type h])
      | BootstrapArgMethodType md -> (tags,[self#index_method_descriptor md]) in
    bootstrap_argument_table#add key

  method get_bootstrap_argument (index:int) =
    let (tags,args) = bootstrap_argument_table#retrieve index in
    let t = t "bootstrap-argument" tags in
    let a = a "bootstrap-argument" args in
    match (t 0) with
    | "c" -> BootstrapArgConstantValue (self#get_constant_value (a 0))
    | "h" ->
       BootstrapArgMethodHandle (
           reference_kind_serializer#from_string (t 1),
           self#get_method_handle_type (a 0))
    | "t" ->
       BootstrapArgMethodType (self#get_method_descriptor (a 0))
    | s ->
       raise
         (JCH_failure
            (LBLOCK [
                 STR "Bootstrap argument tag ";
                 STR s;
                 STR " not recognized"]))

  method write_xml_bootstrap_argument
           ?(tag="iba") (node:xml_element_int) (a:bootstrap_argument_t) =
    node#setIntAttribute tag (self#index_bootstrap_argument a)

  method read_xml_bootstrap_argument
           ?(tag="iba") (node:xml_element_int):bootstrap_argument_t =
    self#get_bootstrap_argument (node#getIntAttribute tag)

  method index_bootstrap_method_data (d:bootstrap_method_data_t) =
    let tags = [reference_kind_serializer#to_string d.bm_kind] in
    let args = (self#index_method_handle_type d.bm_handle) ::
                 (List.map self#index_bootstrap_argument d.bm_args) in
    bootstrap_method_data_table#add (tags,args)

  method get_bootstrap_method_data (index:int) =
    let (tags,args) = bootstrap_method_data_table#retrieve index in
    let t = t "bootstrap-method-data" tags in
    let a = a "bootstrap-method-data" args in
    { bm_kind = reference_kind_serializer#from_string (t 0);
      bm_handle = self#get_method_handle_type (a 0);
      bm_args = List.map self#get_bootstrap_argument (List.tl args) }

  method write_xml_bootstrap_method_data
           ?(tag="ibm") (node:xml_element_int) (d:bootstrap_method_data_t) =
    node#setIntAttribute tag (self#index_bootstrap_method_data d)

  method read_xml_bootstrap_method_data
           ?(tag="ibm") (node:xml_element_int):bootstrap_method_data_t =
    self#get_bootstrap_method_data (node#getIntAttribute tag)

  method index_string (s:string):int =
    let cs = mk_constantstring s in
    let (s,ishex,len) = cs in
    let x = if ishex then ["x"] else [] in
    let tags = if len = 0 then [] else [s] @ x in
    let args = [len] in
    string_table#add (tags,args)

  method get_string (index:int) =
    let (tags,args) = string_table#retrieve index in
    let (s,_,_) = if (List.length tags) > 0  && (List.length args) > 0 then
      (List.hd tags, List.length tags > 1, List.hd args)
    else if (List.length args) > 0 && (List.hd args) = 0 then  (* empty string *)
      ("", false, 0)
    else if (List.length args) > 0 then
      (" ", false, (List.hd args))              (* string of spaces of lengt n *)
    else
      raise
        (JCH_failure
           (LBLOCK [STR "Invalid string record: "; INT (List.hd args)])) in
    s

  method write_xml_string ?(tag="istr") (node:xml_element_int) (s:string) =
    node#setIntAttribute tag (self#index_string s)

  method private read_xml_string ?(tag="istr") (node:xml_element_int):string =
    self#get_string (node#getIntAttribute tag)

  method private make_substitute_cn (cn:string) =
    if H.mem unrecognizedclassnames cn then
      H.find unrecognizedclassnames cn
    else
      let name = "__cn__" ^ (string_of_int unrecognizedclassindex) in
      begin
	unrecognizedclassindex <- unrecognizedclassindex + 1;
	H.add unrecognizedclassnames cn name;
	name
      end

  method private check_method_name_encoding (name:string) =
    if H.mem convertedmethodnames name then
      H.find convertedmethodnames name
    else if has_control_characters name then
      let newname = "__xx__" ^ (hex_string name) in
      begin
	H.add convertedmethodnames name newname;
	newname
      end
    else
      name

  method list_unrecognized_class_names =
    let lst = ref [] in
    let _ = H.iter (fun k v -> lst := (k,v) :: !lst) unrecognizedclassnames in
    List.sort (fun (k1, _) (k2, _) -> Stdlib.compare k1 k2) !lst

  method list_converted_method_names =
    let lst = ref [] in
    let _ = H.iter (fun k v -> lst := (k,v) :: !lst) convertedmethodnames in
    List.sort (fun (k1, _) (k2, _) -> Stdlib.compare k1 k2) !lst

  method list_class_names =
    H.fold (fun _ v acc -> v :: acc) cached_classnames []

  method private cache_class_name (index:int) (name:string) =
    if H.mem cached_classnames index then
      H.find cached_classnames index
    else
      let cn = make_class_name ~index ~name in
      begin
        H.add cached_classnames index cn;
        cn
      end

  method private retrieve_cached_class_name (index:int) =
    if H.mem cached_classnames index then
      H.find cached_classnames index
    else
      raise (JCH_failure (LBLOCK [STR "Cached class name "; INT index;
                                   STR " not found"]))

  method make_class_name (cn:string) =
    let valid_class_name =
      (* Str.regexp "^\\([a-zA-Z_$-][a-zA-Z_$0-9-]*\\.\\)*\\([a-zA-Z_0-9-]+\\$\\)*[a-zA-Z_0-9-]+$" *)
      Str.regexp "^\\([a-zA-Z_$-][a-zA-Z_$0-9-]*\\.\\)*\\([a-zA-Z_$0-9-]+\\$\\)*[a-zA-Z_$0-9-]+$"
    in
      if not (Str.string_match valid_class_name cn 0) then
	let substitute_cn = self#make_substitute_cn cn in
	let _ =
          pr_debug [
              STR cn;
              STR " is not recognized as a valid name for a class; ";
              NL;
	      STR "replacing it with ";
              STR substitute_cn;
              NL] in
        let index = self#index_class_name substitute_cn in
        self#cache_class_name index substitute_cn
      else
        let index = self#index_class_name cn in
        self#cache_class_name index cn

  method retrieve_class_name index =
    if H.mem cached_classnames index then
      H.find cached_classnames index
    else
      let cn = self#get_class_name index in
      self#cache_class_name  index cn

  method retrieve_method_signature index =
    if H.mem cached_methodsignatures index then
      H.find cached_methodsignatures index
    else
      let msd = self#get_method_signature_data index in
      self#cache_method_signature index msd

  method retrieve_field_signature index =
    if H.mem cached_fieldsignatures index then
      H.find cached_fieldsignatures index
    else
      let fsd = self#get_field_signature_data index in
      self#cache_field_signature index fsd

  method retrieve_class_field_signature index =
    if H.mem cached_classfieldsignatures index then
      H.find cached_classfieldsignatures index
    else
      let cfsd = self#get_class_field_signature_data index in
      self#cache_class_field_signature index cfsd

  method retrieve_class_method_signature index =
    if H.mem cached_classmethodsignatures index then
      H.find cached_classmethodsignatures index
    else
      let cmsd = self#get_class_method_signature_data index in
      self#cache_class_method_signature index cmsd

  method private cache_field_signature
                   (index:int) (fsd:field_signature_data_int) =
    if H.mem cached_fieldsignatures index then
      H.find cached_fieldsignatures index
    else
      let fs = make_field_signature ~index ~field_signature_data:fsd in
      begin
        H.add cached_fieldsignatures index fs;
        fs
      end

  method make_field_signature name fdesc =
    let fsd = make_field_signature_data ~name ~field_descriptor:fdesc in
    let index = self#index_field_signature_data fsd in
    self#cache_field_signature index fsd

  method private cache_method_signature
                   (index:int) (msd:method_signature_data_int) =
    if H.mem cached_methodsignatures index then
      H.find cached_methodsignatures index
    else
      let ms = make_method_signature ~index ~method_signature_data:msd in
      begin
        H.add cached_methodsignatures index ms;
        ms
      end

  method make_method_signature is_static name mdesc =
    let name = self#check_method_name_encoding name in
    let msd =
      make_method_signature_data ~is_static ~name ~method_descriptor:mdesc in
    let index = self#index_method_signature_data msd in
    self#cache_method_signature index msd

  method private cache_class_field_signature
                   (index:int) (cfsd:class_field_signature_data_int) =
    if H.mem cached_classfieldsignatures index then
      H.find cached_classfieldsignatures index
    else
      let cfs =
        make_class_field_signature ~index ~class_field_signature_data:cfsd in
      begin
        H.add cached_classfieldsignatures index cfs;
        cfs
      end

  method make_class_field_signature class_name fsig =
    let cfsd =
      make_class_field_signature_data ~class_name ~field_signature:fsig in
    let index = self#index_class_field_signature_data cfsd in
    self#cache_class_field_signature index cfsd

  method private cache_class_method_signature
                   (index:int) (cmsd:class_method_signature_data_int) =
    if H.mem cached_classmethodsignatures index then
      H.find cached_classmethodsignatures index
    else
      let cms =
        make_class_method_signature ~index ~class_method_signature_data:cmsd in
      begin H.add cached_classmethodsignatures index cms; cms end

  method make_class_method_signature class_name msig =
    let cmsd =
      make_class_method_signature_data ~class_name ~method_signature:msig in
    let index = self#index_class_method_signature_data cmsd in
    self#cache_class_method_signature index cmsd

  method get_method_signatures =
    H.fold (fun _ v acc -> v::acc) cached_methodsignatures []

  method private write_xml_type_dictionary (node:xml_element_int) =
    node#appendChildren
      (List.map
         (fun t ->
           let tnode = xmlElement t#get_name in
           begin
             t#write_xml tnode;
             tnode
           end) tables)

  method write_xml (node:xml_element_int) =
    let append = node#appendChildren in
    let ttNode = xmlElement "type-dictionary" in
    begin
      self#write_xml_type_dictionary ttNode;
      append [ttNode];
    end

  method private read_xml_type_dictionary (node:xml_element_int) =
    let getc = node#getTaggedChild in
    List.iter (fun t -> t#read_xml (getc t#get_name)) tables

  method read_xml (node:xml_element_int) =
    let getc = node#getTaggedChild in
    self#read_xml_type_dictionary (getc "type-dictionary");

end


let common_dictionary = new dictionary_t

let make_cn  = common_dictionary#make_class_name
let make_ms  = common_dictionary#make_method_signature
let make_cms = common_dictionary#make_class_method_signature
let make_fs  = common_dictionary#make_field_signature
let make_cfs = common_dictionary#make_class_field_signature

let retrieve_cn  = common_dictionary#retrieve_class_name
let retrieve_ms  = common_dictionary#retrieve_method_signature
let retrieve_cms = common_dictionary#retrieve_class_method_signature
let retrieve_cfs = common_dictionary#retrieve_class_field_signature


let list_class_names () = common_dictionary#list_class_names


let rec read_xmlx_value_type (node:xml_element_int) =
  match node#getChild#getTag with
  | "array" -> TObject (TArray (read_xmlx_value_type node#getChild))
  | "object" -> TObject (TClass (make_cn node#getChild#getText))
  | s ->
    try
      TBasic (java_basic_type_of_string s)
    with
    | JCH_failure p ->
       raise_xml_error node (LBLOCK [STR "Error in reading value type: "; p])


let read_xmlx_object_type (node:xml_element_int) =
  match node#getChild#getTag with
  | "array" -> TArray (read_xmlx_value_type node#getChild)
  | "object" -> TClass (make_cn node#getChild#getText)
  | s ->
     raise_xml_error node
       (LBLOCK [
            STR "Error in reading object type: tag ";
            STR s;
            STR " not recognized"])


let read_xmlx_method_descriptor (node:xml_element_int) =
  let hasc = node#hasOneTaggedChild in
  let getc = node#getTaggedChild in
  let getcc = node#getTaggedChildren in
  let argtypes = List.map (fun n ->
    let geti = n#getIntAttribute in
    let nr = geti "nr" in
    let ty = read_xmlx_value_type n in
    (nr,ty)) (getcc "arg") in
  let argtypes = List.map (fun (_,t) -> t)
  (List.sort (fun (i1,_) (i2,_) -> Stdlib.compare i1 i2) argtypes) in
  let returnType =
    if hasc "return" then
      Some (read_xmlx_value_type (getc "return"))
    else
      None in
  (argtypes, returnType)


let read_xmlx_method_signature
    (node:xml_element_int) (name:string) (isstatic:bool):method_signature_int =
  let (args,rettype) = read_xmlx_method_descriptor node in
  let descr = match rettype with
    | Some r -> make_method_descriptor ~arguments:args ~return_value:r ()
    | _ -> make_method_descriptor ~arguments:args () in
  make_ms isstatic name descr


let read_xmlx_constructor_signature (node:xml_element_int) (cn:class_name_int) =
  let getc = node#getTaggedChild in
  let ms = read_xmlx_method_signature (getc "signature") "<init>" false in
  make_cms cn ms


let read_xmlx_class_method_signature (node:xml_element_int) (cn:class_name_int) =
  let get = node#getAttribute in
  let has = node#hasNamedAttribute in
  let getc = node#getTaggedChild in
  let name = get "name" in
  let isstatic = has "static" && (get "static") = "yes" in
  let ms = read_xmlx_method_signature (getc "signature") name isstatic in
  make_cms cn ms

(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma

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
open CHNumerical
open CHPretty

(* chutil *)
open CHIndexTable
open CHLogger
open CHXmlDocument
open CHStringIndexTable

(* jchlib  *)
open JCHBasicTypes
open JCHBasicTypesAPI
open JCHBytecode
open JCHDictionary
open JCHSumTypeSerializer
   
(* jchfeatures *)
open  JCHFeaturesAPI
open JCHFeatureSumTypeSerializer

module H = Hashtbl


class feature_dictionary_t:feature_dictionary_int =
object (self)

  val class_name_table = mk_index_table "class-name-table"
  val object_type_table = mk_index_table "object-type-table"
  val value_type_table = mk_index_table "value-type-table"
  val fs_table = mk_index_table "fs-table"
  val ms_table = mk_index_table "ms-table"
  val cfs_table = mk_index_table "cfs-table"
  val cms_table = mk_index_table "cms-table"
  val opcode_table = mk_index_table "opcode-table"
  val constant_value_table  = mk_index_table "constant-value-table"
  val fxfeature_table = mk_index_table "fxfeature-table"
  val fxpr_table = mk_index_table "fxpr-table"
  val string_table = mk_string_index_table "string-table"

  val mutable tables = []

  initializer
    tables <- [
      class_name_table ;
      object_type_table ;
      value_type_table ;
      fs_table ;
      cfs_table ;
      ms_table ;
      cms_table ;
      opcode_table ;
      constant_value_table ;
      fxpr_table ;      
      fxfeature_table
    ]

  method index_string (s:string):int = string_table#add s

  method index_class_name (cn:class_name_int) =
    let key = ([],
               (self#index_string cn#simple_name)
               :: (List.map  self#index_string cn#package)) in
    class_name_table#add key

  method index_object_type (b:object_type_t) =
    let key = match b with
      | TClass cn -> ( ["c" ], [ self#index_class_name cn ])
      | TArray v ->  ( ["a" ], [ self#index_value_type v ]) in
    object_type_table#add key

  method index_value_type (v:value_type_t) =
    let key = match v with
      | TBasic t -> ( [ "b" ; java_basic_type_serializer#to_string t ], [])
      | TObject b -> ( [ "o" ], [ self#index_object_type b ]) in
    value_type_table#add key

  method index_field_signature (fs:field_signature_int) =
    let key = ([], [ self#index_string fs#name ;
                     self#index_value_type fs#descriptor ]) in
    fs_table#add key

  method index_method_signature (ms:method_signature_int) =
    let returntype = match ms#descriptor#return_value with
      | Some v -> v | _ -> TBasic Void in
    let key = ([],
               (self#index_string ms#name)
               :: (self#index_value_type returntype)
               :: (List.map self#index_value_type ms#descriptor#arguments)) in
    ms_table#add key

  method index_class_field_signature (cfs:class_field_signature_int) =
    let key = ([],
               [ self#index_class_name cfs#class_name ;
                 self#index_field_signature cfs#field_signature ]) in
    cfs_table#add key

  method index_class_method_signature (cms:class_method_signature_int) =
    let key = ([],
               [ self#index_class_name cms#class_name ;
                 self#index_method_signature cms#method_signature ]) in
    cms_table#add key

  method index_opcode (opc:opcode_t) =
    let tags = [ hex_of_opcode opc ] in
    let key = match opc with
      | OpInstanceOf b -> (tags, [ self#index_object_type b ])
      | OpNew cn -> (tags, [ self#index_class_name cn ])
      | OpNewArray t -> (tags, [ self#index_value_type t ])
      | OpAMultiNewArray (t,n) ->
         (tags, [ self#index_object_type t ; n ])
      | OpAdd _ | OpSub _ | OpMult _ | OpDiv _ | OpRem _ | OpNeg _ ->
         ([ hex_of_arithmetic_opcode opc ],[])
      | opc when is_test_opcode opc -> (tags, [ get_target_offset opc ])
      | _ -> (tags,[]) in
    opcode_table#add key

  method index_constant_value(c:constant_value_t):int =
    let tags = [ constant_value_serializer#to_string c ] in
    let key = match c with
      | ConstString s -> (tags, [ self#index_string s ])
      | ConstInt i32 -> (tags, [ Int32.to_int i32 ])
      | ConstFloat f -> (tags @ [ string_of_float f ], [])
      | ConstLong i64 -> (tags  @ [ Int64.to_string i64 ], [])
      | ConstDouble f -> (tags @ [ string_of_float f ], [])
      | ConstClass b -> (tags, [ self#index_object_type b ]) in
    constant_value_table#add key

  method index_fxpr (x:fxpr_t):int =
    let tags = [ fxpr_serializer#to_string x ] in
    let key = match x with
      | FXVar t -> (tags,[ self#index_value_type t ])
      | FXField cfs -> (tags,[ self#index_class_field_signature cfs ])
      | FXArrayElem (t,a,i) ->
         (tags @ [ java_basic_type_serializer#to_string t ],
          [ self#index_fxpr a ; self#index_fxpr i ])
      | FXConst c -> (tags,[ self#index_constant_value c ])
      | FXOp (opc,args) ->
         (tags,(self#index_opcode opc) :: (List.map self#index_fxpr args))
      | FXFunctionCall (cms,args) ->
         (tags,
          (self#index_class_method_signature cms)
          :: (List.map self#index_fxpr args))
      | FXAttr (s,x) -> (tags,[ self#index_string s ; self#index_fxpr x ])
      | FXMultiple l -> (tags, List.map self#index_fxpr l)
      | FXException -> (tags,[])
      | FXNull ->  (tags,[])
      | FXUnknown -> (tags,[]) in
    fxpr_table#add key
                                   
  method index_fxfeature (fxf:fxfeature_t):int =
    let tags = [ fxfeature_serializer#to_string fxf ] in
    let key = match fxf with
      | FXCondition c -> (tags,[ self#index_fxpr c ])
      | FXAssignment (lhs,rhs) ->
         (tags,[ self#index_fxpr lhs ; self#index_fxpr rhs ])
      | FXProcedureCall (cms,args) ->
         let iargs = List.map  self#index_fxpr args in
         (tags, (self#index_class_method_signature  cms) :: iargs)
      | FXReturn (Some x) -> (tags, [ self#index_fxpr x ])
      | FXReturn None -> (tags, [ (-1) ])
      | FXThrow x -> (tags, [ self#index_fxpr x ]) in
    fxfeature_table#add key

  method write_xml_class_name
           ?(tag="icn") (node:xml_element_int) (cn:class_name_int) =
    node#setIntAttribute tag (self#index_class_name cn)

  method write_xml_method_signature
           ?(tag="ims") (node:xml_element_int) (ms:method_signature_int) =
    node#setIntAttribute tag (self#index_method_signature ms)

  method write_xml_fxfeature
           ?(tag="f") (node:xml_element_int) (fxf:fxfeature_t) =
    node#setIntAttribute tag (self#index_fxfeature fxf)

  method write_xml (node:xml_element_int) =
    let snode = xmlElement string_table#get_name in
    begin
      string_table#write_xml snode ;
      node#appendChildren [ snode ] ;
      node#appendChildren
        (List.map
           (fun t ->
             let tnode = xmlElement t#get_name in
             begin t#write_xml tnode ; tnode end) tables)
    end
      
end


let mk_feature_dictionary () = new feature_dictionary_t

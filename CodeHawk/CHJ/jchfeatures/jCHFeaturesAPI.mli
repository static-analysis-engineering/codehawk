(* =============================================================================
   CodeHawk Java Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024-2025 Aarno Labs LLC

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

(** Extract key-value pairs from class files *)

(* chutil *)
open CHXmlDocument

(* jchlib *)
open  JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

type feature_value_t =
| IntFeature of int
| FloatFeature of int * float

type key_value_pair_t = string * feature_value_t

type feature_values_set_t = string * key_value_pair_t list


class type loop_features_int =
object
  method get_size: int                       (* number of feature sets *)
  method count_key_value_pairs: int
  method generate_features: unit
  method write_xml: xml_element_int -> unit
end


(** Features associated with methods.

   {b Features provided}
   - bc : bytecode frequencies (key: opcode, val: freq)
   - bc1: bytecode pair frequencies (key: opcode pair, val: freq)
   - bc2: bytecode triple frequencies (key: opcode triple, val: freq)
   - api-types: types of arguments, return value  (key:type, val: count)
   - op-types: types of operations (key:type, val:count)
   - libcalls: calls to library functions (key:libname, val: freq)
   - sizes: number of loops, instrs, virtual, interface calls (key:name, val:count)
   - attrs: attributes of the method (key:attr-name, val:1 if present)
 *)
class type method_features_int =
object
  method get_method_info: method_info_int
  method get_feature: string -> key_value_pair_t list
  method generate_features: unit
  method get_size : int     (* number of feature sets *)
  method count_key_value_pairs: int
  method get_name : string
  method get_byte_count: int
  method get_instruction_count: int
  method get_interface_call_count: int
  method get_virtual_call_count: int
  method get_loop_count: int
  method get_subgraph_count: int
  method get_state_count: int
  method get_edge_count: int
  method get_complexity: int
  method get_max_depth : int
  method is_native : bool
  method failed_to_translate: bool
  method write_xml: xml_element_int -> unit
end


(** Features associated with classes.

   {b Features provided}
   - bc : bytecode frequencies (key: opcode, val: freq)
   - bc1: bytecode pair frequencies (key: opcode pair, val: freq)
   - bc2: bytecode triple frequencies (key: opcode triple, val: freq)
   - types: types of arguments, return value, operations (key:type, val: freq)
   - libcalls: calls to library functions (key:libname, val: count)
   - sizes: number of methods, fields, native-methods, loops (key:name, val:count)
   - attrs: attributes of the class (key:attr-name, val:1 if present)
 *)
class type class_features_int =
object
  method get_class_info: class_info_int
  method generate_features: unit
  method get_method_features: method_features_int list
  method get_bc_method_count: int
  method get_native_methods : (string * string * string) list
  method get_loop_count: int
  method get_max_depth: int
  method get_max_complexity: int
  method get_size : int                (* number of feature sets *)
  method count_key_value_pairs: int
  method write_xml: xml_element_int -> unit
end


type fxpr_t =
  | FXVar of value_type_t
  | FXField of class_field_signature_int
  | FXArrayElem of java_basic_type_t * fxpr_t * fxpr_t
  | FXConst of constant_value_t
  | FXOp of opcode_t * fxpr_t list
  | FXFunctionCall of class_method_signature_int * fxpr_t list
  | FXAttr of  string * fxpr_t
  | FXMultiple of fxpr_t list
  | FXException
  | FXNull
  | FXUnknown


type fxfeature_t =
  | FXCondition of fxpr_t
  | FXAssignment of fxpr_t * fxpr_t
  | FXProcedureCall of class_method_signature_int * fxpr_t list
  | FXThrow of fxpr_t
  | FXReturn of fxpr_t option


class type feature_dictionary_int =
  object
    method index_string: string -> int
    method index_class_name: class_name_int -> int
    method index_value_type: value_type_t -> int
    method index_object_type: object_type_t -> int
    method index_field_signature: field_signature_int -> int
    method index_method_signature: method_signature_int -> int
    method index_class_field_signature: class_field_signature_int -> int
    method index_class_method_signature: class_method_signature_int -> int
    method index_opcode:  opcode_t -> int
    method index_constant_value: constant_value_t -> int
    method index_fxpr: fxpr_t  -> int
    method index_fxfeature: fxfeature_t -> int
    method write_xml_class_name:
             ?tag:string ->  xml_element_int -> class_name_int -> unit
    method write_xml_method_signature:
             ?tag:string -> xml_element_int -> method_signature_int -> unit
    method write_xml_fxfeature:
             ?tag:string -> xml_element_int -> fxfeature_t -> unit
    method write_xml: xml_element_int -> unit
  end

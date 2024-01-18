(* =============================================================================
   CodeHawk Java Analyzer
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma

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

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI


class attributes_t
  ~(is_synthetic: bool)
  ~(is_deprecated: bool)
  ~(other: (string * string) list):attributes_int
  =
object

  method is_synthetic = is_synthetic

  method is_deprecated = is_deprecated

  method other = other

end

let make_attributes = new attributes_t


class method_annotations_t
  ~(global: (annotation_t * bool (* visibility *)) list)
  ~(parameters: (annotation_t * bool (* visibility *)) list list):method_annotations_int
  =
object

  method global = global

  method parameters = parameters

end

let make_method_annotations = new method_annotations_t


let implementation_to_pretty = function
  | Native -> STR "native"
  | Bytecode bc -> bc#toPretty


class virtual method_t
  ~(signature: method_signature_int)
  ~(class_method_signature: class_method_signature_int)
  ~(access: access_t)
  ?(generic_signature: method_type_signature_int option)
  ~(is_bridge: bool)
  ~(has_varargs: bool)
  ~(is_synthetic: bool)
  ~(other_flags: int list)
  ~(exceptions: class_name_int list)
  ~(attributes: attributes_int)
  ~(annotations: method_annotations_int)
  () =
object (self: 'a)

  method virtual is_concrete: bool

  method is_abstract = not(self#is_concrete)

  method get_signature = signature

  method get_class_method_signature = class_method_signature

  method get_visibility = access

  method generic_signature = generic_signature

  method is_bridge = is_bridge

  method has_varargs = has_varargs

  method is_synthetic = is_synthetic

  method get_other_flags = other_flags

  method get_exceptions = exceptions

  method get_attributes = attributes

  method get_annotations = annotations

  method virtual is_static: bool

  method virtual is_final: bool

  method virtual is_synchronized: bool

  method virtual is_strict: bool

  method virtual get_annotation_default: element_value_t option

  method virtual get_implementation: implementation_t

  method virtual toPretty: pretty_t

end


class concrete_method_t
  ~(signature: method_signature_int)
  ~(class_method_signature: class_method_signature_int)
  ~(access: access_t)
  ~(is_static: bool)
  ~(is_final: bool)
  ~(is_synchronized: bool)
  ~(is_strict: bool)
  ?(generic_signature: method_type_signature_int option)
  ~(is_bridge: bool)
  ~(has_varargs: bool)
  ~(is_synthetic: bool)
  ~(other_flags: int list)
  ~(exceptions: class_name_int list)
  ~(attributes: attributes_int)
  ~(annotations: method_annotations_int)
  ~(implementation: implementation_t)
  ():method_int =
object

  inherit method_t
    ~signature:signature
    ~class_method_signature:class_method_signature
    ~access:access
    ?generic_signature:generic_signature
    ~is_bridge:is_bridge
    ~has_varargs:has_varargs
    ~is_synthetic:is_synthetic
    ~other_flags:other_flags
    ~exceptions:exceptions
    ~attributes:attributes
    ~annotations:annotations
    ()

  method is_concrete = true

  method is_static = is_static

  method is_final = is_final

  method is_synchronized = is_synchronized

  method is_strict = is_strict

  method get_implementation = implementation

  method get_annotation_default =
    raise
      (JCH_runtime_type_error
	 (STR "Concrete method has no annotation_default"))

  method toPretty =
    LBLOCK [
        access_to_pretty access;
        STR " ";
        signature#toPretty;
        NL;
	implementation_to_pretty implementation]

end

let make_concrete_method = new concrete_method_t


class abstract_method_t
  ~(signature: method_signature_int)
  ~(class_method_signature: class_method_signature_int)
  ~(access: access_t)
  ?(annotation_default: element_value_t option)
  ?(generic_signature: method_type_signature_int option)
  ~(is_bridge: bool)
  ~(has_varargs: bool)
  ~(is_synthetic: bool)
  ~(other_flags: int list)
  ~(exceptions: class_name_int list)
  ~(attributes: attributes_int)
  ~(annotations: method_annotations_int)
  ():method_int =
object

  inherit method_t
    ~signature:signature
    ~class_method_signature:class_method_signature
    ~access:access
    ?generic_signature:generic_signature
    ~is_bridge:is_bridge
    ~has_varargs:has_varargs
    ~is_synthetic:is_synthetic
    ~other_flags:other_flags
    ~exceptions:exceptions
    ~attributes:attributes
    ~annotations:annotations
    ()

  method is_concrete = false

  method is_static = false

  method is_final = false

  method is_synchronized = false

  method is_strict =
    raise
      (JCH_runtime_type_error
	 (STR "Abstract method has no concept of strict"))

  method get_annotation_default = annotation_default

  method get_implementation =
    raise
      (JCH_runtime_type_error
	 (STR "Abstract method does not have an implementation"))

  method toPretty =
    LBLOCK [
        access_to_pretty access;
        STR " ";
        signature#toPretty;
	STR " (Abstract Method)";
        NL]

end

let make_abstract_method = new abstract_method_t

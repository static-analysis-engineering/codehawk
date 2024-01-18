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
open JCHDictionary


class virtual field_t
  ~(signature: field_signature_int)
  ~(class_signature: class_field_signature_int)
  ~(generic_signature: field_type_signature_int option)
  ~(is_synthetic: bool)
  ~(value: constant_value_t option)
  ~(annotations: (annotation_t * bool (* visibility *)) list)
  ~(other_flags: int list)
  ~(attributes: attributes_int)
  () =
object (self: _)

  method virtual is_class_field: bool

  method is_interface_field: bool = not(self#is_class_field)

  method get_signature = signature

  method get_class_signature = class_signature

  method get_generic_signature = generic_signature

  method get_value = value

  method get_annotations = annotations

  method get_other_flags = other_flags

  method get_attributes = attributes

  method virtual get_visibility: access_t

  method is_synthetic = is_synthetic

  method virtual is_static: bool

  method virtual is_final: bool

  method virtual is_enum: bool

  method virtual kind: field_kind_t

  method virtual is_transient: bool

  method virtual toPretty: pretty_t

end


class class_field_t
  ~(signature: field_signature_int)
  ~(class_signature: class_field_signature_int)
  ~(generic_signature: field_type_signature_int option)
  ~(access: access_t)
  ~(is_static: bool)
  ~(is_final:bool)
  ~(is_synthetic: bool)
  ~(is_enum: bool)
  ~(kind: field_kind_t)
  ~(value: constant_value_t option)
  ~(is_transient: bool)
  ~(annotations: (annotation_t * bool (* visibility *)) list)
  ~(other_flags: int list)
  ~(attributes: attributes_int):field_int
  =
object

  inherit field_t
    ~signature:signature
    ~class_signature:class_signature
    ~generic_signature:generic_signature
    ~is_synthetic:is_synthetic
    ~value:value
    ~annotations:annotations
    ~other_flags:other_flags
    ~attributes:attributes
    ()

  method is_class_field = true

  method get_visibility = access

  method is_static = is_static

  method is_final = is_final

  method is_enum = is_enum

  method kind = kind

  method is_transient = is_transient

  method toPretty = raise (JCH_not_implemented "class_field_t")

end

let make_class_field = new class_field_t


class interface_field_t
  ~(signature: field_signature_int)
  ~(class_signature: class_field_signature_int)
  ~(generic_signature: field_type_signature_int option)
  ~(is_synthetic: bool)
  ~(is_final:bool)
  ~(value: constant_value_t option)
  ~(annotations: (annotation_t * bool (* visibility *)) list)
  ~(other_flags: int list)
  ~(attributes: attributes_int):field_int
  =
object

  inherit field_t
    ~signature:signature
    ~class_signature:class_signature
    ~generic_signature:generic_signature
    ~is_synthetic:is_synthetic
    ~value:value
    ~annotations:annotations
    ~other_flags:other_flags
    ~attributes:attributes
    ()

  method is_class_field = false

  method get_visibility = Public

  method is_static = true

  method is_final = is_final

  method is_enum =
    raise (JCH_runtime_type_error (STR "Interface field cannot be an enum"))

  method kind = Final

  method is_transient =
    raise (JCH_runtime_type_error (STR "Interface field cannot be transient"))

  method toPretty = class_signature#toPretty

end

let make_interface_field = new interface_field_t


class inner_class_t
  ?(name: class_name_int option)
  ?(outer_class_name: class_name_int option)
  ?(source_name: string option)
  ~(access: access_t)
  ~(is_static: bool)
  ~(is_final: bool)
  ~(is_synthetic: bool)
  ~(is_annotation: bool)
  ~(is_enum: bool)
  ~(other_flags: int list)
  ~(kind: inner_class_kind_t)
  ():inner_class_int
=
object

  method get_name = name

  method get_outer_class_name = outer_class_name

  method get_source_name = source_name

  method get_access = access

  method is_static = is_static

  method is_final = is_final

  method is_synthetic = is_synthetic

  method is_annotation = is_annotation

  method is_enum = is_enum

  method get_other_flags = other_flags

  method kind = kind

end

let make_inner_class = new inner_class_t


class virtual java_class_or_interface_t
  ~(name: class_name_int)
  ~(version: version_t)
  ~(access: access_t)
  ~(generic_signature: class_signature_int option)
  ~(interfaces: class_name_int list)
  ~(consts: constant_t array)
  ~(fields: field_int list)
  ?(source_file: string option)
  ~(source_origin: string)
  ~(md5_digest:string)
  ~(is_deprecated: bool)
  ?(source_debug_extension : string option)
  ~(inner_classes : inner_class_int list)
  ~(annotations: (annotation_t * bool (* visibility *)) list)
  ~(bootstrapmethods: bootstrap_method_int list)
  ~(other_flags : int list)
  ~(other_attributes : (string * string) list)
  ~(methods: method_int list)
  () =
object (self: _)

  method virtual is_class: bool

  method is_interface = not(self#is_class)

  method get_name = name

  method get_version = version

  method get_visibility = access

  method get_generic_signature = generic_signature

  method virtual get_initializer : method_int option

  method get_fields = fields

  method get_field_signatures = List.map (fun f -> f#get_signature) fields

  method get_interfaces = interfaces

  method get_consts = consts

  method get_source_file = source_file

  method get_source_origin = source_origin

  method get_md5_digest = md5_digest

  method is_deprecated = is_deprecated

  method get_source_debug_extension = source_debug_extension

  method get_inner_classes = inner_classes

  method get_annotations = annotations

  method get_bootstrap_methods = bootstrapmethods

  method get_bootstrap_method (index:int) =
    let l = self#get_bootstrap_methods in
    if index < (List.length l) then
      List.nth l index
    else
      raise
        (JCH_failure
           (LBLOCK [
                STR "Illegal bootstrap method index: ";
                INT index;
                STR "; only ";
                INT (List.length l);
                STR " bootstrap methods found in class ";
                self#get_name#toPretty]))

  method get_other_flags = other_flags

  method get_other_attributes = other_attributes

  method virtual is_final: bool

  method virtual is_abstract: bool

  method virtual get_super_class: class_name_int option

  method virtual get_enclosing_method:
                   (class_name_int * method_signature_int option) option

  method virtual is_synthetic: bool

  method virtual is_enum: bool

  method virtual is_annotation: bool

  method get_methods = methods

  method get_method_signatures = List.map (fun m -> m#get_signature) methods

  method get_method (ms: method_signature_int) =
    try
      Some (List.find (fun m -> m#get_signature#equal ms) methods)
    with
      Not_found -> None

  method get_concrete_methods = List.filter (fun m -> m#is_concrete) methods

  method get_instruction_count =
    List.fold_left (fun acc m ->
      if m#is_concrete then
	match m#get_implementation with
	| Native -> acc
	| Bytecode bc -> bc#get_code#instr_count + acc
      else
	acc) 0 methods

  method get_field (fs: field_signature_int) =
    try
      Some (List.find (fun f -> f#get_signature#equal fs) fields)
    with
      Not_found -> None

  method defines_method (ms: method_signature_int) =
    List.exists (fun m -> m#get_signature#equal ms) methods

  method defines_field (fs: field_signature_int) =
    List.exists (fun f -> f#get_signature#equal fs) fields

  method virtual toPretty: pretty_t

end


class java_class_t
  ~(name: class_name_int)
  ~(version: version_t)
  ~(access: access_t)
  ~(is_final: bool)
  ~(is_abstract: bool)
  ~(super_class: class_name_int option)
  ~(generic_signature: class_signature_int option)
  ~(fields: field_int list)
  ~(interfaces: class_name_int list)
  ~(consts: constant_t array)
  ?(source_file: string option)
  ~(source_origin:string)
  ~(md5_digest:string)
  ~(is_deprecated: bool)
  ?(enclosing_method: (class_name_int * method_signature_int option) option)
  ?(source_debug_extension : string option)
  ~(inner_classes : inner_class_int list)
  ~(is_synthetic: bool)
  ~(is_enum: bool)
  ~(annotations: (annotation_t * bool (* visibility *)) list)
  ~(bootstrapmethods:bootstrap_method_int list)
  ~(other_flags : int list)
  ~(other_attributes : (string * string) list)
  ~(methods: method_int list)
  ():java_class_or_interface_int =
object (self: 'a)

  inherit java_class_or_interface_t
    ~name:name
    ~version:version
    ~access:access
    ~generic_signature:generic_signature
    ~interfaces:interfaces
    ~consts:consts
    ~fields:fields
    ?source_file:source_file
    ~source_origin:source_origin
    ~md5_digest:md5_digest
    ~is_deprecated:is_deprecated
    ?source_debug_extension:source_debug_extension
    ~inner_classes:inner_classes
    ~other_flags:other_flags
    ~other_attributes:other_attributes
    ~annotations:annotations
    ~bootstrapmethods:bootstrapmethods
    ~methods:methods
    ()

  method is_class = true

  method is_final = is_final

  method is_abstract = is_abstract

  method get_super_class = super_class

  method get_enclosing_method = enclosing_method

  method is_synthetic = is_synthetic

  method is_enum = is_enum

  method is_annotation =
    raise (JCH_runtime_type_error (STR "Class is not an annotation"))

  method get_initializer =
    match self#get_method clinit_signature with
      | None -> None
      | Some m ->
	  if m#is_concrete then
	    Some m
	  else
	    raise (JCH_failure (STR "A class initializer cannot be abstract"))

  method toPretty: pretty_t =
    let super_class_to_pretty = match super_class with
      | Some c -> LBLOCK [STR " extends "; STR c#simple_name; STR " "]
      | _ -> STR " " in
    LBLOCK [
        access_to_pretty access; STR " class ";
        STR name#simple_name;
	super_class_to_pretty;
        NL;
	LBLOCK (List.map (fun m -> LBLOCK [ m#toPretty; NL]) methods);
        NL]

end

let make_java_class = new java_class_t


class java_interface_t
  ~(name: class_name_int)
  ~(version: version_t)
  ~(access: access_t)
  ~(interfaces: class_name_int list)
  ~(generic_signature: class_signature_int option)
  ~(consts: constant_t array)
  ?(source_file: string option)
  ~(source_origin: string)
  ~(md5_digest: string)
  ~(is_deprecated: bool)
  ?(source_debug_extension : string option)
  ~(inner_classes : inner_class_int list)
  ?(initializer_method: method_int option)
  ~(is_annotation: bool)
  ~(annotations: (annotation_t * bool (* visibility *)) list)
  ~(bootstrapmethods: bootstrap_method_int list)
  ~(other_attributes : (string * string) list)
  ~(other_flags : int list)
  ~(fields: field_int list)
  ~(methods: method_int list)
  ():java_class_or_interface_int =
object

  inherit java_class_or_interface_t
    ~name:name
    ~version:version
    ~access:access
    ~generic_signature:generic_signature
    ~interfaces:interfaces
    ~consts:consts
    ~fields:fields
    ?source_file:source_file
    ~source_origin: source_origin
		~md5_digest: md5_digest
    ~is_deprecated:is_deprecated
    ?source_debug_extension:source_debug_extension
    ~inner_classes:inner_classes
    ~other_flags:other_flags
    ~other_attributes:other_attributes
    ~annotations:annotations
    ~bootstrapmethods:bootstrapmethods
    ~methods:methods
    ()

  method is_class = false

  method is_final = false

  method is_abstract = true

  method get_super_class =
    let java_lang_object = common_dictionary#make_class_name "java.lang.Object" in
    Some java_lang_object

  method get_enclosing_method =
    raise (JCH_runtime_type_error (STR "Interface does not have an enclosing method"))

  method is_synthetic =
    raise (JCH_runtime_type_error (STR "Interface cannot be synthetic"))

  method is_enum =
    raise (JCH_runtime_type_error (STR "Interface cannot be an enum"))

  method is_annotation = is_annotation

  method get_initializer = initializer_method

  (* why is the method table altered to set the name of the initializer to the
     the clinit_signature; is it different from the method signature itself?
     why is the same not done for classes?
  *)
  method! get_methods = methods

(*    let methods' = methods#clone in
    let _ = match self#get_initializer with
      | Some m -> methods'#set clinit_signature m
      | None -> ()
    in
      methods'  *)

  method toPretty = name#toPretty

end

let make_java_interface = new java_interface_t

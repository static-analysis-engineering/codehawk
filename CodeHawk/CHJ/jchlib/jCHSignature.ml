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
open CHCollections

(* jchlib *)
open JCHBasicTypesAPI
open JCHBasicTypes


let type_argument_kind_to_string a = match a with
  | ArgumentExtends -> "argument extends "
  | ArgumentInherits -> "argument inherits "
  | ArgumentIs -> "argument is "
  | ArgumentIsAny -> "argument is any "

let throws_signature_kind_to_string a = match a with
  | ThrowsClass -> "throws class "
  | ThrowsTypeVariable -> "throws type variable "

let type_signature_kind_to_string a = match a with
  | BasicType -> "basic type "
  | ObjectType -> "object type "

let field_type_signature_kind_to_string a = match a with
  | ClassType -> "class type "
  | ArrayType -> "array type "
  | TypeVariable -> "type variable "


class type_variable_t (name: string):type_variable_int =
object

  method name = name

  method toPretty = STR name

end

let make_type_variable = new type_variable_t

class simple_class_type_signature_t
  ~(name: string)
  ~(type_arguments: type_argument_int list):simple_class_type_signature_int
  =
object

  method name = name

  method type_arguments = type_arguments

  method toPretty =
    match type_arguments with
      [] -> STR name
    | l -> LBLOCK [STR name;  pretty_print_list l (fun a -> a#toPretty) "<" "," ">"]

end

let make_simple_class_type_signature = new simple_class_type_signature_t

class class_type_signature_t
  ~(package: string list)
  ~(enclosing_classes: simple_class_type_signature_int list)
  ~(simple_class_type_signature: simple_class_type_signature_int):class_type_signature_int
  =
object

  method package = package

  method enclosing_classes = enclosing_classes

  method simple_class_type_signature = simple_class_type_signature

  method toPretty =
    LBLOCK [
        pretty_print_list package (fun s -> STR s) "" "." "";
	pretty_print_list enclosing_classes (fun c -> c#toPretty) "" "$" "";
	STR ".";
        simple_class_type_signature#toPretty]

end

let make_class_type_signature = new class_type_signature_t


class formal_type_parameter_t
  ~(name: string)
  ?(class_bound: field_type_signature_int option)
  ~(interface_bounds: field_type_signature_int list)
  ():formal_type_parameter_int =
object

  method name = name

  method class_bound = class_bound

  method interface_bounds = interface_bounds

  method toPretty =
    let cb_p =
      match class_bound with
      | Some s -> LBLOCK [s#toPretty; STR " "]
      | _ -> STR "" in
    let ib_p = pretty_print_list interface_bounds (fun i -> i#toPretty) " " "," " " in
    LBLOCK [cb_p; ib_p; STR name]

end

let make_formal_type_parameter = new formal_type_parameter_t


class type_argument_t
  ?(field_type_signature: field_type_signature_int option)
  ~(kind: type_argument_kind_t)
  ():type_argument_int =
object (self: 'a)

  method field_type_signature =
    match field_type_signature with
    | None ->
       raise
         (JCH_runtime_type_error
	    (STR "Field-type signature is missing in construction of type_argument_t"))
    | Some f -> f

  method kind = kind

  method toPretty =
    match kind with
    | ArgumentExtends -> LBLOCK [STR "? extends "; self#field_type_signature#toPretty]
    | ArgumentInherits -> LBLOCK [STR "? super "; self#field_type_signature#toPretty]
    | ArgumentIs -> self#field_type_signature#toPretty
    | ArgumentIsAny -> STR "?"

end

let make_type_argument = new type_argument_t


class throws_signature_t
  ?(class_type_signature: class_type_signature_int option)
  ?(type_variable: type_variable_int option)
  ~(kind: throws_signature_kind_t)
  ():throws_signature_int =
object (self: 'a)

  method kind = kind

  method class_type_signature =
    match class_type_signature with
      | None -> raise (JCH_runtime_type_error
			 (STR "Throws_signature has no class_type_signature"))
      | Some s -> s

  method type_variable =
    match type_variable with
      | None -> raise (JCH_runtime_type_error
			 (STR "Throws_signature has no type_variable"))
      | Some v -> v

  method toPretty =
    match kind with
      ThrowsClass -> self#class_type_signature#toPretty
    | ThrowsTypeVariable -> self#type_variable#toPretty

end

let make_throws_signature = new throws_signature_t


class type_signature_t
  ?(basic_type: java_basic_type_t option)
  ?(object_type: field_type_signature_int option)
  ~(kind: type_signature_kind_t)
  () =
object (self: 'a)

  method kind = kind

  method basic_type =
    match basic_type with
      | None -> raise (JCH_runtime_type_error
			 (STR "Type_signature has no basic_type"))
      | Some t -> t

  method object_type =
    match object_type with
      | None -> raise (JCH_runtime_type_error
			 (STR "Type_signature has no object_type"))
      | Some t -> t

  method toPretty =
    match kind with
      BasicType  -> java_basic_type_to_pretty self#basic_type
    | ObjectType -> self#object_type#toPretty

end

let make_type_signature = new type_signature_t


class field_type_signature_t
  ?(class_type: class_type_signature_int option)
  ?(array_type: type_signature_int option)
  ?(type_variable: type_variable_int option)
  ~(kind: field_type_signature_kind_t)
  () =
object (self: 'a)

  method kind = kind

  method class_type =
    match class_type with
      | None -> raise (JCH_runtime_type_error
			 (STR "Field_type_signature has no class_type"))
      | Some t -> t

  method array_type =
    match array_type with
      | None -> raise (JCH_runtime_type_error
			 (STR "Field_type_signature has no array_type"))
      | Some t -> t

  method type_variable =
    match type_variable with
      | None -> raise (JCH_runtime_type_error
			 (STR "Field_type_signature has no type_variable"))
      | Some v -> v

  method toPretty =
    match kind with
      ClassType -> self#class_type#toPretty
    | ArrayType -> self#array_type#toPretty
    | TypeVariable -> self#type_variable#toPretty

end

let make_field_type_signature = new field_type_signature_t


class class_signature_t
  ~(formal_type_parameters: formal_type_parameter_int list)
  ~(super_class: class_type_signature_int)
  ~(super_interfaces: class_type_signature_int list)
  =
object

  method formal_type_parameters = formal_type_parameters

  method super_class = super_class

  method super_interfaces = super_interfaces

  method toPretty =
    LBLOCK [
        STR "formals: ";
        pretty_print_list
          formal_type_parameters (fun s -> s#toPretty) "" "," ""; NL;
	STR "; super class: ";
        super_class#toPretty; NL;
        STR "; super interfaces: ";
	pretty_print_list super_interfaces (fun s -> s#toPretty) "" "," ""; NL]

end

let make_class_signature = new class_signature_t


class method_type_signature_t
  ~(formal_type_parameters: formal_type_parameter_int list)
  ~(type_signature: type_signature_int list)
  ?(return_type: type_signature_int option)
  ~(throws: throws_signature_int list)
  () =
object

  method formal_type_parameters = formal_type_parameters

  method type_signature = type_signature

  method return_type = return_type

  method throws = throws

  method toPretty =
    let pReturn = match return_type with
      | Some r -> LBLOCK [STR "return type: "; r#toPretty; NL]
      | _ -> STR "" in
    let pThrows = match throws with
      | [] -> STR ""
      | _ ->
         LBLOCK [
             STR "throws: ";
             pretty_print_list throws (fun t -> t#toPretty) "" "," ""; NL] in
    let pFormals = match formal_type_parameters with
      | [] -> STR ""
      | _ ->
         LBLOCK [
             STR "formals: ";
             pretty_print_list
               formal_type_parameters (fun p -> p#toPretty) "" "," "";
	     NL] in
    LBLOCK [
        pFormals;
	STR "parameters: ";
        pretty_print_list type_signature (fun s -> s#toPretty) "" "," ""; NL;
	pReturn; pThrows]

end

let make_method_type_signature = new method_type_signature_t

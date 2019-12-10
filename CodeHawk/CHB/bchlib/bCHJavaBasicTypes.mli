(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Arnaud Venet and Henny Sipma
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

class type class_name_int =
object ('a)
  method index       : int
  method name        : string
  method simple_name : string
  method equal       : 'a -> bool
  method compare     : 'a -> int
  method package     : string list
  method package_name: string
  method toPretty    : pretty_t
end


type java_basic_type_t =
  | Int
  | Short
  | Char
  | Byte
  | Bool
  | Long
  | Float
  | Double
  | Int2Bool
  | ByteBool
  | Object
  | Void

type object_type_t =
  | TClass of class_name_int
  | TArray of value_type_t
      
and value_type_t =
  | TBasic of java_basic_type_t
  | TObject of object_type_t

type access_t =
  | Default
  | Public
  | Private
  | Protected

class type field_signature_data_int =
object ('a)
  method name      : string
  method descriptor: value_type_t
  method compare   : 'a -> int
  method to_string : string
  method toPretty  : pretty_t
end

class type field_signature_int =
object ('a)
  method index     : int
  method name      : string
  method field_signature_data: field_signature_data_int
  method descriptor: value_type_t
  method equal     : 'a -> bool
  method compare   : 'a -> int
  method to_string : string
  method toPretty  : pretty_t
end

class type method_descriptor_int =
object ('a)
  method arguments : value_type_t list
  method return_value: value_type_t option
  method compare   : 'a -> int
  method to_string : string
  method toPretty  : pretty_t
end

class type method_signature_data_int =
object ('a)
  method name       : string
  method descriptor : method_descriptor_int
  method compare    : 'a -> int
  method to_string  : string
  method toPretty   : pretty_t
end

class type method_signature_int =
object ('a)
  method index      : int
  method method_signature_data: method_signature_data_int
  method name       : string
  method descriptor : method_descriptor_int
  method equal      : 'a -> bool
  method compare    : 'a -> int
  method to_string  : string
  method toPretty   : pretty_t
end

type java_native_method_api_t =
  { jnm_signature : method_signature_int ;
    jnm_access    : access_t ;
    jnm_static    : bool
  }
      

class type java_dictionary_int =
object
  method make_class_name      : string -> class_name_int
  method make_field_signature : string -> value_type_t -> field_signature_int
  method make_method_signature: string -> method_descriptor_int -> method_signature_int
end

type java_native_method_class_t = 
{ jnmc_class : class_name_int ;
  jnmc_native_methods: java_native_method_api_t list
}


class type java_method_name_int =
object
  (* setters *)
  method set_class_name:string -> unit
  method set_method_name:string -> unit
  method add_argument_type: value_type_t -> unit

  (* accessors *)
  method get_class_name : string
  method get_method_name: string
  method get_arguments  : value_type_t list

  (* predicates *)
  method has_arguments : bool

  (* printing *)
  method toPretty: pretty_t
end

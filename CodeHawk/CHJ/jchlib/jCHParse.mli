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

(* jchlib *)
open JCHBasicTypesAPI
open JCHRawClass

type tmp_constant =
  | ConstantClass of int                            (*  7 *)
  | ConstantField of int * int                      (*  9 *)
  | ConstantMethod of int * int                     (* 10 *)
  | ConstantInterfaceMethod of int * int            (* 11 *)
  | ConstantString of int                           (*  8 *)
  | ConstantInt of int32                            (*  3 *)
  | ConstantFloat of float                          (*  4 *)
  | ConstantLong of int64                           (*  5 *)
  | ConstantDouble of float                         (*  6 *)
  | ConstantNameAndType of int * int                (* 12 *)
  | ConstantStringUTF8 of string                    (*  1 *)
  | ConstantMethodHandle of reference_kind_t * int  (* 15 *)
  | ConstantMethodType of int                       (* 16 *)
  | ConstantInvokeDynamic of int  * int             (* 18 *)
  | ConstantUnusable                      (* second part of 64-bit entry *)


type attribute_name_t =
  (* Code *)
  | LineNumberTable
  | LocalVariableTable
  | LocalVariableTypeTable
  | StackMap
  (* ClassFile, field_info, method_info *)
  | Synthetic
  | Deprecated
  | Signature
  (* ClassFile, field_info, method_info, Code *)
  | RuntimeVisibleAnnotations
  | RuntimeInvisibleAnnotations
  (* method_info *)
  | RuntimeVisibleParameterAnnotations
  | RuntimeInvisibleParameterAnnotations
  | Code
  | Exceptions
  | AnnotationDefault
  | MethodParameters
  (* field_info *)
  | ConstantValue
  (* ClassFile *)
  | SourceFile
  | InnerClasses
  | EnclosingMethod
  | SourceDebugExtension
  | BootstrapMethods

val parse_class_low_level : IO.input -> string -> string -> raw_class_t

val parse_class : IO.input -> string -> string -> java_class_or_interface_int

val get_unknown_attributes: unit -> (string * int) list

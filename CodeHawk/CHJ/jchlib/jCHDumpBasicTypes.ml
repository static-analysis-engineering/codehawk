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


let sprintf = Printf.sprintf

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


let basic_type = function
  | Bool -> "bool"
  | Char -> "char"
  | Float -> "float"
  | Double -> "double"
  | Byte -> "byte"
  | Short -> "short"
  | Int -> "int"
  | Long -> "long"
  | _ -> raise (JCH_failure (STR "Inconsistency in JCHDumpBasicTypes"))

let rec object_value_signature = function
  | TClass cl -> cl#name
  | TArray s -> value_signature s ^"[]"

and value_signature = function
  | TBasic b -> basic_type b
  | TObject o -> object_value_signature o


let type2shortstring t =
  let bt2ss = function
    | Long -> "J"
    | Float -> "F"
    | Double -> "D"
    | Int -> "I"
    | Short -> "S"
    | Char -> "C"
    | Byte -> "B"
    | Bool -> "Z"
    | _ -> raise (JCH_failure (STR "Inconsistency in JCHDumpBasicTypes"))
  in
  let rec ot2ss = function
    | TClass cn -> "L" ^ cn#name ^ ";"
    | TArray t -> "[" ^ vt2ss t
  and vt2ss = function
    | TBasic t -> bt2ss t
    | TObject t -> ot2ss t
  in vt2ss t

let _rettype2shortstring = function
  | None -> "V"
  | Some t -> type2shortstring t

let _arraytype2shortstring = function
  | Long -> "J"
  | Float -> "F"
  | Double -> "D"
  | Int -> "I"
  | Short -> "S"
  | Char -> "C"
  | ByteBool -> "B"
  | Object -> "A"
  | _ -> raise (JCH_failure (STR "Inconsistency in JCHDumpBasicTypes"))

let method_signature name m =
  (match m#return_value with
   | None -> "void"
   | Some s -> value_signature s) ^ " " ^name^ "("
  ^ String.concat "," (List.map value_signature m#arguments) ^ ")"

let signature name = function
  | SValue v -> value_signature v ^ " " ^name
  | SMethod m -> method_signature name m

let jvm_basic_type = function
  | Int
    | Int2Bool -> 'i'
  | Long -> 'l'
  | Float -> 'f'
  | Double -> 'd'
  | _ -> raise (JCH_failure (STR "Inconsistency in JCHDumpBasicTypes"))

let java_basic_type = function
  | Int -> 'i'
  | Long -> 'l'
  | Float -> 'f'
  | Double -> 'd'
  | Short -> 's'
  | Char -> 'c'
  | Byte
  | Bool -> 'b'
  | _ -> raise (JCH_failure (STR "Inconsistency in JCHDumpBasicTypes"))

let dump_constant_value ch = function
  | ConstString s -> IO.printf ch "string '%s'" s
  | ConstInt i -> IO.printf ch "int %ld" i
  | ConstFloat f -> IO.printf ch "float %f" f
  | ConstLong i -> IO.printf ch "long %Ld" i
  | ConstDouble f -> IO.printf ch "double %f" f
  | ConstClass cl -> IO.printf ch "class %s" (object_value_signature cl)

let dump_constant ch = function
  | ConstValue v -> dump_constant_value ch v
  | ConstField (cn,fs) ->
     let fn = fs#name
     and ft = fs#descriptor in
     IO.printf ch "field : %s %s::%s" (value_signature ft) (cn#name) fn
  | ConstMethod (cl,ms) ->
     let mn = ms#name
     and md = ms#descriptor in
     IO.printf
       ch
       "method : %s"
       (method_signature (object_value_signature cl ^ "::" ^ mn) md)
  | ConstInterfaceMethod (cn, ms) ->
     let mn = ms#name
     and md = ms#descriptor in
     IO.printf
       ch
       "interface-method : %s"
       (method_signature (cn#name ^ "::" ^ mn) md)
  | ConstDynamicMethod (_i, ms) ->
     let mn = ms#name
     and md = ms#descriptor in
     IO.printf ch "dynamic-method : %s" (method_signature mn md)
  | ConstNameAndType (s,sign) ->
     IO.printf ch "name-and-type : %s" (signature s sign)
  | ConstStringUTF8 s -> IO.printf ch "utf8 %s" s
  | ConstMethodHandle (k,FieldHandle(cn,fs)) ->
     let fn = fs#name
     and ft = fs#descriptor in
     IO.printf
       ch
       "field-method-handle(%s): %s %s::%s"
       (reference_kind_to_string k)
       (value_signature ft)
       cn#name fn
  | ConstMethodHandle (k,MethodHandle(ot,ms)) ->
     let mn = ms#name
     and md = ms#descriptor in
     IO.printf
       ch
       "method-method-handle(%s): %s"
       (reference_kind_to_string k)
       (method_signature (object_value_signature ot ^ "::" ^ mn) md)
  | ConstMethodHandle (k,InterfaceHandle(cn,ms)) ->
     let mn = ms#name
     and md = ms#descriptor in
     IO.printf
       ch "interface-method-handle(%s): %s"
       (reference_kind_to_string k)
       (method_signature (cn#name ^ "::" ^ mn) md)
  | ConstMethodType md -> IO.printf ch "method-type: %s" md#to_string
  | ConstUnusable -> IO.printf ch "unusable"


let _dump_constantpool ch =
  Array.iteri
    (fun i c ->
      IO.printf ch "    %d  " i;
      dump_constant ch c;
      IO.write ch '\n')


let dump_verification_type = function
  | VTop -> "Top"
  | VInteger -> "Integer"
  | VFloat -> "Float"
  | VDouble -> "Double"
  | VLong -> "Long"
  | VNull -> "Null"
  | VUninitializedThis -> "UninitializedThis"
  | VObject c -> sprintf "Object %s" (object_value_signature c)
  | VUninitialized off -> sprintf "Uninitialized %d" off

let dump_stackmap ch (offset, locals, stack) =
  begin
    IO.printf ch "\n      offset=%d,\n      locals=[" offset;
    List.iter
      (fun t -> IO.printf ch "\n        %s" (dump_verification_type t)) locals;
    IO.printf ch "],\n      stack=[";
    List.iter
      (fun t -> IO.printf ch "\n        %s" (dump_verification_type t)) stack;
    IO.printf ch "]"
  end


let dump_exc ch _cl exc =
  IO.printf ch "\n      [%d-%d] -> %d (" exc#h_start exc#h_end exc#handler;
  (match exc#catch_type with
     | None -> IO.printf ch "<finally>"
     | Some cl -> IO.printf ch "class %s" (cl#name));
  IO.printf ch ")"

(* =============================================================================
   CodeHawk Java Analyzer 
   Author: Arnaud Venet
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

open IO
open IO.BigEndian
open ExtList
open ExtString

(* chlib *)
open CHPretty

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(** Output functions *)

let write_ui8 ch n =
  if n < 0 || n > 0xFF then raise (Overflow "write_ui8");
  write_byte ch n

let write_i8 ch n =
  if n < -0x80 || n > 0x7F then raise (Overflow "write_i8");
  if n < 0 then
    write_ui8 ch (0x100 + n)
  else
    write_ui8 ch n

let write_string_with_length length ch s =
  length ch (String.length s);
  nwrite ch (Bytes.of_string s)

let write_with_length length ch write =
  let ch' = output_string () in
    write ch';
    write_string_with_length length ch (close_out ch')

let write_with_size (size:'a IO.output -> int -> unit) ch write l =
  size ch (List.length l);
  List.iter write l

(** Constant pool manipulation *)

let get_constant c n =
  if n < 0 || n >= Array.length c then 
    raise (JCH_class_structure_error
             (LBLOCK [ STR "Illegal constant index:" ; INT n]));
  match c.(n) with
  | ConstUnusable ->
     raise (JCH_class_structure_error
              (LBLOCK [ STR "Illegal constant: unusable"]))
  | x -> x

let get_constant_value c n =
  match get_constant c n with
  | ConstValue v -> v
  | k -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal constant value index: " ;
                            constant_to_pretty k]))

let get_object_type consts i =
  match get_constant consts i with
  | ConstValue (ConstClass n) -> n
  | k -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal class index: " ;
                            constant_to_pretty k]))

let get_class consts i =
  match get_object_type consts i with
  | TClass c -> c
  | _ -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal class index: refers to an array type descriptor"]))

let get_field consts i =
  match get_constant consts i with
  | ConstField cnfs -> cnfs
  | k -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal field index: " ; constant_to_pretty k]))

let get_method_handle consts i =
  match get_constant consts i with
  | ConstMethodHandle (kind,handle) -> (kind,handle)
  | k -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal method handle index: " ;
                            constant_to_pretty k ]))

let get_bootstrap_argument consts i =
  match get_constant consts i with
  | ConstValue v -> BootstrapArgConstantValue v
  | ConstMethodHandle (kind,handle) -> BootstrapArgMethodHandle (kind,handle)
  | ConstMethodType d -> BootstrapArgMethodType d
  | k -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal bootstrap argument index: " ;
                            constant_to_pretty k ]))

let get_method consts i =
  match get_constant consts i with
  | ConstMethod (ot, ms) -> ot,ms
  | ConstInterfaceMethod (cn,ms) -> (TClass cn),ms
  | k -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal method index: " ;
                            constant_to_pretty k ]))

let get_callsite_specifier consts i =
  match get_constant consts i with
  | ConstDynamicMethod (index,ms) -> (index,ms)
  | k  -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal callsite specifier: " ;
                            constant_to_pretty k ]))

let get_interface_method consts i =
  match get_constant consts i with
  | ConstInterfaceMethod cms -> cms
  | k -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal interface method index: " ;
                            constant_to_pretty k ]))

let get_string consts i =
  match get_constant consts i with
  | ConstStringUTF8 s -> s
  | k -> raise (JCH_class_structure_error
                  (LBLOCK [ STR "Illegal string index: " ;
                            constant_to_pretty k ]))

let get_class_ui16 consts ch = get_class consts (read_ui16 ch)
let get_string_ui16 consts ch = get_string consts (read_ui16 ch)

let constant_to_int cp c =
  if c = ConstUnusable
  then raise (JCH_class_structure_error (STR "Illegal constant: unusable"));
  try
    DynArray.index_of (fun c' -> 0 = compare c c') cp (* [nan <> nan], where as [0 = compare nan nan] *)
  with
    Not_found ->
      if DynArray.length cp = 0
      then DynArray.add cp ConstUnusable;
      if not (DynArray.unsafe_get cp 0 = ConstUnusable)
      then raise (JCH_class_structure_error (STR "unparsing with an incorrect constant pool"));
      let i = DynArray.length cp in
      DynArray.add cp c;
      (match c with
      | ConstValue (ConstLong _ | ConstDouble _) ->
	DynArray.add cp ConstUnusable
      | _ -> ());
      i

let value_to_int cp v = constant_to_int cp (ConstValue v)
let object_type_to_int cp ot = value_to_int cp (ConstClass ot)
let field_to_int cp v = constant_to_int cp (ConstField v)
let method_to_int cp v = constant_to_int cp (ConstMethod v)
let class_to_int cp v = object_type_to_int cp (TClass v)
let string_to_int cp v = constant_to_int cp (ConstStringUTF8 v)
let name_and_type_to_int cp (n, s) = constant_to_int cp (ConstNameAndType (n, s))

let write_constant ch cp c = write_ui16 ch (constant_to_int cp c)
let write_value ch cp c = write_ui16 ch (value_to_int cp c)
let write_object_type ch cp c = write_ui16 ch (object_type_to_int cp c)
let write_class ch cp c = write_ui16 ch (class_to_int cp c)
let write_string ch cp c = write_ui16 ch (string_to_int cp c)
let write_name_and_type ch cp c = write_ui16 ch (name_and_type_to_int cp c)



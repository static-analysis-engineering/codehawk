(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2023 Aarno Labs LLC

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
open CHLanguage

(* bchlib *)
open BCHBCTypes


(** {1 Common types}*)

(** {2 Base types} *)

val t_unknown: btype_t
val t_void: btype_t
val t_vararg: btype_t

val t_char: btype_t
val t_uchar: btype_t
val t_wchar: btype_t

val t_short: btype_t
val t_int: btype_t
val t_uint: btype_t
val t_long: btype_t

val t_float: btype_t
val t_double: btype_t

(** {2 Pointer types}*)

val t_voidptr: btype_t

val t_refto: btype_t -> btype_t
val t_ptrto: btype_t -> btype_t


(** {2 Type definition}*)

val t_named: string -> btype_t

(** {2 Composite types}*)

val t_comp: ?name_space:string list -> string -> btype_t
val t_enum: ?name_space:string list -> string -> btype_t
val t_class: ?name_space:string list -> string -> btype_t

val t_tcomp: ?name_space:tname_t list -> tname_t -> btype_t
val t_tenum: ?name_space:tname_t list -> tname_t -> btype_t

val t_tclass: ?name_space:tname_t list -> tname_t -> btype_t

val t_function: btype_t -> bfunarg_t list -> btype_t
val t_vararg_function: btype_t -> bfunarg_t list -> btype_t
val t_function_anon: btype_t -> btype_t        (* arguments not known *)


(** {1 Type predicates}*)

val is_void: btype_t -> bool
val is_pointer: btype_t -> bool
val is_unsigned: btype_t -> bool  (* true if unsigned, false if signed or unknown *)
val is_function_type: btype_t -> bool
val is_unknown_type: btype_t -> bool
val is_known_type: btype_t -> bool
val is_pointer_to_struct: btype_t -> bool


(** {1 Type properties}*)

(** {2 Alignment}*)

val align_of_int_ikind: ikind_t -> int

val align_of_float_fkind: fkind_t -> int

val align_of_btype: btype_t -> int

(** {2 Size}*)

val size_of_int_ikind: ikind_t -> int

val size_of_float_fkind: fkind_t -> int

val size_of_btype: btype_t -> int

(** {2 Scalar kind}*)

(** [size_to_int_ikind ~signed size] returns the integer kind with [size]
    bytes and given signedness. The default value for [signed] is [true].*)
val size_to_int_ikind: ?signed:bool -> int -> ikind_t


(** {1 Comparisons} *)

val btype_compare: btype_t -> btype_t -> int

val bexp_compare: bexp_t -> bexp_t -> int


(** {1 Compinfos} *)

(** {2 Field layout}*)

val layout_fields: bcompinfo_t -> bcompinfo_t

(** {2 Struct field characterization}*)

(** [struct_field_categories ty] returns a list of strings indicating the
    kind of fields in struct [ty].

    The kind of field is expressed by one of the following indicators:
    - "string": the field is constant string
    - "address": the field is a code address
    - "unknown": unknown

    If [ty] is not a struct it returns the regular string representation of
    [ty].*)
val struct_field_categories: btype_t -> string list


(** [struct_offset_field_categories ty] returns a list of pairs indicating the
    offset and kind of fields in struct [ty].

    If [ty] is not a struct it returns the regular string representation of
    [ty] with offset 0.*)
val struct_offset_field_categories: btype_t -> (int * string) list

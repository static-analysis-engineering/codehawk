(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny B. Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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
open CHLanguage

(* bchlib *)
open BCHBCTypes


(** Utility functions to construct, destruct, or examine c-like types.*)


(** {1 Common types}*)

(** {2 Base types} *)

val t_unknown: btype_t
val t_void: btype_t
val t_vararg: btype_t

val t_bool: btype_t
val t_char: btype_t
val t_uchar: btype_t
val t_wchar: btype_t

val t_short: btype_t
val t_ushort: btype_t
val t_int: btype_t
val t_uint: btype_t
val t_long: btype_t
val t_ulong: btype_t

val t_float: btype_t
val t_double: btype_t
val t_longdouble: btype_t

(** {2 Unknown base types} *)

(** The "int" and "int-size" attributes are used to refer to integer types
    for which it is not known whether they are signed or not and, in case
    of "int" what their size is.*)

val t_unknown_int: btype_t
val t_unknown_int_size: int -> btype_t
val t_unknown_float: btype_t

(** {2 Pointer types}*)

val t_voidptr: btype_t

val t_refto: btype_t -> btype_t
val t_ptrto: btype_t -> btype_t
val t_charptr: btype_t

val ptr_deref: btype_t -> btype_t


(** {2 Array types)*)

val t_array: btype_t -> int -> btype_t


(** {2 Type definition}*)

val t_named: string -> btype_t

(** {2 Composite types}*)

val t_comp: ?name_space:string list -> string -> btype_t
val t_enum: ?name_space:string list -> string -> btype_t
val t_class: ?name_space:string list -> string -> btype_t

val t_tcomp: ?name_space:tname_t list -> tname_t -> btype_t
val t_tenum: ?name_space:tname_t list -> tname_t -> btype_t

val t_tclass: ?name_space:tname_t list -> tname_t -> btype_t


(** [t_function returntype args] returns a function type with returntype
    [returntype] and named arguments [args].*)
val t_function: ?is_varargs:bool -> btype_t -> bfunarg_t list -> btype_t


(** [t_signature returntype args] returns a function type with returntype
    [returntype] and arguments [args] represented as a list of
    (argument-name, argument-type) pairs.*)
val t_fsignature:
  ?is_varargs:bool -> btype_t -> (string * btype_t) list -> btype_t


val t_vararg_function: btype_t -> bfunarg_t list -> btype_t


(** [t_function_anon ty] returns an anonymous function type with returntype
    [ty] without arguments (distinct from zero arguments).*)
val t_function_anon: btype_t -> btype_t        (* arguments not known *)


(** {1 Type predicates}*)

val is_void: btype_t -> bool
val is_int: btype_t -> bool
val is_enum: btype_t -> bool
val is_float: btype_t -> bool
val is_float_float: btype_t -> bool
val is_float_double: btype_t -> bool
val is_scalar: btype_t -> bool
val is_pointer: btype_t -> bool
val is_unsigned: btype_t -> bool  (* true if unsigned, false if signed or unknown *)
val is_function_type: btype_t -> bool
val is_unknown_type: btype_t -> bool
val is_known_type: btype_t -> bool
val is_struct_type: btype_t -> bool
val is_array_type: btype_t -> bool
val is_pointer_to_struct: btype_t -> bool

val is_volatile: btype_t -> bool

(** Returns true if [ty] is a function type with attribute [stdcall].*)
val is_stdcall: btype_t -> bool

(** {1 Type resolution}*)

val resolve_type: btype_t -> btype_t

(** {1 Type properties}*)

(** {2 Alignment}*)

val align_of_int_ikind: ikind_t -> int

val align_of_float_fkind: fkind_t -> int

val align_of_btype: btype_t -> int


(** {2 Size}*)

val size_of_int_ikind: ikind_t -> int

val size_of_float_fkind: fkind_t -> int

val size_of_btype: btype_t -> int

val size_of_btype_comp: bcompinfo_t -> int

(** {2 Scalar kind}*)

(** [size_to_int_ikind ~signed size] returns the integer kind with [size]
    bytes and given signedness. The default value for [signed] is [true].*)
val size_to_int_ikind: ?signed:bool -> int -> ikind_t

(** {2 Attributes}*)

(** Returns the attributes associated with the type.*)
val get_attributes: btype_t -> b_attributes_t


(** {1 Comparisons} *)

val btype_compare: btype_t -> btype_t -> int

val btype_equal: btype_t -> btype_t -> bool

val bexp_compare: bexp_t -> bexp_t -> int


(** {1 Abstraction} *)

val btype_abstract: btype_t -> symbol_t

val btype_concretize: symbol_t -> btype_t


(** Returns the smallest type that is larger than or equal to the types in
    the list.*)
val btype_join: btype_t list -> btype_t


(** Returns the largest type that is smaller than or equal to the types in
    the list. If no such type exists (that is, some of the types are
    incomparable) return [None] (that is, bottom).*)
val btype_meet: btype_t list -> btype_t option


(** {1 Promotions} *)

val promote_float: btype_t -> btype_t

val promote_int: btype_t -> btype_t

(** {1 Arrays} *)

val get_element_type: btype_t -> btype_t

(** {1 Compinfos} *)

val get_struct_type_compinfo: btype_t -> bcompinfo_t

val get_struct_type_fields: btype_t -> bfieldinfo_t list

val get_struct_field_at_offset: bcompinfo_t -> int -> (bfieldinfo_t * int) option

val get_compinfo_struct_type: bcompinfo_t -> btype_t

val get_compinfo_field: bcompinfo_t -> string -> bfieldinfo_t

val get_compinfo_scalar_type_at_offset: bcompinfo_t -> int -> btype_t option

val get_compinfo_by_key: int -> bcompinfo_t


(** {2 Fieldinfos}*)

val get_struct_field_name: bfieldinfo_t -> string

val get_struct_field_type: bfieldinfo_t -> btype_t

val get_struct_field_layout: bfieldinfo_t -> fieldlayout_t option

val get_struct_field_offset: bfieldinfo_t -> int option

val get_struct_field_size: bfieldinfo_t -> int option


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

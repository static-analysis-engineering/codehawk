(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2021 Henny Sipma
   Copyright (c) 2022-2025 Aarno Labs LLC

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
open CHNumerical
open CHPretty

(* chutil *)
open CHTraceResult

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


(** {1 Printing} *)

val memory_base_to_pretty: memory_base_t -> pretty_t

val memory_offset_to_pretty: memory_offset_t -> pretty_t

val memory_offset_to_string: memory_offset_t -> string

val stack_offset_to_name: memory_offset_t -> string

val realigned_stack_offset_to_name:memory_offset_t -> string

val global_offset_to_name: int -> memory_offset_t -> string


(** {1 Comparison} *)

val memory_offset_compare: memory_offset_t -> memory_offset_t -> int


(** {1 Offset constructors} *)

val mk_maximal_memory_offset: numerical_t -> btype_t -> memory_offset_t

val add_offset: memory_offset_t -> memory_offset_t -> memory_offset_t


(** [address_memory_offset tgtsize tgttype ty offset] returns the symbolic offset
    that corresponds with the numerical offset [offset] for a base variable with
    type [ty]. The optional arguments [tgtsize] and [tgttype] can be used to
    disambiguate between for example an entire struct or only its first field.

    An error is returned if the the symbolic offset cannot be constructed.
 *)
val address_memory_offset:
  ?tgtsize: int option
  -> ?tgtbtype: btype_t
  -> btype_t
  -> xpr_t
  -> memory_offset_t traceresult


(** {1 Offset predicates} *)

(** Returns [true] if [memoff] consists entirely of constant (numerical) values. *)
val is_constant_offset: memory_offset_t -> bool


(** Returns [true] if [memoff] itself or one of its suboffsets is a field
    offset. *)
val is_field_offset: memory_offset_t -> bool


(** Returns [true] if [memoff] itself or one of its suboffsets is an index
    offset. *)
val is_index_offset: memory_offset_t -> bool


val is_base_ptr_array_index_offset: memory_offset_t -> bool


(** Returns [true] if [memoff] itself or one of its suboffsets is an unknown
    offset. *)
val is_unknown_offset: memory_offset_t -> bool


(** {1 Offset deconstructors} *)

(** Returns a list of numerical offset and suboffsets.

    Returns an Error if [memoff] is not a constant_offset. *)
val get_constant_offsets: memory_offset_t -> numerical_t list traceresult


(** Returns the sum of all numerical offsets in [memoff].

    Returns an Error if not all offsets are constant. *)
val get_total_constant_offset: memory_offset_t -> numerical_t traceresult


(** Returns the list of index variables in [memoff] (including suboffsets.
    Returns the empty list if [memoff] is not an index offset.*)
val get_index_offset_variables: memory_offset_t -> variable_t list


val boffset_to_memory_offset:
  BCHBCTypes.boffset_t -> memory_offset_t CHTraceResult.traceresult


(** {1 Memory reference manager} *)

val make_memory_reference_manager:
  vardictionary_int -> memory_reference_manager_int

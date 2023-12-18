(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2023  Aarno Labs LLC

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

(* chutil *)
open CHXmlDocument

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHBCTypes
open BCHLibTypes


(** {1 Comparison}*)

(** compares two xxpredicates with respect to predicate and arguments.

    Two xxpredicates are considered equal if they have the same predicate
    and their principal arguments are the same (that is, the xxpredicate
    serves the same role).
 *)
val xxpredicate_compare: xxpredicate_t -> xxpredicate_t -> int


(** {1 Modification}*)

(** [modify_types_xxp tr xxp] returns an xxpredicate in which the types have
    been transformed according to [tr].

    This is mostly used in the processing of windows library function where
    the summary is generic that can be specialized to either the ASCII version
    or the wide-character version.*)
val modify_types_xxp: type_transformer_t -> xxpredicate_t -> xxpredicate_t


(** {1 Conversion}*)

val relational_op_to_xop: relational_op_t -> xop_t

val xop_to_relational_op: xop_t -> relational_op_t


(** {1 Accessors}*)

val is_relational_xop: xop_t -> bool

val is_relational_operator: string -> bool

val get_relational_operator: string -> relational_op_t

(** returns the list of terms that appear in the xxpredicate *)
val xxpredicate_terms: xxpredicate_t -> bterm_t list


(** {1 Printing}*)

val relational_op_to_string: relational_op_t -> string

val relational_op_to_xml_string: relational_op_t -> string

val xxpredicate_to_pretty: xxpredicate_t -> pretty_t

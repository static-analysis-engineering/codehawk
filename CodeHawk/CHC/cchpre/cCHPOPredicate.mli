(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024-2026 Aarno Labs LLC

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
open CHTraceResult

(* cchlib *)
open CCHBasicTypes
open CCHLibTypes

(* cchpre *)
open CCHPreTypes


val po_predicate_tag: po_predicate_t -> string

val po_predicate_to_pretty: ?full:bool -> po_predicate_t -> pretty_t

val collect_indexed_predicate_expressions: po_predicate_t -> (int * exp) list

(** Argument indices (a, b) of the components of a length min(a, b) in
    ptr-upper-bound and ptr-upper-bound-deref (fixed indices 1, 3, 4); the
    components are collected as separate predicate expressions, so that they
    get their own check variables and invariants. *)
val ptr_upper_bound_min_indices: int * int

(** Argument indices (a, b) of the components of a length min(a, b) in
    initialized-range (fixed indices 1, 2). *)
val initialized_range_min_indices: int * int

(** [is_ntp_successor e b] is true if [b] is ntp(e) + 1 (modulo casts), the
    number of bytes of [e] up to and including its null terminator. *)
val is_ntp_successor: exp -> exp -> bool

val has_global_vars_in_exp: cfundeclarations_int -> exp -> bool

val is_opaque: po_predicate_t -> bool


(** [violation_status p] is the status recorded for a proof obligation with
    predicate [p] whose condition fails on every execution that reaches it
    (or for which a witness exists): [Purple] if the failure results in
    implementation-defined behavior (conversion to a signed type of a value
    that is not representable, C11 6.3.1.3p3), [Blue] if it results in
    well-defined value wrap-around (unsigned arithmetic, C11 6.2.5p9;
    conversion to an unsigned type, 6.3.1.3p2), and [Red] (undefined
    behavior) otherwise. The analysis level only determines which of these
    are reported (issue 15). *)
val violation_status: po_predicate_t -> po_status_t

val check_assumption_predicates:
  po_predicate_t list -> po_predicate_t -> po_predicate_t option

val offset_to_s_offset: offset -> s_offset_t traceresult

val exp_to_sterm: cfundeclarations_int -> exp -> s_term_t traceresult

val po_predicate_to_xpredicate:
  cfundeclarations_int -> po_predicate_t -> xpredicate_t traceresult

val s_offset_to_offset: typ -> s_offset_t -> offset traceresult

val sterm_to_exp:
  ?returnexp:exp option -> cfundeclarations_int -> s_term_t -> exp traceresult

val xpredicate_to_po_predicate:
  ?returnexp:exp option
  -> cfundeclarations_int
  -> xpredicate_t
  -> po_predicate_t traceresult

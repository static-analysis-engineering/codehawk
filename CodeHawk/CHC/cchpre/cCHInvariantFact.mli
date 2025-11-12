(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

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
open CHPretty

(* xprlib *)
open XprTypes

(* chutil *)
open CHXmlDocument

(* cchpre *)
open CCHPreTypes


val pepr_domain: string
val intervals_domain: string
val valueset_domain: string
val linear_equalities_domain: string
val symbolic_sets_domain: string
val sym_pointersets_domain: string
val sym_initialized_domain: string

val non_relational_value_compare  :
  non_relational_value_t -> non_relational_value_t -> int

val non_relational_value_to_pretty:
  non_relational_value_t -> pretty_t

val domain_of_invariant: non_relational_value_t -> string

val xll_to_pretty: xpr_t list list -> pretty_t

val get_regions:  symbol_t list -> symbol_t list  (* filter out pres symbols *)

val invariant_fact_compare: invariant_fact_t -> invariant_fact_t -> int

val non_relational_fact_to_pretty: invariant_fact_t -> pretty_t

val invariant_fact_to_pretty: invariant_fact_t -> pretty_t

val mk_invariant_io:
  xml_element_int option -> vardictionary_int -> invariant_io_int

val get_invariant_messages:
  invariant_io_int -> (int * int list) list -> pretty_t list


(** [prioritize_invariants f invs] returns the invariants in [invs]
    sorted such that the invariants for which [(f inv)] is true are
    listed before other invariants.

    This is useful in the application of invariants in the checkers,
    where multiple invariants apply to discharge a proof obligation,
    but some invariants may be preferred over others.
 *)
val prioritize_invariants:
  (invariant_int -> bool) -> invariant_int list -> invariant_int list

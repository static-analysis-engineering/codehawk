(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
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

(** Utilities to store invariants *)

(* chlib *)
open CHAtlas
open CHLanguage
open CHNonRelationalDomainValues
open CHNumericalConstraints
open CHPretty

class type invariant_store_int =
  object

    (** [add_invariant addr inv] stores invariant [inv] with address [addr] *)
    method add_invariant : symbol_t -> atlas_t -> unit

    (** returns all symbol addresses for which invariants are present *)
    method getAddresses : CHUtils.SymbolCollections.ObjectSet.elt list

    method getFilteredPolyhedralConstraints :
      ?include_variable:(variable_t -> bool) ->
      ?exclude_variable:(variable_t -> bool) ->
      symbol_t ->
      numerical_constraint_t list

    (** returns all invariants with their identifying symbol addresses *)
    method getInvariants :
             (CHUtils.SymbolCollections.ObjectMap.key * atlas_t) list

    method getNonrelationalValue :
      symbol_t ->
      string ->
      variable_t ->
      non_relational_domain_value_t

    method getVariables : symbol_t -> string -> variable_t list

    (** [get_invariant addr] returns the invariant for address [addr] *)
    method get_invariant : symbol_t -> atlas_t

    method has_invariant : symbol_t -> bool

    method intervalToPretty : atlas_t -> pretty_t

    method intervalsToPretty : pretty_t

    method linearEqualitiesToPretty : pretty_t

    method linearEqualityToPretty : atlas_t -> pretty_t

    (** remove all invariants *)
    method reset : unit

    method stridedIntervalToPretty : atlas_t -> pretty_t

    method stridedIntervalsToPretty : pretty_t

    method toPretty : pretty_t

    method valueSetToPretty : atlas_t -> pretty_t

    method valueSetsToPretty : pretty_t
  end


val mk_invariant_store: unit -> invariant_store_int

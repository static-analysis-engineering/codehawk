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

(** Utilities to access invariants in standard domains *)

(* chlib *)
open CHAtlas
open CHIntervals
open CHLanguage
open CHNonRelationalDomainValues
open CHNumerical
open CHNumericalConstraints
open CHValueSets

class type inv_accessor_int =
object

  method hasIntervals: bool
  method hasLinearEqualities: bool
  method hasPolyhedra: bool
  method hasValueSets: bool
  method hasDomain: string -> bool

  method getObservedVariables: variable_t list

  method isScalar: variable_t -> bool

  (** retrieve the different types of numerical invariants, possibly for a
      restricted set of variables, and return them in the form of numerical
      constraints *)
  method getPolyhedralConstraints:
           ?var_filter:(variable_t -> bool)
           -> unit
           -> numerical_constraint_t list

  method getLinearEqualityConstraints:
           ?var_filter:(variable_t -> bool)
           -> unit
           -> numerical_constraint_t list

  method getIntervalConstraints:
           ?var_filter:(variable_t -> bool)
           -> unit
           -> numerical_constraint_t list

  (** retrieve the different types of numerical invariants, possibly for a
      restricted set of variables, but only return the constraints that include
      variables of interest, as specified by the include_variable function.*)
  method getFilteredPolyhedralConstraints:
           ?include_variable:(variable_t -> bool)
           -> ?exclude_variable:(variable_t -> bool)
           -> unit
           -> numerical_constraint_t list

  method getFilteredEqualityConstraints:
           ?include_variable:(variable_t -> bool)
           ->  ?exclude_variable:(variable_t -> bool)
           -> unit
           -> numerical_constraint_t list

  method getFilteredIntervalConstraints:
           ?include_variable:(variable_t -> bool)
           -> ?exclude_variable:(variable_t -> bool)
           -> unit
           -> numerical_constraint_t list

  method getEqualVariables:
           ?var_filter:(variable_t -> bool) -> variable_t -> variable_t list

  method getNonRelationalValue:
           string -> variable_t -> non_relational_domain_value_t option

  method getConstant: variable_t -> numerical_t option

  method getRange: variable_t -> interval_t option

  method getBaseOffset: variable_t -> base_offset_t option

  method getAffineOffset: variable_t -> variable_t -> numerical_t option

  method getSomeAffineOffset:
           variable_t list -> variable_t -> (variable_t * numerical_t) option

end


val mk_inv_accessor: atlas_t -> inv_accessor_int

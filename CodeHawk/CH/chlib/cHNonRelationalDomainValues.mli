(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
  ============================================================================== *)

type nr_domain_value_t =
  | NUM_CONSTANT_VAL of CHConstants.numerical_constant_t
  | SYM_CONSTANT_VAL of CHConstants.symbolic_constant_t
  | ORDERED_SYM_CONSTANT_VAL of CHConstants.ordered_symbolic_constant_t
  | BOOL_CONSTANT_VAL of CHConstants.boolean_constant_t
  | INTERVAL_VAL of CHIntervals.interval_t
  | TINTERVAL_VAL of CHTIntervals.tinterval_t
  | STRIDED_INTERVAL_VAL of CHStridedIntervals.strided_interval_t
  | PEPR_VAL of CHPEPRTypes.pepr_value_int
  | VALUESET_VAL of CHValueSets.valueset_t
  | SYM_SET_VAL of CHSymbolicSets.symbolic_set_t
  | EXTERNAL_VALUE of CHExternalValues.external_value_int
  | TOP_VAL
  | BOTTOM_VAL
  
val normalize_nr_value : nr_domain_value_t -> nr_domain_value_t
  
class non_relational_domain_value_t :
  nr_domain_value_t ->
  object ('a)
    val value : nr_domain_value_t
    method getValue : nr_domain_value_t
    method isBottom : bool
    method isTop : bool
    method join : 'a -> 'a
    method leq : 'a -> bool
    method meet : 'a -> 'a
    method narrowing : 'a -> 'a
    method private notNormal : unit
    method numericalConstant : CHNumerical.numerical_t option
    method toExternalValue : CHExternalValues.external_value_int
    method toInterval : CHIntervals.interval_t
    method toNumericalConstant : CHConstants.numerical_constant_t
    method toNumericalConstraints :
      CHLanguage.variable_t ->
      CHNumericalConstraints.numerical_constraint_t list
    method toPretty : CHPretty.pretty_t
    method toStridedInterval : CHStridedIntervals.strided_interval_t
    method toSymbolicConstant : CHConstants.symbolic_constant_t
    method toOrderedSymbolicConstant: CHConstants.ordered_symbolic_constant_t
    method toSymbolicSet : CHSymbolicSets.symbolic_set_t
    method toTInterval : CHTIntervals.tinterval_t
    method toPEPRValue: CHPEPRTypes.pepr_value_int
    method toValueSet : CHValueSets.valueset_t
    method widening : 'a -> 'a
  end

val topNonRelationalDomainValue : non_relational_domain_value_t

val bottomNonRelationalDomainValue : non_relational_domain_value_t

val mkNumericalConstantValue :
  CHConstants.numerical_constant_t -> non_relational_domain_value_t

val mkSymbolicConstantValue :
  CHConstants.symbolic_constant_t -> non_relational_domain_value_t

val mkOrderedSymbolicConstantValue:
  CHConstants.ordered_symbolic_constant_t -> non_relational_domain_value_t

val mkBooleanConstantValue :
  CHConstants.boolean_constant_t -> non_relational_domain_value_t

val mkIntervalValue : CHIntervals.interval_t -> non_relational_domain_value_t

val mkTIntervalValue :
  CHTIntervals.tinterval_t -> non_relational_domain_value_t

val mkStridedIntervalValue :
  CHStridedIntervals.strided_interval_t -> non_relational_domain_value_t

val mkSymbolicSetValue :
  CHSymbolicSets.symbolic_set_t -> non_relational_domain_value_t

val mkValueSetValue : CHValueSets.valueset_t -> non_relational_domain_value_t

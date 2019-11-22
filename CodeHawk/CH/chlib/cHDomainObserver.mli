(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

open Big_int_Z
   
class domain_observer_t :
  object
    method getAssocList : (int * int) list option
    method getMatrix : big_int array array option
    method getNonRelationalExtensiveArrayObserver :
      CHLanguage.variable_t ->
      CHNumerical.numerical_t ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
    method getNonRelationalVariableObserver :
      CHLanguage.variable_t ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
    method getNumericalConstraints :
      variables:CHLanguage.variable_t list option ->
      unit -> CHNumericalConstraints.numerical_constraint_t list
    method getObservedArrayIndices :
      CHLanguage.variable_t -> CHNumerical.numerical_t list
    method getObservedArrays : CHLanguage.variable_t list
    method getObservedFactors :
      CHNumericalConstraints.numerical_factor_t list
    method getObservedVariables : CHLanguage.variable_t list
    method getPolyhedron : CHPolyhedra.polyhedron_t option
    method getVariableOrdering : CHLanguage.variable_t array option
    method isBottom : bool option
    method isTop : bool option
  end

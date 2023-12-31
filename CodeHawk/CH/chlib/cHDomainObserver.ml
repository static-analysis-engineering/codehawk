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

(* chlib *)
open CHLanguage   
open CHNonRelationalDomainValues   
open CHNumerical
open CHNumericalConstraints
open CHPolyhedra   

[@@@warning "-27"]

class domain_observer_t =
object

  method getObservedVariables: variable_t list = []
    
  method getObservedArrays: variable_t list = []
      
  method getObservedArrayIndices (_a: variable_t): numerical_t list = []

  method getObservedFactors: numerical_factor_t list = []

  method getNonRelationalVariableObserver: variable_t -> non_relational_domain_value_t =
    fun _v -> topNonRelationalDomainValue      

  method getNonRelationalExtensiveArrayObserver:
           variable_t -> numerical_t -> non_relational_domain_value_t =
    fun _v _i -> topNonRelationalDomainValue      

  method getNumericalConstraints
           ~(variables: variable_t list option) (): numerical_constraint_t list =
    []

  method getPolyhedron: polyhedron_t option = None

  method getVariableOrdering: variable_t array option = None
      
  method getAssocList: (int * int) list option = None

  method getMatrix: big_int array array option = None

  method isTop: bool option = None

  method isBottom: bool option = None
end

(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Henny Sipma
   ------------------------------------------------------------------------------
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
  ------------------------------------------------------------------------------ *)

(* chlib *)
open CHBounds
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty

(* ========================================================== indexed tables *)
class type indexed_htable_int =
  object
    method add: (string list * int list) -> int
    method reset: unit
    method toPretty: pretty_t
  end
  
(* ============================================================== pepr types *)

class type pepr_param_int =
  object
    method get_variable: variable_t
    method lb: numerical_t option
    method ub: numerical_t option
    method toPretty: pretty_t
  end

class type pepr_params_int =
  object
    method get_params: pepr_param_int list
    method nth: int -> pepr_param_int
    method has_variable: variable_t -> bool
    method variable_index: variable_t -> int
    method size: int
    method toPretty: pretty_t
  end

class type coeff_vector_int =
  object ('a)
    method index: int
    method get_k: numerical_t list
    method equal: 'a -> bool
    method compare: 'a -> int
    method neg: 'a
    method add: 'a -> 'a
    method mult: numerical_t -> 'a
    method is_zero: bool
    method is_unary: bool
    method get_single_coefficient_index: int
    method get_pairs: (int * numerical_t) list
    method toPretty: pretty_t
  end

type param_dep_type_t = P_EQ | P_INEQ   (* = 0, >= 0 *)

class type param_constraint_int =
  object ('a)
    method index: int
    method get_n: numerical_t
    method get_k: coeff_vector_int
    method get_pt: param_dep_type_t
    method compare: 'a -> int
    method equal: 'a -> bool
    method neg: 'a
    method add: 'a -> 'a
    method toPretty: pretty_t
  end

class type param_constraint_set_int =
  object ('a)
    method index: int
    method get_s: param_constraint_int list
    method compare: 'a -> int
    method equal: 'a -> bool
    method leq: 'a -> bool

    method is_top: bool
    method is_bottom: bool

    method join: 'a -> 'a
    method meet: 'a -> 'a
    method widening: 'a -> 'a
    method narrowing: 'a -> 'a

    method neg: 'a
    method add: 'a -> 'a
    method sub: 'a -> 'a
    method mult : 'a -> 'a
    method div: 'a -> 'a

    method toPretty: pretty_t

  end

type bound_type_t = LB | UB
                       
(* K, I: K x P + I *)
class type pex_int =
  object ('a)
    method index: int
    method get_n: numerical_t
    method get_k: coeff_vector_int
    method get_bt: bound_type_t
    method compare: 'a -> int
    method equal: 'a -> bool
    method leq: 'a -> bool
    method disjoint: 'a -> bool
    method neg: 'a
    method add: 'a -> 'a
    method mult: numerical_t -> 'a
    method meet: 'a -> 'a
    method join: 'a -> 'a
    method is_number: bool
    method get_number: numerical_t
    method is_parameter: bool              (* single parameter, zero offset *)
    method get_parameter_index: int        (* single parameter, zero offset *)
    method toPretty: pretty_t
  end


(* S: set of (K,I) *)
class type pex_set_int =
  object ('a)
    method index: int
    method get_s: pex_int list
    method compare: 'a -> int
    method equal: 'a -> bool
    method leq: 'a -> bool
    method disjoint: 'a -> bool
    method neg: 'a
    method add: 'a -> 'a
    method mult: numerical_t -> 'a
    method meet: 'a -> 'a
    method is_top: bool
    method is_number: bool
    method is_parameter: bool             (* single parameter, zero offst *)
    method get_number: numerical_t
    method get_parameter_indices: int list
    method strip_dependencies: pex_int -> 'a * (param_constraint_int list)
    method remove_pex: pex_int -> 'a
    method toPretty: pretty_t
  end

(* P: set of S (set of set of (K,I)) *)
class type pex_pset_int =
  object ('a)
    method index: int
    method get_p: pex_set_int list
    method compare: 'a -> int
    method equal: 'a -> bool
    method leq: 'a -> bool
    method disjoint: 'a -> bool
    method neg: 'a
    method add: 'a -> 'a
    method mult: numerical_t -> 'a
    method meet: 'a -> 'a
    method join: 'a -> 'a
    method widening: 'a -> 'a
    method is_top: bool
    method is_number: bool
    method get_number: numerical_t
    method get_parameter_indices: int list
    method get_parameter_exprs: pex_int list
    method remove_pex: pex_int -> 'a
    method strip_dependencies: pex_int -> 'a * (param_constraint_int list)
    method toPretty: pretty_t
  end

type pepr_bounds_t =
  | XTOP
  | XPSET of pex_pset_int

class type pepr_bound_int =
  object ('a)
    method index: int
    method get_bound: pepr_bounds_t
    method equal: 'a -> bool
    method leq: 'a -> bool
    method disjoint: 'a -> bool
    method neg: 'a
    method add: 'a -> 'a
    method mult: 'a -> 'a
    method multc: numerical_t -> 'a
    method meet: 'a -> 'a
    method join: 'a -> 'a
    method widening: 'a -> 'a
    method is_top: bool
    method is_number: bool
    method get_number: numerical_t
    method get_parameter_indices: int list
    method get_parameter_exprs: pex_int list
    method remove_pex: pex_int -> 'a
    method strip_dependencies: pex_int -> 'a * (param_constraint_int list)
    method toPretty: pretty_t
  end


(* ============================================================= pepr dictionary *)

class type pepr_dictionary_int =
  object ('a)
    method reset: unit
    method index_coefficients: numerical_t list -> int
    method index_coeff_vector: coeff_vector_int -> int
    method index_param_constraint_data: coeff_vector_int -> numerical_t -> param_dep_type_t -> int
    method index_param_constraint: param_constraint_int -> int
    method index_param_constraint_set_data: param_constraint_int list -> int
    method index_param_constraint_set: param_constraint_set_int -> int
    method index_pex_data: coeff_vector_int -> numerical_t -> bound_type_t -> int
    method index_pex: pex_int -> int
    method index_pex_set_data: pex_int list -> int
    method index_pex_set: pex_set_int -> int
    method index_pex_pset_data: pex_set_int list -> int
    method index_pex_pset: pex_pset_int -> int
    method index_pepr_bound_data: pepr_bounds_t -> int
    method index_pepr_bound: pepr_bound_int -> int
    method toPretty: pretty_t
  end

(* ================================================================== pepr range *)

class type pepr_range_int =
  object ('a)
    method equal: 'a -> bool
    method leq: 'a -> bool

    method join: 'a -> 'a
    method meet: 'a -> 'a

    method widening: 'a -> 'a
    method narrowing: 'a -> 'a

    method neg: 'a
    method add: 'a -> 'a
    method sub: 'a -> 'a
    method mult: 'a -> 'a
    method multc: numerical_t -> 'a
    method div: 'a -> 'a
         
    method get_min: pepr_bound_int
    method get_max: pepr_bound_int

    method is_top: bool
    method is_bottom: bool
    method is_bounded:bool

    method lower_bound: pepr_bound_int -> 'a * param_constraint_set_int
    method upper_bound: pepr_bound_int -> 'a * param_constraint_set_int
    method strict_lower_bound: pepr_bound_int -> 'a * param_constraint_set_int
    method strict_upper_bound: pepr_bound_int -> 'a * param_constraint_set_int

    method singleton: numerical_t option    (* singleton interval *)
    method interval: interval_t option      (* no parameter dependencies *)
         
    method parameters: int list             (* single parameter, coefficient 1 *)
    method parameter_exprs: (coeff_vector_int * numerical_t) list

    method remove_singleton: numerical_t -> 'a
    method remove_interval: interval_t -> 'a
    method remove_equality: coeff_vector_int -> numerical_t -> 'a

    method toPretty: pretty_t
  end

type pepr_value_type_t =
  | PEPRTOP
  | PEPRANGE of pepr_range_int
  | PEPRDEP of param_constraint_set_int

class type pepr_value_int =
  object ('a)
    method index: int
         
    method equal: 'a -> bool
    method leq: 'a -> bool

    method join: 'a -> 'a
    method meet: 'a -> 'a
    method widening: 'a -> 'a
    method narrowing: 'a -> 'a

    method neg: 'a
    method add: 'a -> 'a
    method sub: 'a -> 'a
    method mult: 'a -> 'a
    method multc: numerical_t -> 'a
    method div: 'a -> 'a

    method get_value: pepr_value_type_t
    method get_min: pepr_bound_int
    method get_max: pepr_bound_int

    method is_top: bool
    method is_bottom: bool
    method is_bounded: bool

    method lower_bound: pepr_bound_int -> ('a * 'a)
    method upper_bound: pepr_bound_int -> ('a * 'a)
    method strict_lower_bound: pepr_bound_int -> ('a * 'a)
    method strict_upper_bound: pepr_bound_int -> ('a * 'a)

    method singleton: numerical_t option
    method interval: interval_t option

    method parameters: int list
    method parameter_exprs: (coeff_vector_int * numerical_t) list

    method toPretty: pretty_t
  end

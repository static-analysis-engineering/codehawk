(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Henny Sipma
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

(* chlib *)
open CHDomainObserver
open CHLanguage
open CHNonRelationalDomainValues
open CHNumericalConstraints
open CHPEPRTypes
open CHPretty


class type pepr_domain_no_arrays_int =
  object ('a)

    (* operations *)
    method analyzeBwd: (code_int, cfg_int) command_t -> 'a
    method analyzeBwdInTransaction: (code_int,cfg_int) command_t -> 'a
    method analyzeFwd: (code_int, cfg_int) command_t -> 'a
    method analyzeFwdInTransaction: (code_int,cfg_int) command_t -> 'a
    method analyzeOperation:
             domain_name:string -> fwd_direction:bool -> operation:operation_t -> 'a

    method importNonRelationalValues:
             ?refine:bool -> (variable_t * non_relational_domain_value_t) list -> 'a
    method importNumericalConstraints: numerical_constraint_t list -> 'a

    method clone: 'a
    method setDownlink: (string -> 'a) -> unit
    method join: ?variables:variable_t list -> 'a -> 'a
    method meet: ?variables:variable_t list -> 'a -> 'a
    method widening: ?kind:string -> ?variables:variable_t list -> 'a -> 'a
    method narrowing: ?variables:variable_t list -> 'a -> 'a

    method projectOut: variable_t list -> 'a
    method special: string -> domain_cmd_arg_t list -> 'a

    method mkBottom: 'a
    method mkEmpty: 'a

    (* accessors *)
    method getNonRelationalValue: variable_t -> non_relational_domain_value_t

    method observer: domain_observer_t

    (* predicates *)
    method isBottom: bool
    method isRelational: bool
    method equal: 'a -> bool
    method leq: ?variables:variable_t list -> 'a -> bool

    (* printing *)
    method toPretty: pretty_t

  end

val mk_pepr_domain_no_arrays: pepr_params_int -> float -> pepr_domain_no_arrays_int

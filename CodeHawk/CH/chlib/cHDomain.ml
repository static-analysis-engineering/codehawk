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

(* chlib *)
open CHCommon
open CHDomainObserver   
open CHLanguage
open CHNonRelationalDomainValues
open CHNumericalConstraints   
open CHPretty


class type domain_int =
object ('a)

  method isRelational: bool
  method setDownlink: (string -> 'a) -> unit
  method mkBottom: 'a
  method mkEmpty: 'a
  method isBottom: bool
  method leq: ?variables: variable_t list -> 'a -> bool
  method equal: 'a -> bool
  method meet: ?variables: variable_t list -> 'a -> 'a
  method join: ?variables: variable_t list -> 'a -> 'a
  method widening: ?kind:string -> ?variables: variable_t list -> 'a -> 'a
  method narrowing: ?variables: variable_t list -> 'a -> 'a
  method projectOut: variable_t list -> 'a
  method observer: domain_observer_t
  method getNonRelationalValue: variable_t -> non_relational_domain_value_t
  method importNonRelationalValues:
           ?refine: bool -> (variable_t * non_relational_domain_value_t) list -> 'a
  method importNumericalConstraints: numerical_constraint_t list -> 'a
  method toPretty: pretty_t
  method special: string -> domain_cmd_arg_t list -> 'a
  method analyzeFwd: (code_int, cfg_int) command_t -> 'a
  method analyzeBwd: (code_int, cfg_int) command_t -> 'a
  method analyzeFwdInTransaction: (code_int, cfg_int) command_t -> 'a
  method analyzeBwdInTransaction: (code_int, cfg_int) command_t -> 'a
  method analyzeOperation:
           domain_name: string -> fwd_direction: bool -> operation: operation_t -> 'a
  method clone: 'a
    
end


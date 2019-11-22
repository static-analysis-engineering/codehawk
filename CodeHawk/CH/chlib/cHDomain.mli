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

class type domain_int =
  object ('a)
    method analyzeBwd :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeBwdInTransaction :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeFwd :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeFwdInTransaction :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeOperation :
      domain_name:string ->
      fwd_direction:bool -> operation:CHLanguage.operation_t -> 'a
    method clone : 'a
    method equal : 'a -> bool
    method getNonRelationalValue :
      CHLanguage.variable_t ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
    method importNonRelationalValues :
      ?refine:bool ->
      (CHLanguage.variable_t *
       CHNonRelationalDomainValues.non_relational_domain_value_t)
      list -> 'a
    method importNumericalConstraints :
      CHNumericalConstraints.numerical_constraint_t list -> 'a
    method isBottom : bool
    method isRelational : bool
    method join : ?variables:CHLanguage.variable_t list -> 'a -> 'a
    method leq : ?variables:CHLanguage.variable_t list -> 'a -> bool
    method meet : ?variables:CHLanguage.variable_t list -> 'a -> 'a
    method mkBottom : 'a
    method mkEmpty : 'a
    method narrowing : ?variables:CHLanguage.variable_t list -> 'a -> 'a
    method observer : CHDomainObserver.domain_observer_t
    method projectOut : CHLanguage.variable_t list -> 'a
    method setDownlink : (string -> 'a) -> unit
    method special : string -> CHLanguage.domain_cmd_arg_t list -> 'a
    method toPretty : CHPretty.pretty_t
    method widening :
      ?kind:string -> ?variables:CHLanguage.variable_t list -> 'a -> 'a
  end

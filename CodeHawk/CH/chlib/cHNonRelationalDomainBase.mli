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

class virtual non_relational_domain_base_int :
  object ('a)
    val virtual table :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
    method virtual analyzeBwd :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method private virtual analyzeBwd' :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeBwdInTransaction :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method virtual analyzeFwd :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method private virtual analyzeFwd' :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeFwdInTransaction :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method clone : 'a
    method private virtual getValue : CHLanguage.variable_t -> 'b
    method virtual isBottom : bool
    method private virtual join_tables :
      ?variables:CHLanguage.variable_t list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
    method private virtual leq' :
      ?variables:CHLanguage.variable_t list -> 'a -> bool
    method private virtual meet_tables :
      ?variables:CHLanguage.variable_t list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
    method virtual mkBottom : 'a
    method private virtual narrowing_tables :
      ?variables:CHLanguage.variable_t list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
    method private virtual observer' : CHDomainObserver.domain_observer_t
    method private virtual setValue :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t ->
      CHLanguage.variable_t -> 'b -> unit
    method virtual special : string -> CHLanguage.domain_cmd_arg_t list -> 'a
    method private virtual widening_tables :
      ?variables:CHLanguage.variable_t list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
  end

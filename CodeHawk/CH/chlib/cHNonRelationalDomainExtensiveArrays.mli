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

class virtual non_relational_domain_extensive_arrays_t :
  bool ->
  string ->
  object ('a)
    val arrays :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t
    val expand_all_arrays : CHIntervals.interval_t option
    val expansions :
      CHIntervals.interval_t CHUtils.VariableCollections.table_t
    val indexDomain : string
    val precise_read_write_enabled : bool
    val virtual table :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
    method private abstractElements :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t ->
      CHUtils.VariableCollections.ObjectMap.key ->
      CHIntervals.interval_t -> unit
    method private abstractVariables' :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t ->
      CHIntervals.interval_t CHUtils.VariableCollections.table_t ->
      CHUtils.VariableCollections.ObjectMap.key list -> unit
    method private abstract_elts :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t ->
      CHIntervals.interval_t CHUtils.VariableCollections.table_t ->
      CHUtils.VariableCollections.ObjectMap.key ->
      CHLanguage.variable_t -> CHLanguage.variable_t -> unit
    method analyzeBwd :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method private virtual analyzeBwd' :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeBwdInTransaction :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeFwd :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method private virtual analyzeFwd' :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeFwdInTransaction :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeOperation :
      domain_name:string ->
      fwd_direction:bool -> operation:CHLanguage.operation_t -> 'a
    method private assign_array_elt :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t ->
      CHUtils.VariableCollections.ObjectMap.key ->
      CHLanguage.variable_t -> CHLanguage.variable_t -> unit
    method clone : 'a
    method private virtual getDownlink : string -> 'a
    method private getElement :
      CHUtils.VariableCollections.ObjectMap.key ->
      CHUtils.NumericalCollections.ObjectMap.key ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
    method private getElements :
      CHUtils.VariableCollections.ObjectMap.key ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
    method private getExpansion :
      CHUtils.VariableCollections.ObjectMap.key -> CHIntervals.interval_t
    method private getIndex : CHLanguage.variable_t -> CHIntervals.interval_t
    method private virtual getValue :
      CHLanguage.variable_t ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
    method virtual isBottom : bool
    method join :
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list -> 'a -> 'a
    method private join_like :
      (CHNonRelationalDomainValues.non_relational_domain_value_t ->
       CHNonRelationalDomainValues.non_relational_domain_value_t ->
       CHNonRelationalDomainValues.non_relational_domain_value_t) ->
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t
    method private virtual join_tables :
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
    method private leq : ?variables:CHLanguage.variable_t list -> 'a -> bool
    method private virtual leq' :
      ?variables:CHLanguage.variable_t list -> 'a -> bool
    method meet :
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list -> 'a -> 'a
    method private meet_like :
      (CHNonRelationalDomainValues.non_relational_domain_value_t ->
       CHNonRelationalDomainValues.non_relational_domain_value_t ->
       CHNonRelationalDomainValues.non_relational_domain_value_t) ->
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t
    method private virtual meet_tables :
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
    method virtual mkBottom : 'a
    method private mkBottom' : 'a
    method narrowing :
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list -> 'a -> 'a
    method private virtual narrowing_tables :
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
    method observer : CHDomainObserver.domain_observer_t
    method private virtual observer' : CHDomainObserver.domain_observer_t
    method private read_array_elt :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t ->
      CHUtils.VariableCollections.ObjectMap.key ->
      CHUtils.VariableCollections.ObjectMap.key ->
      CHLanguage.variable_t -> unit
    method private setElement :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.NumericalCollections.table_t
      CHUtils.VariableCollections.table_t ->
      CHUtils.VariableCollections.ObjectMap.key ->
      CHUtils.NumericalCollections.ObjectMap.key ->
      CHNonRelationalDomainValues.non_relational_domain_value_t -> unit
    method private setExpansion :
      CHIntervals.interval_t CHUtils.VariableCollections.table_t ->
      CHUtils.VariableCollections.ObjectMap.key ->
      CHIntervals.interval_t -> unit
    method private virtual setValue :
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t ->
      CHLanguage.variable_t ->
      CHNonRelationalDomainValues.non_relational_domain_value_t -> unit
    method special : string -> CHLanguage.domain_cmd_arg_t list -> 'a
    method toPretty : CHPretty.pretty_t
    method widening :
      ?kind:string ->
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list -> 'a -> 'a
    method private virtual widening_tables :
      ?variables:CHUtils.VariableCollections.ObjectSet.elt list ->
      'a ->
      CHNonRelationalDomainValues.non_relational_domain_value_t
      CHUtils.VariableCollections.table_t
  end

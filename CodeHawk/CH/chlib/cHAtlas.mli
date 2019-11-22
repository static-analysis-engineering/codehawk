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

class atlas_t :
  ?db_num:CHUtils.StringCollections.ObjectMap.key ->
  ?db_sym:CHUtils.StringCollections.ObjectMap.key ->
  ?sigmas:'a CHSigmaCombinator.sigma_combinator_int list ->
  (CHUtils.StringCollections.ObjectMap.key * CHDomain.domain_int) list ->
  object ('a)
    val database : CHNonRelationalDatabase.non_relational_database_t
    val db_num_domain : CHUtils.StringCollections.ObjectMap.key
    val db_sym_domain : CHUtils.StringCollections.ObjectMap.key
    val domains : CHDomain.domain_int CHUtils.StringCollections.table_t
    val initials : CHDomain.domain_int CHUtils.StringCollections.table_t
    val reductions : 'a CHSigmaCombinator.sigma_combinator_int list
    method activateDomains :
      CHUtils.StringCollections.ObjectMap.key list -> 'a
    method analyzeBwd :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method private analyzeBwd' :
      in_transaction:bool ->
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeBwdInTransaction :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeDBQuery :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeDBQueryNoDB :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeDBUpdate :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeFwd :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method private analyzeFwd' :
      in_transaction:bool ->
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method analyzeFwdInTransaction :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 'a
    method private checkCompatibility : 'a -> unit
    method clone : 'a
    method deactivateDomains :
      CHUtils.StringCollections.ObjectMap.key list -> 'a
    method domainOperation :
      bool ->
      CHUtils.StringCollections.ObjectMap.key list ->
      CHLanguage.operation_t -> 'a
    method equal : 'a -> bool
    method getDatabase : CHNonRelationalDatabase.non_relational_database_t
    method getDomain :
      CHUtils.StringCollections.ObjectMap.key -> CHDomain.domain_int
    method getDomains : CHUtils.StringCollections.ObjectSet.elt list
    method private hasDomain :
      CHUtils.StringCollections.ObjectMap.key -> bool
    method hasRelationalDomain : bool
    method isBottom : bool
    method join : ?variables:CHLanguage.variable_t list -> 'a -> 'a
    method leq : ?variables:CHLanguage.variable_t list -> 'a -> bool
    method meet : ?variables:CHLanguage.variable_t list -> 'a -> 'a
    method mkBottom : 'a
    method mkEmpty : 'a
    method move :
      relational:bool ->
      vars:CHLanguage.variable_t list ->
      src:CHUtils.StringCollections.ObjectMap.key ->
      tgt:CHUtils.StringCollections.ObjectMap.key -> 'a
    method narrowing : ?variables:CHLanguage.variable_t list -> 'a -> 'a
    method reduce : 'a
    method sendCmd :
      CHUtils.StringCollections.ObjectMap.key ->
      string -> CHLanguage.domain_cmd_arg_t list -> 'a
    method setDomains :
      (CHUtils.StringCollections.ObjectMap.key * CHDomain.domain_int) list ->
      'a
    method toPretty : CHPretty.pretty_t
    method updateDownlinks : unit
    method widening :
      ?kind:string -> ?variables:CHLanguage.variable_t list -> 'a -> 'a
  end

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

class non_relational_database_t :
  object ('a)
    val tables :
      CHNonRelationalTable.non_relational_table_t
      CHUtils.VariableCollections.table_t
    method analyzeQuery :
      db_num:CHDomain.domain_int ->
      db_sym:CHDomain.domain_int ->
      cmd:(CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
      (CHLanguage.variable_t *
       CHNonRelationalDomainValues.non_relational_domain_value_t)
      list
    method analyzeQueryNoDB :
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
      (CHLanguage.variable_t *
       CHNonRelationalDomainValues.non_relational_domain_value_t)
      list
    method analyzeUpdate :
      db_num:CHDomain.domain_int ->
      db_sym:CHDomain.domain_int ->
      cmd:(CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
      'a
    method equal : 'a -> bool
    method getRows :
      CHLanguage.variable_t ->
      (CHUtils.StringCollections.ObjectSet.elt *
       CHNonRelationalDomainValues.non_relational_domain_value_t)
      list list
    method getTables :
      CHNonRelationalTable.non_relational_table_t
      CHUtils.VariableCollections.table_t
    method join : 'a -> 'a
    method leq : 'a -> bool
    method meet : 'a -> 'a
    method narrowing : 'a -> 'a
    method removeTables :
      CHUtils.VariableCollections.ObjectMap.key list -> 'a
    method toPretty : CHPretty.pretty_t
    method widening : 'a -> 'a
  end

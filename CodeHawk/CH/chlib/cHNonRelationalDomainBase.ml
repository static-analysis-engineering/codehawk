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

(* chlib  *)
open CHCommon
open CHDomainObserver   
open CHLanguage
open CHNonRelationalDomainValues   
open CHUtils


class virtual non_relational_domain_base_int =
object (self: 'a)
  
  val virtual table: non_relational_domain_value_t VariableCollections.table_t

  method virtual isBottom: bool
    
  method virtual mkBottom: 'a

  method virtual special: string -> domain_cmd_arg_t list -> 'a

  method virtual analyzeFwd: (code_int, cfg_int) command_t -> 'a

  method virtual analyzeBwd: (code_int, cfg_int) command_t -> 'a

  method analyzeFwdInTransaction = self#analyzeFwd

  method analyzeBwdInTransaction = self#analyzeBwd

  method clone = {< >}
    
  method virtual private leq': ?variables: variable_t list -> 'a -> bool

  method virtual private observer': domain_observer_t

  method virtual private analyzeFwd': (code_int, cfg_int) command_t -> 'a
    
  method virtual private analyzeBwd': (code_int, cfg_int) command_t -> 'a

  method virtual private getValue: variable_t -> 'v
    
  method virtual private setValue:
                           non_relational_domain_value_t VariableCollections.table_t
                           -> variable_t
                           -> 'v
                           -> unit

  method virtual private meet_tables:
                           ?variables: variable_t list
                           -> 'a
                           -> non_relational_domain_value_t VariableCollections.table_t

  method virtual private join_tables:
                           ?variables: variable_t list
                           -> 'a
                           -> non_relational_domain_value_t VariableCollections.table_t

  method virtual private narrowing_tables:
                           ?variables: variable_t list
                           -> 'a
                           -> non_relational_domain_value_t VariableCollections.table_t

  method virtual private widening_tables:
                           ?variables: variable_t list
                           -> 'a
                           -> non_relational_domain_value_t VariableCollections.table_t

end

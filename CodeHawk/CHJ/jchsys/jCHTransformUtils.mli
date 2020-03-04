(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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
   ============================================================================= *)

(* chlib *)
open CHLanguage
open CHNumerical
open CHPretty   
open CHUtils

val does_not_need_to_be_analyzed : symbol_t -> procedure_int -> bool

val mk_state : state_int -> code_int -> state_int

val get_vars_in_code : 
  symbol_t
  -> code_int
  -> VariableCollections.set_t
     * VariableCollections.set_t
     * VariableCollections.set_t
  
val get_vars_in_cmd : 
  symbol_t 
  -> (code_int, cfg_int) command_t
  -> VariableCollections.set_t
     * VariableCollections.set_t
     * VariableCollections.set_t

class ['a] pretty_stack_t :
  object
    constraint 'a = < toPretty : pretty_t; .. >
    val mutable stack : 'a list
    method clear : unit
    method listFromBottom : 'a list
    method listFromTop : 'a list
    method pop : 'a
    method push : 'a -> unit
    method toPretty : pretty_t
    method top : 'a
  end


class vv_stacks_t :
  object ('a)
    method get : variable_t -> variable_t pretty_stack_t option
    method get_top : variable_t -> variable_t
    method get_tops : variable_t VariableCollections.table_t 
    method increase_assignments :
      variable_t -> unit
    method num_assignments : JCHPrintUtils.pretty_int_t VariableCollections.table_t
    method pop : JCHPrintUtils.pretty_int_t VariableCollections.table_t -> unit
    method push : variable_t -> variable_t -> unit
    method reset_num_assignments : unit
    method toPretty : pretty_t

  end

class alias_sets_t :
  object
    method add : variable_t -> variable_t -> unit
    method add_const : variable_t -> numerical_t -> unit
    method change_representative : variable_t VariableCollections.table_t -> unit
    method find_aliased_locals : (variable_t * variable_t) list
    method get_representative : variable_t -> variable_t option
    method get_representatives : variable_t VariableCollections.table_t 
    method toPretty : pretty_t
  end

class ssa_variable_t :
  object
    method get_scope : scope_int
    method make_new_variable : variable_t -> variable_t
    method make_new_temp : variable_t -> variable_t
    method set_scope : scope_int -> unit
    method set_stacks : vv_stacks_t -> unit
  end

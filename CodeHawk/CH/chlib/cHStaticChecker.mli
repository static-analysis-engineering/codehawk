(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
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

class static_type_checker_t :
        bool ->
        (< getProcedure :
             CHLanguage.symbol_t ->
             < getSignature : (CHUtils.SymbolCollections.ObjectMap.key *
                                 CHLanguage.variable_type_t *
                                   CHLanguage.arg_mode_t)
                                list;
         .. >;
           hasProcedure : CHLanguage.symbol_t -> bool; .. >
                                                       as 'a) ->
        < getNumTmpVariables : CHUtils.VariableCollections.ObjectSet.elt list;
      getSymTmpVariables : CHUtils.VariableCollections.ObjectSet.elt list;
      getVariables : CHUtils.VariableCollections.ObjectSet.elt list; .. > ->
  object
    val mutable in_transaction : bool
    val num_tmp_vars : CHUtils.VariableCollections.set_t
    val sym_tmp_vars : CHUtils.VariableCollections.set_t
    val system : 'a
    val vars : CHUtils.VariableCollections.set_t
    method private error : CHPretty.pretty_t list -> unit
    method private hasVariable :
                     CHUtils.VariableCollections.set_t -> CHLanguage.variable_t -> bool
    method walkBoolExp : CHLanguage.boolean_exp_t -> unit
    method walkCmd :
             (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> unit
    method walkCode : CHLanguage.code_int -> unit
    method walkNumExp : CHLanguage.numerical_exp_t -> unit
    method walkSymExp : CHLanguage.symbolic_exp_t -> unit
    method walkVar : CHLanguage.variable_t -> unit
  end
      
class static_checker_t :
        CHLanguage.system_int ->
        object
          val system : CHLanguage.system_int
          method checkAll : unit
          method checkProcedure : ?locally:bool -> CHLanguage.symbol_t -> unit
        end
    

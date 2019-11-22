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

class code_t :
        int -> 
        ?command_to_pretty:
          ((CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> 
	   CHPretty.pretty_t) ->
        (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t list ->
	CHLanguage.code_int
    
class state_t :
        CHLanguage.symbol_t -> CHLanguage.code_int -> CHLanguage.state_int

class cfg_t :
        int -> CHLanguage.symbol_t -> CHLanguage.symbol_t -> CHLanguage.cfg_int

class scope_t :
  tmp_base:string ->
  register_base:string ->
  object ('a)
    val mutable in_transaction : bool
    val mutable max_available_suffix : int
    val num_array_tmp_vars : CHUtils.VariableCollections.set_t
    val num_tmp_vars : CHUtils.VariableCollections.set_t
    val register_base_name : CHLanguage.symbol_t
    val sym_array_tmp_vars : CHUtils.VariableCollections.set_t
    val sym_tmp_vars : CHUtils.VariableCollections.set_t
    val tmp_base_name : string
    val mutable transaction_num_array_tmp :
                  CHUtils.VariableCollections.ObjectSet.elt list
    val mutable transaction_num_tmp :
                  CHUtils.VariableCollections.ObjectSet.elt list
    val mutable transaction_sym_array_tmp :
                  CHUtils.VariableCollections.ObjectSet.elt list
    val mutable transaction_sym_tmp :
                  CHUtils.VariableCollections.ObjectSet.elt list
    val mutable vars : CHUtils.VariableCollections.set_t
    method addVariable : CHUtils.VariableCollections.ObjectSet.elt -> unit
    method addVariables :
             CHUtils.VariableCollections.ObjectSet.elt list -> unit
    method endTransaction : unit
    method getNumTmpArrays : CHUtils.VariableCollections.ObjectSet.elt list
    method getNumTmpVariables :
             CHUtils.VariableCollections.ObjectSet.elt list
    method getSymTmpArrays : CHUtils.VariableCollections.ObjectSet.elt list
    method getSymTmpVariables :
             CHUtils.VariableCollections.ObjectSet.elt list
    method getVariables : CHUtils.VariableCollections.ObjectSet.elt list
    method getTmpBase: string
    method getRegisterBase: string
    method private makeVariable :
                     CHLanguage.symbol_t ->
                     ?register:bool -> CHLanguage.variable_type_t -> CHLanguage.variable_t
    method mergeWith :
             'a ->
             CHUtils.VariableCollections.ObjectMap.key ->
             CHUtils.VariableCollections.ObjectMap.key
    method private mkNumTmpArray : CHLanguage.variable_t
    method private mkNumTmpVar : CHLanguage.variable_t
    method mkRegister : CHLanguage.variable_type_t -> CHLanguage.variable_t
    method private mkSymTmpArray : CHLanguage.variable_t
    method private mkSymTmpVar : CHLanguage.variable_t
    method mkVariable :
             CHLanguage.symbol_t ->
             CHLanguage.variable_type_t -> CHLanguage.variable_t
    method removeVariable : CHUtils.VariableCollections.ObjectSet.elt -> unit
    method removeVariables :
             CHUtils.VariableCollections.ObjectSet.elt list -> unit
    method private renameVariable :
                     CHUtils.VariableCollections.ObjectSet.elt ->
                     CHLanguage.variable_t CHUtils.VariableCollections.table_t -> unit
    method requestNumTmpArray : CHUtils.VariableCollections.ObjectSet.elt
    method requestNumTmpVariable : CHUtils.VariableCollections.ObjectSet.elt
    method requestSymTmpArray : CHUtils.VariableCollections.ObjectSet.elt
    method requestSymTmpVariable : CHUtils.VariableCollections.ObjectSet.elt
    method startTransaction : unit
    method toPretty : CHPretty.pretty_t
    method transformVariables :
             (CHUtils.VariableCollections.ObjectSet.elt ->
              CHUtils.VariableCollections.ObjectSet.elt) ->
             unit
  end
    
class procedure_t :
        CHLanguage.symbol_t ->
        CHLanguage.signature_t ->
        CHLanguage.bindings_t -> scope_t -> code_t -> CHLanguage.procedure_int
    
class system_t :
        CHLanguage.symbol_t ->
        object
          val name : CHLanguage.symbol_t
          val table : procedure_t CHUtils.SymbolCollections.table_t
          method addProcedure : procedure_t -> unit
          method getName : CHLanguage.symbol_t
          method getProcedure :
                   CHUtils.SymbolCollections.ObjectMap.key -> procedure_t
          method getProcedures : CHUtils.SymbolCollections.ObjectSet.elt list
          method hasProcedure : CHUtils.SymbolCollections.ObjectMap.key -> bool
          method toPretty : CHPretty.pretty_t
        end
    
module LanguageFactory :
sig
  val id_counter : int ref
  val command_pretty_printer :
    ((CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> CHPretty.pretty_t) ref
  val set_command_pretty_printer :
    ((CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t -> CHPretty.pretty_t) -> unit 
  val get_new_id : unit -> int
  val mkCode :
    (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t list ->
    code_t
  val mkState : CHLanguage.symbol_t -> CHLanguage.code_int -> state_t
  val mkCFG_s : CHLanguage.symbol_t -> CHLanguage.symbol_t -> cfg_t
  val mkCFG : CHLanguage.state_int -> CHLanguage.state_int -> cfg_t
  val mkScope :
    ?tmp_base:string -> ?register_base:string -> unit -> scope_t
  val mkProcedure :
    CHLanguage.symbol_t ->
    signature:CHLanguage.signature_t ->
    bindings:CHLanguage.bindings_t ->
    scope:scope_t -> body:code_t -> procedure_t
  val mkSystem : CHLanguage.symbol_t -> system_t
end
     

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

[@@@warning "-67"]
module Make :
functor (F: CHLanguage.LANGUAGE_FACTORY) ->
sig
  class inlining_processor_t :
          int ->
          CHNumerical.numerical_t CHUtils.SymbolCollections.table_t ->
          ?op_proc:CHLanguage.op_processor_t ->
          (CHLanguage.symbol_t -> bool) ->
          CHLanguage.system_int ->
          CHLanguage.scope_int ->
          object
            val context : CHLanguage.symbol_t list
            val depth : CHNumerical.numerical_t
            val excludes : CHLanguage.symbol_t -> bool
            val expanded :
              CHNumerical.numerical_t CHUtils.SymbolCollections.table_t
            val op_processor : CHLanguage.op_processor_t option
            val scope : CHLanguage.scope_int
            val system : CHLanguage.system_int
            method expand : CHLanguage.code_int -> unit
            method private inline : CHLanguage.symbol_t -> bool
            method transformCmd :
                     (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
                     (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t
            method transformCode : CHLanguage.code_int -> unit
          end
  class static_inliner_t :
          ?depth:int ->
          ?op_proc:CHLanguage.op_processor_t ->
          ?exclusions:(CHLanguage.symbol_t -> bool) ->
          CHLanguage.system_int ->
          object
            val excludes : CHLanguage.symbol_t -> bool
            val system : CHLanguage.system_int
            method expandProcedure : CHLanguage.symbol_t -> unit
          end
end

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

val zero : CHBounds.bound_t

val one : CHBounds.bound_t

class loop_stack_t :
  object ('a)
    val stack : CHLanguage.symbol_t list
    method delta : 'a -> 'a * 'a
    method getStack : CHLanguage.symbol_t list
    method isPrefix : 'a -> bool
    method push : CHLanguage.symbol_t -> 'a
    method toPretty : CHPretty.pretty_t
  end

type wto_component_t = SCC of wto_t | VERTEX of CHLanguage.symbol_t
and wto_t = wto_component_t list

val pretty_print_wto : wto_component_t list -> CHPretty.pretty_t

class wto_engine_t :
  CHUtils.graph_t ->
  object
    val dfn : CHBounds.bound_t CHUtils.SymbolCollections.table_t
    val graph : CHUtils.graph_t
    val nodeToStack : loop_stack_t CHUtils.SymbolCollections.table_t
    val mutable num : CHBounds.bound_t
    val stack : CHLanguage.symbol_t CHStack.stack_t
    method private component :
      loop_stack_t -> CHLanguage.symbol_t -> wto_component_t
    method computeWTO : wto_component_t list
    method private getDFN :
      CHUtils.SymbolCollections.ObjectMap.key -> CHBounds.bound_t
    method getLoopStackTable : loop_stack_t CHUtils.SymbolCollections.table_t
    method private shift :
      CHLanguage.symbol_t -> CHUtils.SymbolCollections.ObjectMap.key -> unit
    method private visit :
      loop_stack_t ->
      CHUtils.SymbolCollections.ObjectMap.key ->
      wto_component_t list ref -> CHBounds.bound_t
  end

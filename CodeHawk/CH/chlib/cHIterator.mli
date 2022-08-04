(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyright (c) 2021-2022 Aarno Labs LLC

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

type op_semantics_t =
    invariant:CHAtlas.atlas_t ->
    stable:bool ->
    fwd_direction:bool ->
    context:CHLanguage.symbol_t CHStack.stack_t ->
    operation:CHLanguage.operation_t -> CHAtlas.atlas_t

type cmd_processor_t =
    invariant:CHAtlas.atlas_t ->
    context:CHLanguage.symbol_t CHStack.stack_t ->
    cmd:(CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
    (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t

type proc_semantics_t =
    invariant:CHAtlas.atlas_t ->
    stable:bool ->
    context:CHLanguage.symbol_t CHStack.stack_t ->
    procedure:CHLanguage.symbol_t ->
    args:(CHLanguage.symbol_t * CHLanguage.variable_t) list ->
    CHAtlas.atlas_t

type iteration_strategy_t = {
  widening : int -> bool * string;
  narrowing : int -> bool;
}

type iteration_mode_t =
    WIDENING_MODE
  | NARROWING_MODE
  | STABLE_MODE
  | BREAKOUT_POINT of CHLanguage.symbol_t * CHAtlas.atlas_t ref

class boxed_mode_t :
  iteration_mode_t ->
  object
    val mode : iteration_mode_t
    method getMode : iteration_mode_t
    method toPretty : CHPretty.pretty_t
  end

module CFGAtlasTable :
  sig
    module C :
      sig
        module ObjectMap :
          sig
            type key = CHLanguage.symbol_t
            type +'a t
            val empty : 'a t
            val is_empty : 'a t -> bool
            val mem : key -> 'a t -> bool
            val add : key -> 'a -> 'a t -> 'a t
            val singleton : key -> 'a -> 'a t
            val remove : key -> 'a t -> 'a t
            val merge :
              (key -> 'a option -> 'b option -> 'c option) ->
              'a t -> 'b t -> 'c t
            val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
            val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
            val iter : (key -> 'a -> unit) -> 'a t -> unit
            val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
            val for_all : (key -> 'a -> bool) -> 'a t -> bool
            val exists : (key -> 'a -> bool) -> 'a t -> bool
            val filter : (key -> 'a -> bool) -> 'a t -> 'a t
            val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
            val cardinal : 'a t -> int
            val bindings : 'a t -> (key * 'a) list
            val min_binding : 'a t -> key * 'a
            val max_binding : 'a t -> key * 'a
            val choose : 'a t -> key * 'a
            val split : key -> 'a t -> 'a t * 'a option * 'a t
            val find : key -> 'a t -> 'a
            val map : ('a -> 'b) -> 'a t -> 'b t
            val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
          end
        module ObjectSet :
          sig
            type elt = CHLanguage.symbol_t
            type t
            val empty : t
            val is_empty : t -> bool
            val mem : elt -> t -> bool
            val add : elt -> t -> t
            val singleton : elt -> t
            val remove : elt -> t -> t
            val union : t -> t -> t
            val inter : t -> t -> t
            val diff : t -> t -> t
            val compare : t -> t -> int
            val equal : t -> t -> bool
            val subset : t -> t -> bool
            val iter : (elt -> unit) -> t -> unit
            val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
            val for_all : (elt -> bool) -> t -> bool
            val exists : (elt -> bool) -> t -> bool
            val filter : (elt -> bool) -> t -> t
            val partition : (elt -> bool) -> t -> t * t
            val cardinal : t -> int
            val elements : t -> elt list
            val min_elt : t -> elt
            val max_elt : t -> elt
            val choose : t -> elt
            val split : elt -> t -> t * bool * t
          end
        class set_t :
          object ('a)
            val mutable count : int
            val mutable objectSet : ObjectSet.t
            method add : ObjectSet.elt -> unit
	    method choose: ObjectSet.elt option
            method addList : ObjectSet.elt list -> unit
            method addSet : 'a -> unit
            method clone : 'a
            method diff : 'a -> 'a
            method equal : 'a -> bool
            method filter : (ObjectSet.elt -> bool) -> 'a
            method fold : ('b -> ObjectSet.elt -> 'b) -> 'b -> 'b
            method has : ObjectSet.elt -> bool
            method inter : 'a -> 'a
            method isEmpty : bool
            method iter : (ObjectSet.elt -> unit) -> unit
            method private mkNew : 'a
            method remove : ObjectSet.elt -> unit
            method removeList : ObjectSet.elt list -> unit
            method singleton : ObjectSet.elt option
            method size : int
            method subset : 'a -> bool
            method toList : ObjectSet.elt list
            method toPretty : CHPretty.pretty_t
            method union : 'a -> 'a
          end
        class ['a] simple_table_t :
          object ('b)
            val mutable count : int
            val mutable table : 'a ObjectMap.t
            method clone : 'b
            method fold : ('c -> ObjectMap.key -> 'a -> 'c) -> 'c -> 'c
            method get : ObjectMap.key -> 'a option
            method has : ObjectMap.key -> bool
            method iter : (ObjectMap.key -> 'a -> unit) -> unit
            method keys : set_t
            method listOfKeys : ObjectSet.elt list
            method listOfPairs : (ObjectMap.key * 'a) list
            method listOfValues : 'a list
            method map : ('a -> 'a) -> 'b
            method mapi : (ObjectMap.key -> 'a -> 'a) -> 'b
            method private mkNew : 'b
            method remove : ObjectMap.key -> unit
            method removeList : ObjectMap.key list -> unit
            method set : ObjectMap.key -> 'a -> unit
            method setOfKeys : set_t
            method size : int
          end
        class ['a] table_t :
          object ('b)
            constraint 'a = < toPretty : CHPretty.pretty_t; .. >
            val mutable count : int
            val mutable table : 'a ObjectMap.t
            method clone : 'b
            method fold : ('c -> ObjectMap.key -> 'a -> 'c) -> 'c -> 'c
            method get : ObjectMap.key -> 'a option
            method has : ObjectMap.key -> bool
            method iter : (ObjectMap.key -> 'a -> unit) -> unit
            method keys : set_t
            method listOfKeys : ObjectSet.elt list
            method listOfPairs : (ObjectMap.key * 'a) list
            method listOfValues : 'a list
            method map : ('a -> 'a) -> 'b
            method mapi : (ObjectMap.key -> 'a -> 'a) -> 'b
            method private mkNew : 'b
            method remove : ObjectMap.key -> unit
            method removeList : ObjectMap.key list -> unit
            method set : ObjectMap.key -> 'a -> unit
            method setOfKeys : set_t
            method size : int
            method toPretty : CHPretty.pretty_t
          end
        val set_of_list : ObjectSet.elt list -> set_t
      end
    class atlas_table_t :
      object
        val table : CHAtlas.atlas_t C.table_t
        method add : C.ObjectMap.key -> CHAtlas.atlas_t -> unit
        method get : C.ObjectMap.key -> CHAtlas.atlas_t option
        method toPretty : CHPretty.pretty_t
      end
  end

module FwdBwdTable :
  sig
    module ObjectMap :
      sig
        type key = int * int
        type +'a t
        val empty : 'a t
        val is_empty : 'a t -> bool
        val mem : key -> 'a t -> bool
        val add : key -> 'a -> 'a t -> 'a t
        val singleton : key -> 'a -> 'a t
        val remove : key -> 'a t -> 'a t
        val merge :
          (key -> 'a option -> 'b option -> 'c option) ->
          'a t -> 'b t -> 'c t
        val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
        val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
        val iter : (key -> 'a -> unit) -> 'a t -> unit
        val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
        val for_all : (key -> 'a -> bool) -> 'a t -> bool
        val exists : (key -> 'a -> bool) -> 'a t -> bool
        val filter : (key -> 'a -> bool) -> 'a t -> 'a t
        val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
        val cardinal : 'a t -> int
        val bindings : 'a t -> (key * 'a) list
        val min_binding : 'a t -> key * 'a
        val max_binding : 'a t -> key * 'a
        val choose : 'a t -> key * 'a
        val split : key -> 'a t -> 'a t * 'a option * 'a t
        val find : key -> 'a t -> 'a
        val map : ('a -> 'b) -> 'a t -> 'b t
        val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
      end
    module ObjectSet :
      sig
        type elt = int * int
        type t
        val empty : t
        val is_empty : t -> bool
        val mem : elt -> t -> bool
        val add : elt -> t -> t
        val singleton : elt -> t
        val remove : elt -> t -> t
        val union : t -> t -> t
        val inter : t -> t -> t
        val diff : t -> t -> t
        val compare : t -> t -> int
        val equal : t -> t -> bool
        val subset : t -> t -> bool
        val iter : (elt -> unit) -> t -> unit
        val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
        val for_all : (elt -> bool) -> t -> bool
        val exists : (elt -> bool) -> t -> bool
        val filter : (elt -> bool) -> t -> t
        val partition : (elt -> bool) -> t -> t * t
        val cardinal : t -> int
        val elements : t -> elt list
        val min_elt : t -> elt
        val max_elt : t -> elt
        val choose : t -> elt
        val split : elt -> t -> t * bool * t
      end
    class set_t :
      object ('a)
        val mutable count : int
        val mutable objectSet : ObjectSet.t
        method add : ObjectSet.elt -> unit
	method choose: ObjectSet.elt option
        method addList : ObjectSet.elt list -> unit
        method addSet : 'a -> unit
        method clone : 'a
        method diff : 'a -> 'a
        method equal : 'a -> bool
        method filter : (ObjectSet.elt -> bool) -> 'a
        method fold : ('b -> ObjectSet.elt -> 'b) -> 'b -> 'b
        method has : ObjectSet.elt -> bool
        method inter : 'a -> 'a
        method isEmpty : bool
        method iter : (ObjectSet.elt -> unit) -> unit
        method private mkNew : 'a
        method remove : ObjectSet.elt -> unit
        method removeList : ObjectSet.elt list -> unit
        method singleton : ObjectSet.elt option
        method size : int
        method subset : 'a -> bool
        method toList : ObjectSet.elt list
        method toPretty : CHPretty.pretty_t
        method union : 'a -> 'a
      end
    class ['a] simple_table_t :
      object ('b)
        val mutable count : int
        val mutable table : 'a ObjectMap.t
        method clone : 'b
        method fold : ('c -> ObjectMap.key -> 'a -> 'c) -> 'c -> 'c
        method get : ObjectMap.key -> 'a option
        method has : ObjectMap.key -> bool
        method iter : (ObjectMap.key -> 'a -> unit) -> unit
        method keys : set_t
        method listOfKeys : ObjectSet.elt list
        method listOfPairs : (ObjectMap.key * 'a) list
        method listOfValues : 'a list
        method map : ('a -> 'a) -> 'b
        method mapi : (ObjectMap.key -> 'a -> 'a) -> 'b
        method private mkNew : 'b
        method remove : ObjectMap.key -> unit
        method removeList : ObjectMap.key list -> unit
        method set : ObjectMap.key -> 'a -> unit
        method setOfKeys : set_t
        method size : int
      end
    class ['a] table_t :
      object ('b)
        constraint 'a = < toPretty : CHPretty.pretty_t; .. >
        val mutable count : int
        val mutable table : 'a ObjectMap.t
        method clone : 'b
        method fold : ('c -> ObjectMap.key -> 'a -> 'c) -> 'c -> 'c
        method get : ObjectMap.key -> 'a option
        method has : ObjectMap.key -> bool
        method iter : (ObjectMap.key -> 'a -> unit) -> unit
        method keys : set_t
        method listOfKeys : ObjectSet.elt list
        method listOfPairs : (ObjectMap.key * 'a) list
        method listOfValues : 'a list
        method map : ('a -> 'a) -> 'b
        method mapi : (ObjectMap.key -> 'a -> 'a) -> 'b
        method private mkNew : 'b
        method remove : ObjectMap.key -> unit
        method removeList : ObjectMap.key list -> unit
        method set : ObjectMap.key -> 'a -> unit
        method setOfKeys : set_t
        method size : int
        method toPretty : CHPretty.pretty_t
      end
    val set_of_list : ObjectSet.elt list -> set_t
  end

class fwd_graph_t :
  CHLanguage.cfg_int ->
  object
    val graph : CHLanguage.cfg_int
    method getNextNodes : CHLanguage.symbol_t -> CHLanguage.symbol_t list
    method getRootNode : CHLanguage.symbol_t
  end

class bwd_graph_t :
  CHLanguage.cfg_int ->
  object
    val graph : CHLanguage.cfg_int
    method getNextNodes : CHLanguage.symbol_t -> CHLanguage.symbol_t list
    method getRootNode : CHLanguage.symbol_t
  end

class loop_counter_factory_t :
  object
    val mutable count : int
    method mkCounter : CHLanguage.variable_t
    method mkSCCCounter : CHLanguage.symbol_t -> CHLanguage.variable_t
    method mkSCCCounterName : CHLanguage.symbol_t -> CHLanguage.symbol_t
    method reset : unit
  end

class iterator_t :
  ?db_enabled : bool ->
  ?strategy : iteration_strategy_t ->
  ?do_narrowing : bool ->
  ?do_loop_counters : bool ->
  ?op_semantics : op_semantics_t ->
  ?cmd_processor : cmd_processor_t ->
  ?proc_semantics : proc_semantics_t ->
  CHLanguage.system_int ->
  object
    val cmd_processor : cmd_processor_t option
    val do_loop_counters : bool
    val do_narrowing : bool
    val goto_table_stack : CFGAtlasTable.atlas_table_t CHStack.stack_t
    val iteration_stack : iteration_mode_t CHStack.stack_t
    val loop_counter_factory : loop_counter_factory_t
    val op_semantics : op_semantics_t option
    val proc_semantics : proc_semantics_t option
    val strategy : iteration_strategy_t
    val system : CHLanguage.system_int
    method private activeDomains :
      CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      CHUtils.StringCollections.set_t
    method private analyzeBwd :
      in_transaction : bool ->
      must_terminate : bool ->
      iterate_on_transactions : bool ->
      iterate_on_relations : bool ->
      fwd_bwd : CHAtlas.atlas_t FwdBwdTable.simple_table_t option ->
      modified : CHUtils.VariableCollections.set_t ->
      context : CHLanguage.symbol_t CHStack.stack_t ->
      domains : CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      post : CHAtlas.atlas_t ->
      cmd : (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
      CHAtlas.atlas_t
    method private analyzeBwd_FwdBwd :
      in_transaction : bool ->
      iterate_on_transactions : bool ->
      iterate_on_relations : bool ->
      modified : CHUtils.VariableCollections.set_t ->
      context : CHLanguage.symbol_t CHStack.stack_t ->
      domains : CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      post : CHAtlas.atlas_t -> code:CHLanguage.code_int -> CHAtlas.atlas_t
    method private analyzeCFG :
      must_terminate : bool ->
      iterate_on_transactions : bool ->
      iterate_on_relations : bool ->
      fwd_bwd : CHAtlas.atlas_t FwdBwdTable.simple_table_t option ->
      modified : CHUtils.VariableCollections.set_t ->
      context : CHLanguage.symbol_t CHStack.stack_t ->
      domains : CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      inv_table : CHAtlas.atlas_t CHUtils.SymbolCollections.table_t ->
      loop_counter_table : CHLanguage.variable_t
                           CHUtils.SymbolCollections.table_t ->
      cfg : CHLanguage.cfg_int ->
      wto : CHSCC.wto_component_t list ->
      fwd : bool ->
      graph : bwd_graph_t ->
      loop_stack_table : CHSCC.loop_stack_t CHUtils.SymbolCollections.table_t ->
      loop_mode_table : boxed_mode_t CHUtils.SymbolCollections.table_t -> unit
    method private analyzeCFGBwd :
      must_terminate : bool ->
      iterate_on_transactions : bool ->
      iterate_on_relations : bool ->
      fwd_bwd : CHAtlas.atlas_t FwdBwdTable.simple_table_t option ->
      modified : CHUtils.VariableCollections.set_t ->
      context : CHLanguage.symbol_t CHStack.stack_t ->
      domains : CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      post : CHAtlas.atlas_t -> cfg:CHLanguage.cfg_int -> CHAtlas.atlas_t
    method private analyzeCFGFwd :
      iterate_on_transactions : bool ->
      iterate_on_relations : bool ->
      fwd_bwd : CHAtlas.atlas_t FwdBwdTable.simple_table_t option ->
      modified : CHUtils.VariableCollections.set_t ->
      context : CHLanguage.symbol_t CHStack.stack_t ->
      domains : CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      pre : CHAtlas.atlas_t -> cfg:CHLanguage.cfg_int -> CHAtlas.atlas_t
    method private analyzeFwd :
      in_transaction : bool ->
      iterate_on_transactions : bool ->
      iterate_on_relations : bool ->
      fwd_bwd : CHAtlas.atlas_t FwdBwdTable.simple_table_t option ->
      modified : CHUtils.VariableCollections.set_t ->
      context : CHLanguage.symbol_t CHStack.stack_t ->
      domains : CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      pre : CHAtlas.atlas_t ->
      cmd : (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
      CHAtlas.atlas_t
    method private analyzeFwd_FwdBwd :
      in_transaction : bool ->
      iterate_on_transactions : bool ->
      iterate_on_relations : bool ->
      modified : CHUtils.VariableCollections.set_t ->
      context : CHLanguage.symbol_t CHStack.stack_t ->
      domains : CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      pre : CHAtlas.atlas_t -> code:CHLanguage.code_int -> CHAtlas.atlas_t
    method private getInv :
      CHAtlas.atlas_t CHUtils.SymbolCollections.table_t ->
      CHLanguage.symbol_t -> CHAtlas.atlas_t
    method private propagateInv :
      CHAtlas.atlas_t FwdBwdTable.simple_table_t option ->
      bool ->
      bool ->
      CHUtils.VariableCollections.set_t ->
      CHLanguage.symbol_t CHStack.stack_t ->
      CHUtils.StringCollections.ObjectMap.key list CHStack.stack_t ->
      CHSCC.loop_stack_t CHUtils.SymbolCollections.table_t ->
      boxed_mode_t CHUtils.SymbolCollections.table_t ->
      CHAtlas.atlas_t CHUtils.SymbolCollections.table_t ->
      CHLanguage.variable_t CHUtils.SymbolCollections.table_t ->
      CHLanguage.symbol_t -> CHLanguage.symbol_t -> CHAtlas.atlas_t -> unit
    method runBwd :
      ?must_terminate : bool ->
      ?iterate_on_transactions : bool ->
      ?iterate_on_relations : bool ->
      ?domains : CHUtils.StringCollections.ObjectMap.key list ->
      atlas : CHAtlas.atlas_t ->
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
      CHAtlas.atlas_t
    method runFwd :
      ?iterate_on_transactions : bool ->
      ?iterate_on_relations : bool ->
      ?domains : CHUtils.StringCollections.ObjectMap.key list ->
      atlas : CHAtlas.atlas_t ->
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
      CHAtlas.atlas_t
    method runFwdBwd :
      ?domains : CHUtils.StringCollections.ObjectMap.key list ->
      pre : CHAtlas.atlas_t ->
      post : CHAtlas.atlas_t ->
      (CHLanguage.code_int, CHLanguage.cfg_int) CHLanguage.command_t ->
      CHAtlas.atlas_t * CHAtlas.atlas_t
    method private stable : bool
  end

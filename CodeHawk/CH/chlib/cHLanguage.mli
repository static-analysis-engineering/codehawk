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

val tab : int

class internal_symbol_t :
  string list ->
  int ->
  string ->
  object ('a)
    val base : string
    val attributes : string array
    val seq_number : int
    method hash : int
    method compare : 'a -> int
    method equal : 'a -> bool
    method getAttributes : string list
    method getBaseName : string
    method getSeqNumber : int
    method getSymbol : string list
    method private lexComp : string list -> string list -> int
    method toPretty : CHPretty.pretty_t
  end

class symbol_t :
  ?atts:string list ->
  ?seqnr:int ->
  string ->
  object ('a)
    val index : int
    val internal_symbol : internal_symbol_t
    method compare : 'a -> int
    method equal : 'a -> bool
    method getAttributes : string list
    method getBaseName : string
    method getIndex : int
    method getSeqNumber : int
    method getSymbol : string list
    method toPretty : CHPretty.pretty_t
  end

type nr_table_entry_kind_t = NUMERICAL_ENTRY | SYMBOLIC_ENTRY

val nr_table_entry_kind_to_pretty :
  nr_table_entry_kind_t -> CHPretty.pretty_t

type nr_table_index_t = PRIMARY_INDEX | SECONDARY_INDEX | NO_INDEX

val nr_table_index_to_pretty : nr_table_index_t -> CHPretty.pretty_t

type nr_table_signature_t =
    (string * (nr_table_entry_kind_t * nr_table_index_t)) list

val nr_table_signature_to_pretty :
  (string * (nr_table_entry_kind_t * nr_table_index_t)) list ->
  CHPretty.pretty_t

val signature_included :
  ('a * ('b * 'c)) list -> ('a * ('b * 'c)) list -> bool

type variable_type_t =
  | NUM_LOOP_COUNTER_TYPE
  | NUM_TMP_VAR_TYPE
  | SYM_TMP_VAR_TYPE
  | NUM_TMP_ARRAY_TYPE
  | SYM_TMP_ARRAY_TYPE
  | NUM_VAR_TYPE
  | SYM_VAR_TYPE
  | NUM_ARRAY_TYPE
  | SYM_ARRAY_TYPE
  | STRUCT_TYPE of (symbol_t * variable_type_t) list
  | NR_TABLE_TYPE of nr_table_signature_t

val variable_type_to_pretty : variable_type_t -> CHPretty.pretty_t

val is_base_type : variable_type_t -> bool

val is_numerical_type : variable_type_t -> bool

val is_symbolic_type : variable_type_t -> bool

val is_array_type : variable_type_t -> bool

val is_table_type : variable_type_t -> bool

val is_struct_type : variable_type_t -> bool

val is_temporary_type : variable_type_t -> bool

val compatible_table_types : variable_type_t -> variable_type_t -> bool

val compatible_struct_types : variable_type_t -> variable_type_t -> bool

val compatible_types : variable_type_t -> variable_type_t -> bool

val compare_types : variable_type_t -> variable_type_t -> int

class internal_variable_t :
  symbol_t ->
  int ->
  bool ->
  symbol_t list ->
  variable_type_t ->
  object ('a)
    val isRegister : bool
    val name : symbol_t
    val path : symbol_t array
    val suffix : int
    val vtype : variable_type_t
    method hash: int
    method compare : 'a -> int
    method private compare_paths : symbol_t list -> symbol_t list -> int
    method equal : 'a -> bool
    method private equal_paths : symbol_t list -> symbol_t list -> bool
    method field : symbol_t -> 'a
    method fields : symbol_t list -> 'a
    method getAllComponents : symbol_t list list
    method getName : symbol_t
    method getPath : symbol_t list
    method getSuffix : int
    method getType : variable_type_t
    method isArray : bool
    method isAtomic : bool
    method isNumerical : bool
    method isRegister : bool
    method isStruct : bool
    method isSymbolic : bool
    method isTable : bool
    method isTemporary : bool
    method isTmp : bool
    method marshalToSymbol : symbol_t
    method toPretty : CHPretty.pretty_t
    method transformType : variable_type_t -> 'a
  end

class variable_t :
  symbol_t ->
  ?suffix:int ->
  ?register:bool ->
  ?path:symbol_t list ->
  variable_type_t ->
  object ('a)
    val index : int
    val internal_variable: internal_variable_t
    method compare : 'a -> int
    method equal : 'a -> bool
    method field : symbol_t -> 'a
    method fields : symbol_t list -> 'a
    method getAllComponents : symbol_t list list
    method getIndex : int
    method getName : symbol_t
    method getPath : symbol_t list
    method getSuffix : int
    method getType : variable_type_t
    method isArray : bool
    method isAtomic : bool
    method isNumerical : bool
    method isRegister : bool
    method isStruct : bool
    method isSymbolic : bool
    method isTable : bool
    method isTemporary : bool
    method isTmp : bool
    method marshalToSymbol : symbol_t
    method toPretty : CHPretty.pretty_t
    method transformType : variable_type_t -> 'a
  end

val unmarshalVariable : symbol_t -> variable_t

type arg_mode_t = READ | WRITE | READ_WRITE

type op_arg_t = string * variable_t * arg_mode_t
              
type operation_t = {
    op_name : symbol_t;
    op_args : (string * variable_t * arg_mode_t) list;
  }

type op_processor_t =
  renaming:(variable_t -> variable_t) ->
  context:symbol_t list -> operation:operation_t -> operation_t
  
type domain_cmd_arg_t =
  | NUM_DOM_ARG of CHNumerical.numerical_t
  | VAR_DOM_ARG of variable_t
                 
type symbolic_exp_t = SYM of symbol_t | SYM_VAR of variable_t

type numerical_exp_t =
  | NUM of CHNumerical.numerical_t
  | NUM_VAR of variable_t
  | PLUS of variable_t * variable_t
  | MINUS of variable_t * variable_t
  | MULT of variable_t * variable_t
  | DIV of variable_t * variable_t
         
type boolean_exp_t =
  | RANDOM
  | TRUE
  | FALSE
  | LEQ of variable_t * variable_t
  | GEQ of variable_t * variable_t
  | LT of variable_t * variable_t
  | GT of variable_t * variable_t
  | EQ of variable_t * variable_t
  | NEQ of variable_t * variable_t
  | SUBSET of variable_t * symbol_t list
  | DISJOINT of variable_t * symbol_t list

type select_args_t = {
    selected : (string * variable_t) list;
    from : variable_t;
    where : (string * variable_t) list;
  }

type insert_args_t = {
    into : variable_t;
    values : (string * variable_t) list;
  }

type delete_args_t = {
    rows_from : variable_t;
    rows_where : (string * variable_t) list;
  }

type ('a, 'b) command_t =
  | CODE of symbol_t * 'a
  | CFG of symbol_t * 'b
  | RELATION of 'a
  | TRANSACTION of symbol_t * 'a * 'a option
  | BREAKOUT_BLOCK of symbol_t * 'a
  | BREAK of symbol_t
  | GOTO_BLOCK of 'a
  | LABEL of symbol_t
  | GOTO of symbol_t
  | SKIP
  | ABSTRACT_VARS of variable_t list
  | ASSIGN_NUM of variable_t * numerical_exp_t
  | INCREMENT of variable_t * CHNumerical.numerical_t
  | ASSIGN_SYM of variable_t * symbolic_exp_t
  | ASSIGN_STRUCT of variable_t * variable_t
  | ABSTRACT_ELTS of variable_t * variable_t * variable_t
  | ASSIGN_ARRAY of variable_t * variable_t
  | ASSIGN_NUM_ELT of variable_t * variable_t * variable_t
  | ASSIGN_SYM_ELT of variable_t * variable_t * variable_t
  | READ_NUM_ELT of variable_t * variable_t * variable_t
  | READ_SYM_ELT of variable_t * variable_t * variable_t
  | SHIFT_ARRAY of variable_t * variable_t * CHNumerical.numerical_t
  | BLIT_ARRAYS of variable_t * variable_t * variable_t * variable_t *
      variable_t
  | SET_ARRAY_ELTS of variable_t * variable_t * variable_t * variable_t
  | ASSERT of boolean_exp_t
  | BRANCH of 'a list
  | LOOP of 'a * 'a * 'a
  | OPERATION of operation_t
  | DOMAIN_OPERATION of string list * operation_t
  | CALL of symbol_t * (symbol_t * variable_t) list
  | CONTEXT of symbol_t * 'a
  | DOMAINS of string list * 'a
  | DOMAIN_CMD of string * string * domain_cmd_arg_t list
  | MOVE_VALUES of variable_t list * string * string
  | MOVE_RELATIONS of variable_t list * string * string
  | SELECT of select_args_t
  | INSERT of insert_args_t
  | DELETE of delete_args_t
  | ASSIGN_TABLE of variable_t * variable_t

class type code_int =
  object ('a)
    method getId : int
    method clone :
             ?context:symbol_t list ->
             ?renaming:(variable_t -> variable_t) ->
             ?op_proc:op_processor_t -> unit -> 'a
    method getCmdAt : int -> (code_int, cfg_int) command_t
    method length : int
    method removeSkips : unit
    method setCmdAt : int -> (code_int, cfg_int) command_t -> unit
    method toPretty : CHPretty.pretty_t
  end
      and state_int =
        object ('a)
          method addIncomingEdge : symbol_t -> unit
          method addOutgoingEdge : symbol_t -> unit
          method clone :
                   ?context:symbol_t list ->
                   ?renaming:(variable_t -> variable_t) ->
                   ?op_proc:op_processor_t -> unit -> 'a
          method getCode : code_int
          method getIncomingEdges : symbol_t list
          method getLabel : symbol_t
          method getOutgoingEdges : symbol_t list
          method toPretty : CHPretty.pretty_t
        end
      and cfg_int =
        object ('a)
          method getId : int
          method addEdge : symbol_t -> symbol_t -> unit
          method addState : state_int -> unit
          method addStates : state_int list -> unit
          method clone :
                   ?context:symbol_t list ->
                   ?renaming:(variable_t -> variable_t) ->
                   ?op_proc:op_processor_t -> unit -> 'a
          method getEntry : state_int
          method getExit : state_int
          method getState : symbol_t -> state_int
          method getStates : symbol_t list
          method getStatesFrom : symbol_t -> symbol_t list
          method toPretty : CHPretty.pretty_t
        end
        
class type scope_int =
  object ('a)
    method addVariable : variable_t -> unit
    method addVariables : variable_t list -> unit
    method endTransaction : unit
    method getTmpBase: string
    method getRegisterBase: string
    method getNumTmpArrays : variable_t list
    method getNumTmpVariables : variable_t list
    method getSymTmpArrays : variable_t list
    method getSymTmpVariables : variable_t list
    method getVariables : variable_t list
    method mergeWith : 'a -> variable_t -> variable_t
    method mkRegister : variable_type_t -> variable_t
    method mkVariable : symbol_t -> variable_type_t -> variable_t
    method removeVariable : variable_t -> unit
    method removeVariables : variable_t list -> unit
    method requestNumTmpArray : variable_t
    method requestNumTmpVariable : variable_t
    method requestSymTmpArray : variable_t
    method requestSymTmpVariable : variable_t
    method startTransaction : unit
    method toPretty : CHPretty.pretty_t
    method transformVariables : (variable_t -> variable_t) -> unit
  end

type signature_t = (symbol_t * variable_type_t * arg_mode_t) list

type bindings_t = (symbol_t * variable_t) list

class type procedure_int =
  object
    method getBindings : bindings_t
    method getBody : code_int
    method getName : symbol_t
    method getScope : scope_int
    method getSignature : signature_t
    method setBody : code_int -> unit
    method toPretty : CHPretty.pretty_t
  end

class type system_int =
  object
    method addProcedure : procedure_int -> unit
    method getName : symbol_t
    method getProcedure : symbol_t -> procedure_int
    method getProcedures : symbol_t list
    method hasProcedure : symbol_t -> bool
    method toPretty : CHPretty.pretty_t
  end

module type LANGUAGE_FACTORY =
  sig
    val mkCode : (code_int, cfg_int) command_t list -> code_int
    val mkState : symbol_t -> code_int -> state_int
    val mkCFG : state_int -> state_int -> cfg_int
    val mkCFG_s : symbol_t -> symbol_t -> cfg_int
    val mkScope :
      ?tmp_base:string -> ?register_base:string -> unit -> scope_int
    val mkProcedure :
      symbol_t ->
      signature:signature_t ->
      bindings:bindings_t ->
      scope:scope_int -> body:code_int -> procedure_int
    val mkSystem : symbol_t -> system_int
  end

val numerical_exp_to_pretty : numerical_exp_t -> CHPretty.pretty_t

val symbolic_exp_to_pretty : symbolic_exp_t -> CHPretty.pretty_t

val bool_exp_to_pretty : boolean_exp_t -> CHPretty.pretty_t

val arg_mode_to_pretty : arg_mode_t -> CHPretty.pretty_t

val signature_to_pretty :
  (< toPretty : CHPretty.pretty_t; .. > * variable_type_t * arg_mode_t) list ->
  CHPretty.pretty_t

val bindings_to_pretty :
  (< toPretty : CHPretty.pretty_t; .. > *
   < toPretty : CHPretty.pretty_t; .. >)
  list -> CHPretty.pretty_t

val command_to_pretty : int -> (code_int, cfg_int) command_t -> CHPretty.pretty_t

class code_walker_t :
  object
    method walkBoolExp : boolean_exp_t -> unit
    method walkCmd : (code_int, cfg_int) command_t -> unit
    method walkCode : code_int -> unit
    method walkNumExp : numerical_exp_t -> unit
    method walkSymExp : symbolic_exp_t -> unit
    method walkVar : variable_t -> unit
  end

class code_transformer_t :
  object
    method transformCmd :
      (code_int, cfg_int) command_t -> (code_int, cfg_int) command_t
    method transformCode : code_int -> unit
  end

val negate_bool_exp : boolean_exp_t -> boolean_exp_t

val modified_vars_in_cmd_fwd : ('a, 'b) command_t -> variable_t list

module VariableCollections' :
  sig
    module ObjectMap :
      sig
        type key = variable_t
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
        type elt = variable_t
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

class var_collector_t :
  object
    val vars : VariableCollections'.set_t
    method getVars : VariableCollections'.ObjectSet.elt list
    method walkBoolExp : boolean_exp_t -> unit
    method walkCmd : (code_int, cfg_int) command_t -> unit
    method walkCode : code_int -> unit
    method walkNumExp : numerical_exp_t -> unit
    method walkSymExp : symbolic_exp_t -> unit
    method walkVar : variable_t -> unit
  end

val vars_in_cmd :
  (code_int, cfg_int) command_t -> VariableCollections'.ObjectSet.elt list

val vars_in_code : code_int -> VariableCollections'.ObjectSet.elt list

val modified_vars_in_cmd_bwd :
  (code_int, cfg_int) command_t -> variable_t list

class tmp_collector_t :
  object
    val vars : VariableCollections'.set_t
    method getVars : VariableCollections'.ObjectSet.elt list
    method walkBoolExp : boolean_exp_t -> unit
    method walkCmd : (code_int, cfg_int) command_t -> unit
    method walkCode : code_int -> unit
    method walkNumExp : numerical_exp_t -> unit
    method walkSymExp : symbolic_exp_t -> unit
    method walkVar : variable_t -> unit
  end

val tmp_vars_in_cmd :
  (code_int, cfg_int) command_t -> VariableCollections'.ObjectSet.elt list

val tmp_vars_in_code : code_int -> VariableCollections'.ObjectSet.elt list

class read_vars_collector_t :
  system_int ->
  object
    val vars : VariableCollections'.set_t
    method private add : VariableCollections'.ObjectSet.elt -> unit
    method private addl : VariableCollections'.ObjectSet.elt list -> unit
    method getVars : VariableCollections'.ObjectSet.elt list
    method walkBoolExp : boolean_exp_t -> unit
    method walkCmd : (code_int, cfg_int) command_t -> unit
    method walkCode : code_int -> unit
    method walkNumExp : numerical_exp_t -> unit
    method walkSymExp : symbolic_exp_t -> unit
    method walkVar : variable_t -> unit
  end

val read_vars_in_code :
  code_int -> system_int -> VariableCollections'.ObjectSet.elt list

val expand_structure_assignment :
  < fields : 'a -> variable_t; getAllComponents : 'a list; .. > ->
  < fields : 'a -> variable_t; .. > -> ('b, 'c) command_t list

val expand_struct_vars_in_list :
  (< fields : 'b -> 'a; getAllComponents : 'b list; isStruct : bool; .. >
   as 'a)
  list -> 'a list

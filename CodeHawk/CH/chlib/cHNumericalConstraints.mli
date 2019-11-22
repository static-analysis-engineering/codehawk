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

class numerical_factor_t :
  ?index:CHNumerical.numerical_t ->
  ?tag:string ->
  CHLanguage.variable_t ->
  object ('a)
    val index : CHNumerical.numerical_t option
    val tag : string
    val variable : CHLanguage.variable_t
    method compare : 'a -> int
    method equal : 'a -> bool
    method getIndex : CHNumerical.numerical_t option
    method getTag : string
    method getVariable : CHLanguage.variable_t
    method tag : string -> 'a
    method toPretty : CHPretty.pretty_t
  end

type numerical_constraint_kind_t = LINEAR_EQ | LINEAR_INEQ

module FactorCollections :
  sig
    module ObjectMap :
      sig
        type key = numerical_factor_t
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
        type elt = numerical_factor_t
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

class numerical_constraint_t :
  factors:(CHNumerical.numerical_t * FactorCollections.ObjectMap.key) list ->
  constant:CHNumerical.numerical_t ->
  kind:numerical_constraint_kind_t ->
  object ('a)
    val mutable constant : CHNumerical.numerical_t
    val mutable factors_table :
      CHNumerical.numerical_t FactorCollections.table_t
    val kind : numerical_constraint_kind_t
    val mutable normalized : bool
    method affineCombination :
      CHNumerical.numerical_t -> CHNumerical.numerical_t -> 'a -> 'a
    method equal : 'a -> bool
    method getCoefficient :
      FactorCollections.ObjectMap.key -> CHNumerical.numerical_t
    method getConstant : CHNumerical.numerical_t
    method getFactors : FactorCollections.ObjectMap.key list
    method getFactorsList :
      (CHNumerical.numerical_t * FactorCollections.ObjectMap.key) list
    method getFactorsTable :
      CHNumerical.numerical_t FactorCollections.table_t
    method getKind : numerical_constraint_kind_t
    method getVariables : CHUtils.VariableCollections.set_t
    method getVariablesList : CHLanguage.variable_t list
    method increment :
      FactorCollections.ObjectMap.key -> CHNumerical.numerical_t -> 'a
    method isContradiction : bool
    method isNormalized : bool
    method isTrivial : bool
    method normalize : ?pivot:numerical_factor_t -> unit -> unit
    method range : (CHLanguage.variable_t * CHIntervals.interval_t) option
    method toPretty : CHPretty.pretty_t
  end

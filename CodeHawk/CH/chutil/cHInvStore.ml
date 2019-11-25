(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
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
   ============================================================================= *)

(** Utilities to store invariants *)

(* chlib *)
open CHAtlas
open CHCommon
open CHIntervalsDomainNoArrays
open CHIterator   
open CHLanguage
open CHLinearEqualitiesDomainNoArrays   
open CHNonRelationalDomainValues
open CHNumerical
open CHNumericalConstraints   
open CHPolyhedraDomainNoArrays   
open CHPretty   
open CHUtils   

(* chutil *)
open CHInvAccess   
open CHPrettyUtil
open CHUtil
open CHXmlDocument

class type invariant_store_int =
  object
    method add_invariant : symbol_t -> atlas_t -> unit
         
    method getAddresses : CHUtils.SymbolCollections.ObjectSet.elt list
         
    method getFilteredPolyhedralConstraints :
      ?include_variable:(variable_t -> bool) ->
      ?exclude_variable:(variable_t -> bool) ->
      symbol_t ->
      numerical_constraint_t list
         
    method getInvariants :
             (CHUtils.SymbolCollections.ObjectMap.key * atlas_t) list
         
    method getNonrelationalValue :
      symbol_t ->
      string ->
      variable_t ->
      non_relational_domain_value_t
         
    method getVariables : symbol_t -> string -> variable_t list
         
    method get_invariant : symbol_t -> atlas_t
         
    method has_invariant : symbol_t -> bool
         
    method intervalToPretty : atlas_t -> pretty_t
         
    method intervalsToPretty : pretty_t
         
    method linearEqualitiesToPretty : pretty_t
         
    method linearEqualityToPretty : atlas_t -> pretty_t
         
    method reset : unit
         
    method stridedIntervalToPretty : atlas_t -> pretty_t
         
    method stridedIntervalsToPretty : pretty_t
         
    method toPretty : pretty_t
         
    method valueSetToPretty : atlas_t -> pretty_t
         
    method valueSetsToPretty : pretty_t
  end



(* Invariants are stored in a table indexed by symbol_t *)
class invariant_store_t =
object (self)

  val store = new SymbolCollections.table_t

  (* return all invariants with their identifying symbol addresses *)
  method getInvariants = store#listOfPairs

  (* return all symbol addresses for which invariants are present *)
  method getAddresses = store#listOfKeys

  (* remove all invariants *)
  method reset = 
    let addresses = store#listOfKeys in
    store#removeList addresses

  (* store an invariant for the given address *)
  method add_invariant (address:symbol_t) (invariant:atlas_t) =
    store#set address invariant

  (* retrieve the invariant for the given address; throws an exception if the
     given address is not found *)
  method get_invariant (address:symbol_t):atlas_t =
    match store#get address with
      Some inv -> inv
    | _ -> failwith ("No invariant found for address: " ^ (List.hd address#getSymbol))

  (* return true if the store contains an invariant for the given address *)
  method has_invariant (address:symbol_t):bool =
    match store#get address with Some inv -> true | _ -> false

  (* return the nonrelational value for variable var at a given address for the given domain;
     return top if there is no invariant *)
  method getNonrelationalValue (address:symbol_t) 
    (dom:string) (var:variable_t):non_relational_domain_value_t =
    if self#has_invariant address then
      let inv_accessor = mk_inv_accessor (self#get_invariant address) in
      match inv_accessor#getNonRelationalValue dom var with
	Some v -> v
      | _ -> topNonRelationalDomainValue
    else
      topNonRelationalDomainValue

  (* retrieve the polyhedral constraints possibly projected onto a restricted set of variables,
     but only return the constraints that include the variables of interest, as specified by
     the filter <include_variable>, at the given address. Return the empty list if there is no
     invariant
   *)
  method getFilteredPolyhedralConstraints 
           ?(include_variable=fun _ -> true)
           ?(exclude_variable=fun _ -> false)
           (address:symbol_t) =
    if self#has_invariant address then
      let inv_accessor = mk_inv_accessor (self#get_invariant address) in
      inv_accessor#getFilteredPolyhedralConstraints ~exclude_variable:exclude_variable
	~include_variable:include_variable ()
    else
      []
    
  (* return the list of variables that have a value in the given domain *)
  method getVariables (address:symbol_t) (dom:string):variable_t list =
    if self#has_invariant address then
      let inv = self#get_invariant address in
      let domain = inv#getDomain dom in
      domain#observer#getObservedVariables
    else
      []

  (* standard pretty output of a table *)
  method toPretty:pretty_t = store#toPretty

  (* custom pretty printing of interval invariants; in particular, omit temporary variables *)
  method intervalsToPretty:pretty_t =
    LBLOCK
      (List.map
	 (fun (s,i) -> LBLOCK [ s#toPretty ; NL ; INDENT (5, self#intervalToPretty i) ; NL ]) 
	 store#listOfPairs)

  method intervalToPretty inv =
      let domain = inv#getDomain "intervals" in
      let var_observer = domain#observer#getNonRelationalVariableObserver in
      let vars = List.filter (fun v ->
                     not v#isTmp) domain#observer#getObservedVariables in
      List.fold_right 
	(fun v a -> 
	  let i = (var_observer v)#toInterval in
	  if i#isTop then 
	    a
	  else
            match i#singleton with
	    | Some n -> LBLOCK [ v#toPretty ; STR " = " ; n#toPretty ; NL ; a ]
            | _ ->
               LBLOCK [ v#toPretty ; STR " in " ; i#toPretty ; NL ; a ])
        vars (LBLOCK [])
      
  method linearEqualitiesToPretty =
    LBLOCK
      (List.map
	 (fun (s,i) ->
           LBLOCK [ s#toPretty ; NL ;
                    INDENT (5, self#linearEqualityToPretty i) ; NL ]) 
	 store#listOfPairs)
    
  method linearEqualityToPretty inv =
    let domain = inv#getDomain "karr" in domain#toPretty
	                               
  (* custom pretty printing of strided interval invariants, in particular omit temporary variables *)
  method stridedIntervalsToPretty =
    LBLOCK
      (List.map
	 (fun (s,i) ->
           LBLOCK [ s#toPretty ; NL ; INDENT (5, self#stridedIntervalToPretty i) ; NL ]) 
	 store#listOfPairs)
    
  method stridedIntervalToPretty inv =
    let domain = inv#getDomain "strided_intervals" in
    let var_observer = domain#observer#getNonRelationalVariableObserver in
    let vars =
      List.filter (fun v ->
          not v#isTmp) domain#observer#getObservedVariables in
    List.fold_right 
      (fun v a -> 
	let i = (var_observer v) in
	if i#isTop then 
	  a
	else LBLOCK [ v#toPretty ; STR " -> " ; i#toPretty ; NL ; a ]) vars (LBLOCK [])
    
  method valueSetsToPretty =
    LBLOCK
      (List.map 
	 (fun (s,i) ->
           LBLOCK [ s#toPretty ; NL ; INDENT (5, self#valueSetToPretty i); NL])
	 store#listOfPairs)
    
  method valueSetToPretty inv = 
    if inv#isBottom then
      STR "_|_"
    else
      let domain = inv#getDomain "valuesets" in
      let var_observer = domain#observer#getNonRelationalVariableObserver in
      let vars =
        List.filter (fun v ->
            not v#isTmp) domain#observer#getObservedVariables in
      let (zero_offsets,single_base,multiple_base,mixed) =
	List.fold_left 
	  (fun (z,s,m,x) var ->
	    let vs =
              match (var_observer var)#getValue with
	      | VALUESET_VAL v -> v
	      | _ -> raise (CHFailure
                              (LBLOCK [ STR "Unexpected value in " ;
                                        (var_observer var)#toPretty ])) in
	    if vs#isTop then
	      (z,s,m,x)
	    else
	      if vs#isZeroOffset then
		((var,vs#getZeroOffset)::z,s,m,x)
	      else if vs#isSingleBase then
		(z,(var,vs#getSingleBase)::s,m,x)
	      else if vs#isMultipleBase then
		(z,s,(var,vs#getMultipleBase)::m,x)
	      else
		(z,s,m,(var,vs#getValue)::x)) ([],[],[],[]) vars in
      let zero_offset_pretty = match zero_offsets with
	| [] -> STR ""
        | _ ->
	   let rec aux l p =
	     match l with
	     | [] -> LBLOCK [ STR "globals: " ; INDENT (3, p) ]
	     | (v,i)::tl ->
                aux tl (LBLOCK [ p ; NL ; v#toPretty ; STR ": " ;
                                 i#toPretty ]) in
	   aux zero_offsets (STR "") in
      let single_base_pretty = match single_base with
	| [] -> STR ""
        | _ ->
	   let bases = remove_duplicates_f 
	                 (List.map (fun (_,(s,_)) -> s) single_base)
	                 (fun s1 s2 -> s1#equal s2) in
	   let rec aux b l p =
	     match l with
	     | [] -> LBLOCK [ b#toPretty ; INDENT (3, p) ; NL ]
	     | (v, (_,i))::tl ->
                aux b tl (LBLOCK [p ; NL ; v#toPretty ; STR ": " ; i#toPretty ]) in
	   LBLOCK
             (List.map
                (fun b ->
                  aux b (List.filter (fun (_, (s,_)) -> s#equal b)
                                     single_base) (STR "")) bases) in
      LBLOCK [ zero_offset_pretty ; NL ; single_base_pretty ]


end

let mk_invariant_store () = new invariant_store_t

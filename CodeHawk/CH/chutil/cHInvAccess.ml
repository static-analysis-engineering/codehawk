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

(** Utilities to access invariants in standard domains *)

(* chlib *)
open CHAtlas
open CHIntervals
open CHIntervalsDomainNoArrays
open CHIterator   
open CHLanguage
open CHLinearEqualitiesDomainNoArrays
open CHNonRelationalDomainValues   
open CHNumerical
open CHNumericalConstraints   
open CHPolyhedraDomainNoArrays   
open CHPretty   
open CHValueSets

(* chutil *)
open CHLogger
open CHUtil

class type inv_accessor_int = 
object

  method hasIntervals: bool
  method hasLinearEqualities: bool
  method hasPolyhedra: bool
  method hasValueSets: bool
  method hasDomain: string -> bool

  method getObservedVariables: variable_t list

  method isScalar: variable_t -> bool

  (* retrieve the different types of numerical invariants, possibly for a restricted
     set of variables, and return them in the form of numerical constraints 
   *)
  method getPolyhedralConstraints: 
      ?var_filter:(variable_t -> bool) -> unit -> numerical_constraint_t list
  method getLinearEqualityConstraints: 
      ?var_filter:(variable_t -> bool) -> unit -> numerical_constraint_t list
  method getIntervalConstraints:
      ?var_filter:(variable_t -> bool) -> unit -> numerical_constraint_t list

  (* retrieve the different types of numerical invariants, possibly for a restricted
     set of variables, but only return the constraints that include variables of
     interest, as specified by the include_variable function.
   *)
  method getFilteredPolyhedralConstraints:
      ?include_variable:(variable_t -> bool) -> 
	?exclude_variable:(variable_t -> bool) -> unit -> numerical_constraint_t list
  method getFilteredEqualityConstraints:
      ?include_variable:(variable_t -> bool) -> 
	?exclude_variable:(variable_t -> bool) -> unit -> numerical_constraint_t list
  method getFilteredIntervalConstraints:
      ?include_variable:(variable_t -> bool) ->
	?exclude_variable:(variable_t -> bool) -> unit -> numerical_constraint_t list
  method getEqualVariables: ?var_filter:(variable_t -> bool) -> variable_t -> variable_t list

  method getNonRelationalValue: string -> variable_t -> non_relational_domain_value_t option
  method getConstant: variable_t -> numerical_t option
  method getRange: variable_t -> interval_t option
  method getBaseOffset: variable_t -> base_offset_t option
  method getAffineOffset: variable_t -> variable_t -> numerical_t option
  method getSomeAffineOffset: variable_t list -> variable_t -> (variable_t * numerical_t) option

end


class inv_accessor_t (inv:atlas_t):inv_accessor_int =
object (self)

  val inv = inv

  method private get_constraints var_filter domain_name = 
    let domain = inv#getDomain domain_name in
    let vars   = (domain#observer)#getObservedVariables in
    let vars   = List.filter (fun v -> not (var_filter v)) vars in
    let domain = domain#projectOut vars in
    (domain#observer)#getNumericalConstraints ~variables:None ()
    
  method hasDomain name = List.mem name inv#getDomains
                        
  method hasIntervals = self#hasDomain "intervals"
  method hasLinearEqualities = self#hasDomain "karr"
  method hasPolyhedra = self#hasDomain "polyhedra"
  method hasValueSets = self#hasDomain "valuesets"
                      
  method getObservedVariables =
    let domains = inv#getDomains in
    let vars =
      List.fold_left 
	(fun acc domain -> (inv#getDomain domain)#observer#getObservedVariables @ acc) 
	[] domains in
    remove_duplicates_f vars (fun v1 v2 -> v1#equal v2)

  (* retrieve the different types of numerical invariants, possibly for a restricted
     set of variables, and return them in the form of numerical constraints 
   *)
  method getPolyhedralConstraints ?(var_filter = fun v -> true) () =
    self#get_constraints var_filter "polyhedra"
    
  method getLinearEqualityConstraints ?(var_filter = fun v -> true) () =
    self#get_constraints var_filter "karr"
    
  method getIntervalConstraints ?(var_filter = fun v -> true) () =
    self#get_constraints var_filter "intervals"
    
  method private getAffines var_filter (v:variable_t):(variable_t * numerical_t) list =
    let extract_affine factor offset cst =
      let is_one c = c#equal numerical_one in
      let is_negone c = c#equal numerical_one#neg in
      let is_f f = f#equal factor in
      match cst#getFactorsList with
	[ (c1,f1) ; (c2,f2) ] when is_f f1 && is_one c1 && is_negone c2 -> [(f2,offset#add cst#getConstant)]
      | [ (c1,f1) ; (c2,f2) ] when is_f f2 && is_one c2 && is_negone c1 -> [(f1,offset#add cst#getConstant)]
      | [ (c1,f1) ; (c2,f2) ] when is_f f1 && is_negone c1 && is_one c2 -> [(f2,offset#sub cst#getConstant)]
      | [ (c1,f1) ; (c2,f2) ] when is_f f2 && is_negone c2 && is_one c1 -> [(f1,offset#sub cst#getConstant)]
      | _ -> [] in
    let extract_affines factor offset constraints =
      List.fold_left (fun a c -> (extract_affine factor offset c) @ a) [] constraints in
    let rec affines wl ncs aff =
      match (wl,ncs) with
      | ([], _)
        | (_, []) -> aff
      | ((factor,offset)::tl, _) ->
	 let (includesf,excludesf) =
           list_split_p
	     (fun c -> List.exists (fun f -> f#equal factor) c#getFactors) ncs in
	 let nwl = extract_affines factor offset includesf in
	 affines (tl @ nwl) excludesf (aff @ nwl) in
    let constraints = self#getLinearEqualityConstraints () in
    let constraints = List.filter (fun c -> (List.length c#getFactors) = 2) constraints in
    let factors = List.concat (List.map (fun c -> c#getFactors) constraints) in
    let vfactor = 
      try
	Some (List.find (fun f -> f#getVariable#equal v) factors)
      with
	Not_found -> None in
    match vfactor with
    | Some vf -> 
       let affs = affines [ (vf, numerical_zero) ] constraints [] in
       let affs = List.filter (fun (f,_) -> (var_filter f#getVariable)) affs in
      List.map (fun (f,n) -> (f#getVariable, n)) affs
    | _ -> []
         
  method getEqualVariables ?(var_filter = fun v -> true) (base:variable_t):(variable_t list) =
    let affines = self#getAffines var_filter base in
    List.map (fun (v,_) -> v) (List.filter (fun (_,n) -> n#equal numerical_zero) affines)
    
  (* return a number c if the invariant implies a a linear relationship of the
     form -- off = base + c --, otherwise return None
   *)
  method getAffineOffset (base:variable_t) (off:variable_t):numerical_t option =
    let domain = inv#getDomain "karr" in
    let vars   = (domain#observer)#getObservedVariables in
    let observed_names = List.map (fun v -> v#getName#getBaseName) vars in
    if (List.mem base#getName#getBaseName observed_names)
       && (List.mem off#getName#getBaseName observed_names) then
      let filter = (fun v -> (v#equal base) || (v#equal off)) in
      let constraints = self#getLinearEqualityConstraints ~var_filter:filter ()  in
      match constraints with
	[c] ->
	begin
	  let factors = c#getFactorsList in
	  match factors with
	  | [ (c1,f1) ; (c2,f2) ] ->
	     if f1#getVariable#equal base && f2#getVariable#equal off then
	       begin
		 if (c1#equal numerical_one#neg && c2#equal numerical_one) then       (* -base + off = c *)
		   Some c#getConstant
		 else if (c1#equal numerical_one && c2#equal numerical_one#neg) then  (*  base - off = c *)
		   Some c#getConstant#neg
		 else
		   None
	       end
	     else if (f1#getVariable#equal off && f2#getVariable#equal base) then
	       if (c1#equal numerical_one#neg && c2#equal numerical_one) then       (* -off + base = c *)
		 Some c#getConstant#neg
	       else if (c1#equal numerical_one && c2#equal numerical_one#neg) then  (*  off - base = c *)
		 Some c#getConstant
	       else
		 None
	     else
	       None
	  | _ -> None
	end
      | _ -> None
    else
      None
    
  (* return a variable v and number n if the invariant implies a linear relationship
     of the form --- off = v + num --- where v is included in the basevars  *)
  method getSomeAffineOffset
           (basevars: variable_t list)
           (off:variable_t):(variable_t * numerical_t) option =
    let filter = (fun v -> List.exists (fun w -> v#equal w) basevars) in
    let affines = self#getAffines filter off in
    match affines with
    | [] -> None
    | [a] -> Some (a)
    | _ -> Some (List.hd affines) 

  (*
    List.fold_left
    (fun acc basevar ->
    match acc with
    Some _ -> acc
	| _ ->
	    match self#getAffineOffset basevar off with
	      Some num -> Some (basevar, num)
	    | _ -> None ) None basevars   *)

  (* return a number c if the invariant implies v = c, otherwise return None *)
  method getConstant (v:variable_t):numerical_t option =
    if self#hasIntervals || self#hasValueSets then
      let domain =
        if self#hasIntervals then
          inv#getDomain "intervals"
        else
          inv#getDomain "valuesets" in
      let observer = domain#observer in
      let var_observer = observer#getNonRelationalVariableObserver in
      (var_observer v)#toInterval#singleton
    else if self#hasLinearEqualities then
      let constraints = self#getLinearEqualityConstraints () in
      List.fold_left 
	(fun acc c ->
	  match acc with
	  | Some _ -> acc
	  | _ ->
	     match c#range with
	     | Some (w,interval) -> if w#equal v then interval#singleton else None
	     | _ -> None) None constraints
    else
      None

  method getRange (v:variable_t):interval_t option =
    if self#hasIntervals then
      let domain = inv#getDomain "intervals" in
      let observer = domain#observer#getNonRelationalVariableObserver in
      let interval_value = (observer v)#toInterval in
      if interval_value#isTop then
	None
      else
        match interval_value#singleton with
	| Some _ -> None
        | _ -> Some interval_value
    else
      None

(* returns true if v is known to be a scalar value, false otherwise *)
  method isScalar (v:variable_t):bool =
    match self#getRange v with 
    | Some _ -> true
    | _ ->
       if self#hasValueSets then
	 let domain = inv#getDomain "valuesets" in
	 let observer = domain#observer#getNonRelationalVariableObserver in
	 let valueset_value = (observer v)#toValueSet in
	 valueset_value#isZeroOffset
       else
	 false
      
  method getBaseOffset (v:variable_t):base_offset_t option =
    if self#hasValueSets then
      let domain = inv#getDomain "valuesets" in
      let observer = domain#observer#getNonRelationalVariableObserver in
      let valueset_value = (observer v)#toValueSet in
      if valueset_value#isSingleBase then
	Some valueset_value#getSingleBase 
      else
	None
    else
      None
    
  (* return the value of v in domain dom, if dom is present in the invariant *)
  method getNonRelationalValue
           (dom:string)
           (v:variable_t):non_relational_domain_value_t option =
    if self#hasDomain dom then
      let domain = inv#getDomain dom in
      let observer = domain#observer in
      let var_observer = observer#getNonRelationalVariableObserver in
      Some (var_observer v)
    else
      None
    
  (* retrieve the different types of numerical invariants, possibly for a restricted
     set of variables, but only return the constraints that include variables of
     interest, as specified by the include_variable function.
   *)
  method getFilteredPolyhedralConstraints
           ?(include_variable=fun _ -> true)
           ?(exclude_variable=fun _ -> false) () =
    let filter = (fun v -> not (exclude_variable v)) in
    let constraints = self#getPolyhedralConstraints ~var_filter:filter () in
    List.filter
      (fun c -> List.exists include_variable c#getVariablesList) constraints
    
  method getFilteredEqualityConstraints
           ?(include_variable=fun _ -> true)
           ?(exclude_variable=fun _ -> false) () =
    let filter = (fun v -> not (exclude_variable v)) in
    let constraints = self#getLinearEqualityConstraints ~var_filter:filter () in
    List.filter (fun c ->
        List.exists include_variable c#getVariablesList) constraints
    
  method getFilteredIntervalConstraints
           ?(include_variable=fun _ -> true)
           ?(exclude_variable=fun _ -> false) () =
    let filter = (fun v -> not (exclude_variable v)) in
    let constraints = self#getIntervalConstraints ~var_filter:filter () in
    List.filter
      (fun c -> List.exists include_variable c#getVariablesList) constraints
    
end


let mk_inv_accessor = new inv_accessor_t

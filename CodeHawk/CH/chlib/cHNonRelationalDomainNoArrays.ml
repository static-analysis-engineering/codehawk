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

(* chlib *)
open CHCommon
open CHCommunications   
open CHLanguage
open CHDomainObserver   
open CHNonRelationalDomainBase   
open CHNonRelationalDomainValues   
open CHNumericalConstraints   
open CHPretty
open CHUtils

[@@@warning "-27"]

class virtual non_relational_domain_t =
object (self: 'a)
  
  inherit ['a] domain_downlink_t
  inherit non_relational_domain_base_int

  val bottom = false
    
  val table: non_relational_domain_value_t VariableCollections.table_t =
    new VariableCollections.table_t
    
  method isRelational = false

  method isBottom = bottom
    
  method mkBottom = {< bottom = true; table = new VariableCollections.table_t >}
    
  method mkEmpty = {< bottom = false; table = new VariableCollections.table_t >}

  method private setValue
                   (t: 'v VariableCollections.table_t)
                   (x: variable_t)
                   (v: non_relational_domain_value_t) =
    if v#isTop then t#remove x else t#set x v
    
  method private getValue (v: variable_t): non_relational_domain_value_t =
    match table#get v with
    | None -> topNonRelationalDomainValue
    | Some value -> value
                  
  method getNonRelationalValue = self#getValue
                               
  method virtual private importValue:
                           non_relational_domain_value_t -> non_relational_domain_value_t    
    
  method importNumericalConstraints (csts: numerical_constraint_t list) =
    let env =
      List.fold_left (fun a cst -> 
	  match cst#range with
	  | Some (v, i) -> (v, mkIntervalValue i) :: a
	  | None -> a
	) [] csts in
    self#importNonRelationalValues ~refine:true env
    
  method importNonRelationalValues ?(refine = true) env =
    let table' = table#clone in
    let process (x, v) =
      let v' = self#importValue v in
      let previous_v = self#getValue x in
      if refine then
	let v'' = previous_v#meet v' in
	if v''#isBottom then
	  raise Found
	else
	  self#setValue table' x v''
      else
	if v'#isBottom then
	  raise Found
	else
	  self#setValue table' x v'
    in
    try
      let _ = List.iter process env in
      {< table = table' >}
    with Found -> self#mkBottom
                
	
  method equal (dom: 'a) = self#leq dom && dom#leq self
    
  method private getVarSet ?variables (dom: 'a) =
    let observer = dom#observer in
    let var_set = new VariableCollections.set_t in
    let _ = match variables with
      | Some vars ->
	 var_set#addList vars
      | None ->
         begin
	   var_set#addList table#listOfKeys;
	   var_set#addList observer#getObservedVariables
         end in
    var_set
    
  method private leq' ?variables (dom: 'a) =
    if bottom then
      true
    else if dom#isBottom then
      false
    else
      try
	let var_set = self#getVarSet ?variables dom in
	let getValue' = dom#observer#getNonRelationalVariableObserver in
	let _ =
          var_set#iter (fun v ->
	      let value = self#getValue v in
	      let value' = getValue' v in
	      if value#leq value' then () else raise Found) in
	true
      with Found -> false
                  
  method leq ?variables (dom: 'a) = self#leq' ?variables dom
                                  
  method private meet_tables ?variables (dom: 'a) =
    let var_set = self#getVarSet ?variables dom in
    let getValue' = dom#observer#getNonRelationalVariableObserver in
    let table'' = table#clone in
    let _ =
      var_set#iter (fun v -> 
	  let e'' = (self#getValue v)#meet (getValue' v) in
	  if e''#isBottom then
	    raise Found
	  else
	    self#setValue table'' v e'') in
    table''
    
  method meet ?variables (dom: 'a) =
    if bottom || dom#isBottom then
      self#mkBottom
    else
      try
	{< bottom = false; table = self#meet_tables ?variables dom >}
      with Found -> self#mkBottom
	          
  method private join_tables ?variables (dom: 'a) =
    let vars = match variables with
      | Some vars -> vars
      | None -> table#listOfKeys
    in
    let getValue' = dom#observer#getNonRelationalVariableObserver in
    let table'' = table#clone in
    let _ = List.iter (fun v ->
                self#setValue table'' v ((self#getValue v)#join (getValue' v))) vars in
    table''
    
  method join ?variables (dom: 'a) =
    if bottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      {< bottom = false; table = self#join_tables ?variables dom >}
    
  method private widening_tables ?variables (dom: 'a) =
    let vars = match variables with
      | Some vars -> vars
      | None -> table#listOfKeys in
    let getValue' = dom#observer#getNonRelationalVariableObserver in
    let table'' = table#clone in
    let _ =
      List.iter (fun v ->
          self#setValue table'' v ((self#getValue v)#widening (getValue' v))) vars in
    table''
    
  method widening ?(kind: string option) ?variables (dom: 'a) =
    if bottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      {< bottom = false; table = self#widening_tables ?variables dom >}
    
  method private narrowing_tables ?variables (dom: 'a) =
    let vars = match variables with
      | Some vars -> vars
      | None -> table#listOfKeys in
    let getValue' = dom#observer#getNonRelationalVariableObserver in
    let table'' = table#clone in
    let _ =
      List.iter (fun v -> 
	  let narrowed = (self#getValue v)#narrowing (getValue' v) in
	  if narrowed#isBottom then
	    raise Found
	  else
	    self#setValue table'' v narrowed) vars in
    table''
    
  method narrowing ?variables (dom: 'a) =
    if bottom || dom#isBottom then
      self#mkBottom
    else
      try
	{< bottom = false; table = self#narrowing_tables ?variables dom >}
      with Found -> self#mkBottom
	          
  method projectOut (l:variable_t list) = self#analyzeFwd (ABSTRACT_VARS l)
                                        
  method virtual special: string -> domain_cmd_arg_t list -> 'a
               
  method toPretty = if bottom then STR "_|_" else table#toPretty
                  
  method private observer' =
    let get_value = self#getValue in
    object
      inherit domain_observer_t
            
      method! getObservedVariables = table#listOfKeys
                                  
      method! getNonRelationalVariableObserver = get_value
    end
    
  method observer = self#observer'
                  
  method virtual private analyzeFwd': (code_int, cfg_int) command_t -> 'a
                       
  method virtual private analyzeBwd': (code_int, cfg_int) command_t -> 'a
                       
  method analyzeFwd (cmd: (code_int, cfg_int) command_t) =
    self#analyzeFwd' cmd
    
  method analyzeBwd (cmd: (code_int, cfg_int) command_t) =
    if self#isBottom then
      match cmd with
      | ASSERT e ->
	 self#mkEmpty#analyzeFwd (ASSERT (negate_bool_exp e))
      | _ ->
	 self#mkBottom
    else
      self#analyzeBwd' cmd
    
  method private abstractVariables table' (vars: variable_t list) =
    List.iter (fun v -> table'#remove v) vars
    
  method analyzeOperation
           ~(domain_name: string)
           ~(fwd_direction: bool)
           ~(operation: operation_t): 'a =
    raise (CHFailure (LBLOCK [
                          STR "Domain ";
                          STR domain_name;
                          STR " does not implement operation ";
                          operation.op_name#toPretty]))
    
end
        
        

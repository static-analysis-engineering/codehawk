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
open CHConstants   
open CHDomain
open CHDomainObserver
open CHIntervals   
open CHLanguage   
open CHMatrix
open CHNonRelationalDomainValues   
open CHNumerical
open CHNumericalConstraints   
open CHPolyhedra   
open CHPolyhedraGlobalData   
open CHPretty
open CHVector
open CHUtils


let dummy_variable = new variable_t (new symbol_t "<#dummy#>") NUM_VAR_TYPE
let dummy_factor = new numerical_factor_t dummy_variable
                 
let initializePolyhedralDomain ~max_dimensions:dims ~max_constraints:rows =
  pGD := new global_data_t dims rows
  
  
type reflected_poly_t = {
    bottom: bool;
    var2index: numerical_t VariableCollections.table_t;
    index2var: variable_t array;
    polyhedron: polyhedron_t
  }
                      
class polyhedra_domain_no_arrays_t =
object (self: 'a)
     
  inherit ['a] domain_downlink_t
        
  val mutable bottom = false
                     
  val mutable var2index: numerical_t VariableCollections.table_t =
    new VariableCollections.table_t
    
  val mutable index2var: variable_t array = Array.make 0 dummy_variable
                                          
  val mutable polyhedron: polyhedron_t = universe 0
                                       
  val max_variable_set: VariableCollections.set_t = new VariableCollections.set_t
                                                  
  val include_tmps: bool = true
                         
                         
  method isRelational = true
                      
  method mkBottom =
    {< bottom = true;
       var2index = new VariableCollections.table_t;
       index2var = Array.make 0 dummy_variable;
       polyhedron = universe 0
    >}
    
  method mkEmpty =
    {< bottom = false;
       var2index = new VariableCollections.table_t;
       index2var = Array.make 0 dummy_variable;
       polyhedron = universe 0
    >}
    
  method isBottom =
    if bottom then
      true
    else if polyhedron#is_empty then
      let _ =
	begin
	  bottom <- true;
	  var2index <- new VariableCollections.table_t;
	  index2var <- Array.make 0 dummy_variable;
	  polyhedron <- universe 0	  
	end
      in
      true
    else
      false
    
  method projectOut (l:variable_t list) = self#analyzeFwd (ABSTRACT_VARS l)
                                        
  method private reflect =
    { bottom = bottom;
      var2index = var2index;
      index2var = index2var;
      polyhedron = polyhedron
    }
    
  method private reify reflection =
    if reflection.bottom then
      self#mkBottom
    else
      {< bottom = reflection.bottom;
	 var2index = reflection.var2index;
	 index2var = reflection.index2var;
	 polyhedron = reflection.polyhedron
      >}
    
  method private empty_pol_r =
    { bottom = true;
      var2index = new VariableCollections.table_t;
      index2var = Array.make 0 dummy_variable;
      polyhedron = universe 0
    }
    
  method private reifyConstraint
                   (nc: int)
                   (v2i: numerical_t VariableCollections.table_t)
                   (cst: numerical_constraint_t) =
    let vec = new vector_t nc in
    let factors = cst#getFactorsList in
    let _ =
      begin
	vec#set 1 cst#getConstant;
	vec#set 0 (match cst#getKind with
                   | LINEAR_EQ -> numerical_zero
                   | LINEAR_INEQ -> numerical_one);
	List.iter (fun (k, f) ->
	    match v2i#get f#getVariable with
	    | Some i -> vec#set ((!pGD)#dec + i#toInt)  k#neg
	    | None -> raise (CHFailure (STR "Polyhedral domain: Inconsistency in reifyConstraint"))
	  ) factors
      end
    in
    vec
    
  method private reifyConstraints
                   (v2i: numerical_t VariableCollections.table_t)
                   (csts: numerical_constraint_t list) =
    let nc = v2i#size + (!pGD)#dec in
    let vecs = List.map (self#reifyConstraint nc v2i) csts in
    let p = Array.of_list vecs in
    let nr = Array.length p in
    let mat = new matrix_t nr 0 false in
    let _ =
      begin
	mat#set_p p;
	mat#set_nbrows nr;
	mat#set_nbcolumns nc;
	mat#set_empty (nr * nc = 0)
      end
    in
    mat
    
  method private reflectConstraint i2v (cst: vector_t) =
    let kind = if (cst#get 0)#equal numerical_zero then LINEAR_EQ else LINEAR_INEQ in
    let constant = match kind with LINEAR_EQ -> (cst#get 1)#neg | _ -> cst#get 1 in
    let factors = ref [] in
    let dec = (!pGD)#dec in
    let _ =
      for i = dec to cst#size - 1 do
	let v = i2v.(i - dec) in
	let k = cst#get i in
	factors := ((match kind with
                     | LINEAR_EQ -> k
                     | _ -> k#neg), new numerical_factor_t v) :: !factors
      done
    in
    new numerical_constraint_t ~factors:(!factors) ~constant:constant ~kind:kind
    
  method private reflectConstraints i2v (mat: matrix_t) =
    let csts = ref [] in
    let _ =
      for i = 0 to mat#nbrows - 1 do
	let cst_r = self#reflectConstraint i2v (mat#get_row i) in
	csts := if cst_r#getVariables#isEmpty then !csts else cst_r :: !csts
      done
    in
    !csts
    
  method getNonRelationalValue (v: variable_t) =
    if self#isBottom then
      bottomNonRelationalDomainValue
    else
      match var2index#get v with
      | None -> topNonRelationalDomainValue
      | Some _ ->
	 let i2v = Array.of_list [v] in
	 let (dimsup, permutation) = self#transfer ~extend:false i2v index2var in
	 let pol = polyhedron#permute_remove_dimensions dimsup permutation in
	 let csts = self#reflectConstraints i2v pol#get_constraints in
	 let range = ref topInterval in
	 let refine cst =
	   match cst#range with
	   | Some (x, r) ->
	      if x#equal v then
		range := (!range)#meet r
	      else
		raise (CHFailure (STR "Polyhedral domain: Inconsistency in getNonRelationalValue"))
	   | None ->
	      ()
	 in
	 let _ = List.iter refine csts in
	 mkIntervalValue !range
	 
  method importNonRelationalValues
           ?(refine = true)
           (env: (variable_t * non_relational_domain_value_t) list)  =
    if self#isBottom then
      self#mkBottom
    else
      let env_vars = new VariableCollections.set_t in
      let _ = env_vars#addList (List.map fst env) in
      if refine then
	let new_vars = var2index#keys#union env_vars in
	let (i2v, v2i) = self#arrangeVariables new_vars in
	let (dimsup, permutation) = self#transfer ~extend:true index2var i2v in
	let polyhedron' =
          (polyhedron#add_dimensions_and_embed dimsup)#permute_remove_dimensions 0 permutation in
	let csts = List.fold_left (fun a (x, v) -> (v#toNumericalConstraints x) @ a) [] env in
	let mat = self#reifyConstraints v2i csts in
	let pol = polyhedron'#add_constraints mat in
	if pol#is_empty then
	  self#mkBottom
	else
	  {< bottom = false;
	     index2var = i2v;
	     var2index = v2i;
	     polyhedron = pol
	  >}
      else
	let self_r = self#reflect in
	let self_r' = self#remove_variables_r self_r env_vars#toList in
	(self#reify self_r')#importNonRelationalValues ~refine:true env
	
  method importNumericalConstraints (csts: numerical_constraint_t list) =
    if self#isBottom then
      self#mkBottom
    else
      let csts_vars = new VariableCollections.set_t in
      let _ = List.iter (fun cst -> csts_vars#addSet cst#getVariables) csts in
      let new_vars = var2index#keys#union csts_vars in
      let (i2v, v2i) = self#arrangeVariables new_vars in
      let (dimsup, permutation) = self#transfer ~extend:true index2var i2v in
      let polyhedron' =
        (polyhedron#add_dimensions_and_embed dimsup)#permute_remove_dimensions 0 permutation in
      let mat = self#reifyConstraints v2i csts in
      let pol = polyhedron'#add_constraints mat in
      if pol#is_empty then
	self#mkBottom
      else
	{< bottom = false;
	   index2var = i2v;
	   var2index = v2i;
	   polyhedron = pol
	>}
      
  method observer =
    object
      inherit domain_observer_t
            
      method getObservedVariables = var2index#keys#toList
                                  
      method getPolyhedron =
        if self#isBottom then
	  None
        else
	  Some polyhedron
	
      method getNonRelationalVariableObserver v =
        self#getNonRelationalValue v
	
      method getNumericalConstraints ~(variables: variable_t list option) () =
        if self#isBottom then
	  []
        else
	  match variables with
	  | None -> 
	     let csts = polyhedron#get_constraints in
	     self#reflectConstraints index2var csts
	  | Some vars ->
	     let self_r = self#reflect in
	     let variables_to_keep = new VariableCollections.set_t in
	     let _ = variables_to_keep#addList vars in
	     let variables_to_remove = self_r.var2index#setOfKeys#diff variables_to_keep in
	     let self_r' = self#remove_variables_r self_r variables_to_remove#toList in
	     (self#reify self_r')#observer#getNumericalConstraints ~variables:None ()
             
      method getVariableOrdering = Some index2var
    end
    
  method private arrangeVariables (vars: VariableCollections.set_t) =
    let i2v = Array.make vars#size dummy_variable in
    let v2i = new VariableCollections.table_t in
    let _ =
      vars#fold (fun i v -> 
	  let _ = i2v.(i) <- v in
	  let _ = v2i#set v (mkNumerical i) in
	  i + 1) 0
    in
    (i2v, v2i)
    
  method private invert (i2v: variable_t array) =
    let v2i = new VariableCollections.table_t in
    let _ = 
      for i = 0 to (Array.length i2v) - 1 do
	v2i#set i2v.(i) (mkNumerical i)
      done
    in
    v2i
    
  method private transfer ~(extend: bool) (i2v_1: variable_t array) (i2v_2: variable_t array) =
    (* vars(i2v_1) is included in vars(i2v_2) *)
    let dimsup = (Array.length i2v_2) - (Array.length i2v_1) in
    let permutation = Array.make (Array.length i2v_2) 0 in
    let vars1 = new VariableCollections.set_t in
    let vars2 = new VariableCollections.set_t in
    let _ =
      begin 
	for i = 0 to (Array.length i2v_1) - 1 do
	  vars1#add i2v_1.(i)
	done;
	for i = 0 to (Array.length i2v_2) - 1 do
	  vars2#add i2v_2.(i)
	done
      end
    in
    let delta = vars2#diff vars1 in
    let i2v_1_ext = Array.make (Array.length i2v_2) dummy_variable in
    let _ = Array.blit i2v_1 0 i2v_1_ext 0 (Array.length i2v_1) in
    let _ = delta#fold (fun i v -> let _ = i2v_1_ext.(i) <- v in i + 1) (Array.length i2v_1) in
    let _ =
      if extend then
	let v2i_2 = self#invert i2v_2 in
	for i = 0 to (Array.length i2v_2) - 1 do
	  match v2i_2#get i2v_1_ext.(i) with
	  | Some i' -> 
	     permutation.(i) <- i'#toInt
	  | None -> 
	     raise (CHFailure (STR "Polyhedral domain: Inconsistency in transfer - extend = true"))
	done
      else
	let v2i_1_ext = self#invert i2v_1_ext in
	for i = 0 to (Array.length i2v_2) - 1 do
	  match v2i_1_ext#get i2v_2.(i) with
	  | Some i' -> 
	     permutation.(i) <- i'#toInt
	  | None -> 
	     raise (CHFailure (STR "Polyhedral domain: Inconsistency in transfer - extend = false"))		  
	done
    in
    (dimsup, permutation)
    
  method private cofiberedExtension (d1: 'a) (d2: 'a) =
    (* d1 and d2 must be non-bottom *)
    match (d1#observer#getPolyhedron, d2#observer#getPolyhedron) with
    | (Some p1, Some p2) ->
       let vars1 = VariableCollections.set_of_list d1#observer#getObservedVariables in
       let vars2 = VariableCollections.set_of_list d2#observer#getObservedVariables in
       let all_vars = vars1#union vars2 in
       let (i2v, _) = self#arrangeVariables all_vars in
       (match (d1#observer#getVariableOrdering, d2#observer#getVariableOrdering) with
	| (Some i2v1, Some i2v2) ->
	   let (dimsup1, permutation1) = self#transfer ~extend:true i2v1 i2v in
	   let (dimsup2, permutation2) = self#transfer ~extend:true i2v2 i2v in
	   let p1' =
             (p1#add_dimensions_and_embed dimsup1)#permute_remove_dimensions 0 permutation1 in
	   let p2' =
             (p2#add_dimensions_and_embed dimsup2)#permute_remove_dimensions 0 permutation2 in
	   (p1', p2', i2v)
	| _ ->
	   raise (CHFailure (STR "Polyhedral domain: Inconsistency #1 in cofiberedExtension"))
       )
    | _ -> 
       raise (CHFailure (STR "Polyhedral domain: Inconsistency #2 in cofiberedExtension"))
      
  method private cofiberedReduction (d1: 'a) (d2: 'a) =
    (* d1 and d2 must be non-bottom *)
    match (d1#observer#getPolyhedron, d2#observer#getPolyhedron) with
    | (Some p1, Some p2) ->
       let vars1 = VariableCollections.set_of_list d1#observer#getObservedVariables in
       let vars2 = VariableCollections.set_of_list d2#observer#getObservedVariables in
       let common_vars = vars1#inter vars2 in
       let (i2v, _) = self#arrangeVariables common_vars in
       (match (d1#observer#getVariableOrdering, d2#observer#getVariableOrdering) with
	| (Some i2v1, Some i2v2) ->
	   let (dimsup1, permutation1) = self#transfer ~extend:false i2v i2v1 in
	   let (dimsup2, permutation2) = self#transfer ~extend:false i2v i2v2 in
	   let p1' = p1#permute_remove_dimensions dimsup1 permutation1 in
	   let p2' = p2#permute_remove_dimensions dimsup2 permutation2 in
	   (p1', p2', i2v)
	| _ ->
	   raise (CHFailure (STR "Polyhedral domain: Inconsistency #1 in cofiberedReduction"))
       )
    | _ -> 
       raise (CHFailure (STR "Polyhedral domain: Inconsistency #2 in cofiberedReduction"))
      
  method leq ?(variables: variable_t list option) (dom: 'a) =
    if self#isBottom then
      true
    else if dom#isBottom then
      false
    else
      let (p1, p2, _) = self#cofiberedExtension self dom in
      p1#is_included_in p2
      
  method equal (dom: 'a) =
    if self#isBottom then
      dom#isBottom
    else if dom#isBottom then
      false
    else
      let (p1, p2, _) = self#cofiberedExtension self dom in
      p1#is_equal p2
      
  method meet ?(variables: variable_t list option) (dom: 'a) =
    if self#isBottom then
      self#mkBottom
    else if dom#isBottom then
      self#mkBottom
    else
      let (p1, p2, i2v) = self#cofiberedExtension self dom in
      let p = p1#intersection p2 in
      if p#is_empty then
	self#mkBottom
      else
	{< bottom = false;
	   index2var = i2v;
	   var2index = self#invert i2v;
	   polyhedron = p
	>}
      
  method narrowing ?(variables: variable_t list option) (dom: 'a) =
    if self#isBottom then
      self#mkBottom
    else
      {< >}
    
  method join ?(variables: variable_t list option) (dom: 'a) =
    if self#isBottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      try
	let (p1, p2, i2v) = self#cofiberedReduction self dom in
	{< bottom = false;
	   index2var = i2v;
	   var2index = self#invert i2v;
	   polyhedron = p1#convex_hull p2
	>}
      with
	CHFailure p ->
	raise (CHFailure
		 (LBLOCK [
                      p ; NL ;
		      STR "; called by CHPolyhdedraDomainNoArrays.polyhedra_domain_no_arrays_t#join" ;
                      NL ; var2index#toPretty ]))
	
  method widening ?(kind: string option) ?(variables: variable_t list option) (dom: 'a) =
    if self#isBottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      let (p1, p2, i2v) = self#cofiberedReduction self dom in
      {< bottom = false;
	 index2var = i2v;
	 var2index = self#invert i2v;
	 polyhedron = p1#widening p2
      >}
      
  method special (cmd: string) (args: domain_cmd_arg_t list) =
    match cmd with
    | "set_max_variable_set" ->
       let vars = new VariableCollections.set_t in
       let _ = List.iter (fun arg ->
                   match arg with VAR_DOM_ARG v -> vars#add v | _ -> ()) args in
       {< max_variable_set = vars >}
    | "expand_max_variable_set" ->
       let vars = max_variable_set#clone in
       let _ = List.iter (fun arg ->
                   match arg with VAR_DOM_ARG v -> vars#add v | _ -> ()) args in
       {< max_variable_set = vars >}
    | "include_tmps" -> {< include_tmps = true >}
    | "exclude_tmps" -> {< include_tmps = false >}
    | _ ->
       raise (CHFailure (LBLOCK [STR "Polyhedral Domain: unrecognized command '";
                                 STR cmd; STR "'"]))
      
  method toPretty =
    if self#isBottom then
      STR "_|_"
    else
      let csts = self#reflectConstraints index2var polyhedron#get_constraints in
      LBLOCK [STR "{"; NL;
	      INDENT (2, LBLOCK (List.fold_left (fun a c -> (c#toPretty) :: NL :: a) [] csts));
	      STR "}"]
      
  method private remove_variables_r (pol:reflected_poly_t) (l: variable_t list) =
    let vars = new VariableCollections.set_t in
    let _ = vars#addSet pol.var2index#keys in
    let new_vars = vars#clone in
    let _ = new_vars#removeList l in
    if vars#equal new_vars then
      pol
    else
      let (i2v, v2i) = self#arrangeVariables new_vars in
      let (dimsup, permutation) = self#transfer ~extend:false i2v pol.index2var in
      let poly = pol.polyhedron#permute_remove_dimensions dimsup permutation in
      { bottom = false;
	index2var = i2v;
	var2index = v2i;
	polyhedron = poly
      }
      
  method private add_variables_r (pol:reflected_poly_t) (l: variable_t list) =
    let vars = new VariableCollections.set_t in
    let _ = vars#addSet pol.var2index#keys in
    let new_vars = vars#clone in
    let _ = new_vars#addList l in
    if vars#equal new_vars then
      pol
    else
      let (i2v, v2i) = self#arrangeVariables new_vars in
      let (dimsup, permutation) = self#transfer ~extend:true pol.index2var i2v in
      let poly =
        (pol.polyhedron#add_dimensions_and_embed dimsup)#permute_remove_dimensions 0 permutation in
      { bottom = false;
	index2var = i2v;
	var2index = v2i;
	polyhedron = poly
      }
      
  method private filter_constraints (csts: numerical_constraint_t list) =
    match csts with
    | [] -> []
    | cst :: l ->
       let vars = cst#getVariablesList in
       (try
	  let _ =
            List.iter (fun v ->
	        if v#equal dummy_variable then
	          (* Used for internal computations *)
	          ()
	        else if max_variable_set#has v then
	          ()
	        else if v#isTmp then
	          if include_tmps then
		    ()
	          else
		    raise Found
	        else
	          raise Found
	      ) vars
	  in
	  cst :: (self#filter_constraints l)
	with Found -> self#filter_constraints l
       )
       
  method private add_constraints_r (pol: reflected_poly_t) (csts: numerical_constraint_t list) =
    let csts =
      if max_variable_set#isEmpty then
	csts
      else
	self#filter_constraints csts 
    in
    let vars = new VariableCollections.set_t in
    let _ = List.iter (fun cst -> vars#addSet cst#getVariables) csts in
    let pol = self#add_variables_r pol vars#toList in
    let mat = self#reifyConstraints pol.var2index csts in
    let poly = pol.polyhedron#add_constraints mat in
    if poly#is_empty then
      self#empty_pol_r
    else
      { bottom = false;
	index2var = pol.index2var;
	var2index = pol.var2index;
	polyhedron = poly
      }
    
  method analyzeBwd (cmd: (code_int, cfg_int) command_t) =
    if self#isBottom then
      match cmd with
      | ASSERT e ->
	 self#mkEmpty#analyzeFwd (ASSERT (negate_bool_exp e))
      | _ ->
	 self#mkBottom
    else
      match cmd with
      | ABSTRACT_VARS l ->
	 let self_r = self#reflect in	
	 let self_r' = self#remove_variables_r self_r l in
	 self#reify self_r'
      | ASSIGN_NUM (v, NUM n) ->
	 let self_r = self#reflect in
	 let self_r = self#remove_variables_r self_r [v] in
	 self#reify self_r
      | ASSIGN_NUM (v, NUM_VAR w) ->
	 if v#equal w then
	   {< >}
	 else
	   let self_r = self#reflect in
	   let v_f = new numerical_factor_t v in
	   let w_f = new numerical_factor_t w in
	   let eq = new numerical_constraint_t
                        [(numerical_one, v_f); (numerical_one#neg, w_f)]
                        numerical_zero LINEAR_EQ in
	   let self_r = self#add_constraints_r self_r [eq] in
	   let self_r = self#remove_variables_r self_r [v] in
	   self#reify self_r
      | ASSIGN_NUM (v, PLUS (x, y)) ->
	 let self_r = self#reflect in
	 let v_f = new numerical_factor_t v in
	 if (v#equal x) || (v#equal y) then
	   let self_r = self#remove_variables_r self_r [v] in
	   self#reify self_r
	 else
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq = 
	     if x#equal y then		  
	       new numerical_constraint_t
                   [(numerical_one, v_f); ((mkNumerical 2)#neg, x_f)]
                   numerical_zero LINEAR_EQ
	     else
	       new numerical_constraint_t
                   [(numerical_one, v_f);
                    (numerical_one#neg, x_f);
                    (numerical_one#neg, y_f)]
                   numerical_zero LINEAR_EQ 
		in
		let self_r = self#add_constraints_r self_r [eq] in
		let self_r = self#remove_variables_r self_r [v] in
		self#reify self_r
      | ASSIGN_NUM (v, MINUS (x, y)) ->
	 let self_r = self#reflect in
	 let v_f = new numerical_factor_t v in
	 if (v#equal x) || (v#equal y) || (x#equal y) then
	   let self_r = self#remove_variables_r self_r [v] in 
	   self#reify self_r
	 else
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq = new numerical_constraint_t
                        [(numerical_one, v_f);
                         (numerical_one#neg, x_f);
                         (numerical_one, y_f)]
                        numerical_zero LINEAR_EQ in		  
	   let self_r = self#add_constraints_r self_r [eq] in
	   let self_r = self#remove_variables_r self_r [v] in
	   self#reify self_r
      | ASSIGN_NUM (v, MULT (_, _))
	| ASSIGN_NUM (v, DIV (_, _))
	| READ_NUM_ELT (v, _, _) ->
	 let self_r = self#reflect in
	 let self_r = self#remove_variables_r self_r [v] in
	 self#reify self_r
      | INCREMENT (v, n) ->
	 self#analyzeFwd (INCREMENT (v, n#neg))
      | ASSERT TRUE ->
	 {< >}
      | ASSERT FALSE ->
	 self#mkBottom
      | ASSERT (EQ (x, y))
	| ASSERT (LEQ (x, y))
	| ASSERT (GEQ (x, y))
	| ASSERT (LT (x, y))
	| ASSERT (GT (x, y)) ->
	 self#analyzeFwd cmd
      | _ ->
	 {< >}
	
  method analyzeFwd (cmd: (code_int, cfg_int) command_t) =
    if self#isBottom then
      self#mkBottom
    else
      match cmd with
      | ABSTRACT_VARS l ->
	 let self_r = self#reflect in	
	 let self_r = self#remove_variables_r self_r l in
	 self#reify self_r
      | ASSIGN_NUM (v, NUM n) ->
	 let self_r = self#reflect in
	 let self_r = self#remove_variables_r self_r [v] in
	 let v_f = new numerical_factor_t v in
	 let eq = new numerical_constraint_t [(numerical_one, v_f)] n LINEAR_EQ in		
	 let self_r = self#add_constraints_r self_r [eq] in
	 self#reify self_r
      | ASSIGN_NUM (v, NUM_VAR w) ->
	 if v#equal w then
	   {< >}
	 else
	   let self_r = self#reflect in
	   let v_f = new numerical_factor_t v in
	   let w_f = new numerical_factor_t w in
	   let self_r = self#remove_variables_r self_r [v] in
	   let eq = new numerical_constraint_t
                        [(numerical_one, v_f); (numerical_one#neg, w_f)]
                        numerical_zero LINEAR_EQ in
	   let self_r = self#add_constraints_r self_r [eq] in
	   self#reify self_r
      | ASSIGN_NUM (v, PLUS (x, y)) ->
	 let self_r = self#reflect in
	 let v_f = new numerical_factor_t v in
	 let x_f = new numerical_factor_t x in
	 let y_f = new numerical_factor_t y in
	 let eq = 
	   if x#equal y then
	     new numerical_constraint_t
                 [(numerical_one, dummy_factor); ((mkNumerical 2)#neg, x_f)]
                 numerical_zero LINEAR_EQ
	   else
	     new numerical_constraint_t
                 [(numerical_one, dummy_factor);
                  (numerical_one#neg, x_f);
                  (numerical_one#neg, y_f)]
                 numerical_zero LINEAR_EQ 
	 in
	 let self_r = self#add_constraints_r self_r [eq] in
	 let self_r = self#remove_variables_r self_r [v] in
	 let eq' = new numerical_constraint_t
                       [(numerical_one, v_f); (numerical_one#neg, dummy_factor)]
                       numerical_zero LINEAR_EQ in
	 let self_r = self#add_constraints_r self_r [eq'] in
	 let self_r = self#remove_variables_r self_r [dummy_variable] in
	 self#reify self_r
      | ASSIGN_NUM (v, MINUS (x, y)) ->
	 let self_r = self#reflect in
	 if x#equal y then
	   self#analyzeFwd (ASSIGN_NUM (v, NUM numerical_zero))
	 else
	   let v_f = new numerical_factor_t v in
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq = new numerical_constraint_t
                        [(numerical_one, dummy_factor);
                         (numerical_one#neg, x_f);
                         (numerical_one, y_f)]
                        numerical_zero LINEAR_EQ in
	   let self_r = self#add_constraints_r self_r [eq] in
	   let self_r = self#remove_variables_r self_r [v] in
	   let eq' = new numerical_constraint_t
                         [(numerical_one, v_f); (numerical_one#neg, dummy_factor)]
                         numerical_zero LINEAR_EQ in
	   let self_r = self#add_constraints_r self_r [eq'] in
	   let self_r = self#remove_variables_r self_r [dummy_variable] in
	   self#reify self_r
      | ASSIGN_NUM (v, MULT (x, y)) ->
	 let self_r = self#reflect in
	 let self_r = self#remove_variables_r self_r [v] in
	 let x_r = (self#getNonRelationalValue x)#toInterval in
	 let y_r = (self#getNonRelationalValue y)#toInterval in
	 let v_f = new numerical_factor_t v in
	 let x_f = new numerical_factor_t x in
	 let y_f = new numerical_factor_t y in
	 let csts = match (x_r#singleton, y_r#singleton) with
	   | (None, None) ->
	      let v_r = x_r#mult y_r in
	      (mkIntervalValue v_r)#toNumericalConstraints v
	   | (Some x_c, Some y_c) ->
	      let v_c = x_c#mult y_c in
	      (mkNumericalConstantValue (mkNumericalConstant v_c))#toNumericalConstraints v
	   | (Some x_c, None) ->
	      [new numerical_constraint_t
                   [(numerical_one, v_f); (x_c#neg, y_f)] numerical_zero LINEAR_EQ]
	   | (None, Some y_c) ->
	      [new numerical_constraint_t
                   [(numerical_one, v_f); (y_c#neg, x_f)] numerical_zero LINEAR_EQ]
	 in
	 let self_r = self#add_constraints_r self_r csts in
	 self#reify self_r
      | ASSIGN_NUM (v, DIV (_, _))
	| READ_NUM_ELT (v, _, _) ->
	 let self_r = self#reflect in
	 let self_r = self#remove_variables_r self_r [v] in
	 self#reify self_r
      | INCREMENT (v, n) ->
	 let self_r = self#reflect in
	 if n#equal numerical_zero then
	   {< >}
	 else
	   let v_f = new numerical_factor_t v in
	   let eq = new numerical_constraint_t
                        [(numerical_one, dummy_factor); (numerical_one#neg, v_f)]
                        n LINEAR_EQ in
	   let self_r = self#add_constraints_r self_r [eq] in
	   let self_r = self#remove_variables_r self_r [v] in
	   let eq' = new numerical_constraint_t
                         [(numerical_one, v_f); (numerical_one#neg, dummy_factor)]
                         numerical_zero LINEAR_EQ in
	   let self_r = self#add_constraints_r self_r [eq'] in
	   let self_r = self#remove_variables_r self_r [dummy_variable] in
	   self#reify self_r
      | ASSERT TRUE ->
	 {< >}
      | ASSERT FALSE ->
	 self#mkBottom
      | ASSERT (EQ (x, y)) ->
	 if x#equal y then
	   {< >}
	 else
	   let self_r = self#reflect in
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq = new numerical_constraint_t
                        [(numerical_one, x_f); (numerical_one#neg, y_f)]
                        numerical_zero LINEAR_EQ in
	   let self_r = self#add_constraints_r self_r [eq] in
	   self#reify self_r
      | ASSERT (LEQ (x, y)) ->
	 if x#equal y then
	   {< >}
	 else
	   let self_r = self#reflect in
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq = new numerical_constraint_t
                        [(numerical_one, x_f); (numerical_one#neg, y_f)]
                        numerical_zero LINEAR_INEQ in
	   let self_r = self#add_constraints_r self_r [eq] in
	   self#reify self_r
      | ASSERT (LT (x, y)) ->
	 if x#equal y then
	   {< >}
	 else
	   let self_r = self#reflect in
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq = new numerical_constraint_t
                        [(numerical_one, x_f); (numerical_one#neg, y_f)]
                        numerical_one#neg LINEAR_INEQ in
	   let self_r = self#add_constraints_r self_r [eq] in
	   self#reify self_r
      | ASSERT (GEQ (x, y)) ->
	 self#analyzeFwd (ASSERT (LEQ (y, x)))
      | ASSERT (GT (x, y)) ->
	 self#analyzeFwd (ASSERT (LT (y, x)))
      | _ ->
	 {< >}
        
  method analyzeFwdInTransaction = self#analyzeFwd
                                 
  method analyzeBwdInTransaction = self#analyzeBwd
	                         
  method analyzeOperation
           ~(domain_name: string)
           ~(fwd_direction: bool)
           ~(operation: operation_t): 'a =
    raise (CHFailure (LBLOCK [ STR "Domain "; STR domain_name;
                               STR " does not implement operation ";
                               operation.op_name#toPretty]))

  method clone = {< >}
	      
end

(* =============================================================================
   CodeHawk Abstract Interpretation Engine
   Author: Arnaud Venet
   -----------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2022 Henny Sipma
   Copyright (c) 2023      Aarno Labs LLC

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
open CHLanguage
open CHNonRelationalDomainValues   
open CHNumerical
open CHNumericalConstraints   
open CHPretty
open CHUtils

[@@@warning "-27"]

exception Contradiction
exception Got_integer of int

let dummy_variable = new variable_t (new symbol_t "<#dummy#>") NUM_VAR_TYPE
let dummy_factor = new numerical_factor_t dummy_variable

type reflected_structure_t = {
  mutable bottom: bool;
  factors: FactorCollections.set_t;
  factors_order: numerical_factor_t array;
  factor_to_rank: numerical_t FactorCollections.table_t;
  matrix: numerical_constraint_t option array;
}

let reflectBottom () = 
  {
    bottom = true; 
    factors = new FactorCollections.set_t; 
    factors_order = Array.make 0 dummy_factor;
    factor_to_rank = new FactorCollections.table_t;
    matrix = Array.make 0 None
  }
  
let reflect_trivial (vars: variable_t list) =
  let var_set = new VariableCollections.set_t in
  let _ = var_set#addList vars in
  let normalized = var_set#toList in
  let factors_order = Array.of_list (List.map (fun v -> new numerical_factor_t v) normalized) in
  let factors = new FactorCollections.set_t in
  let factor_to_rank = new FactorCollections.table_t in
  let _ =
    for i = 0 to (Array.length factors_order) - 1 do
      factors#add (factors_order.(i));
      factor_to_rank#set (factors_order.(i)) (mkNumerical i)
    done
  in
  {
    bottom = false;
    factors = factors;
    factors_order = factors_order;
    factor_to_rank = factor_to_rank;
    matrix = Array.make 0 None
  }    
  
let _reflected_to_pretty rs =
  if rs.bottom then
    STR "_|_"
  else
    LBLOCK [STR "factors = "; rs.factors#toPretty; NL;
	    STR "factors_order = ";
            ABLOCK (Array.map (fun f -> LBLOCK [f#toPretty; STR " "]) rs.factors_order); NL;
	    STR "factor_to_rank = "; rs.factor_to_rank#toPretty; NL;
	    STR "matrix = "; NL; 
	    INDENT (2, 
		    ABLOCK (Array.mapi (fun i r ->
                                match r with
                                | None -> LBLOCK [INT i; STR ": NONE"; NL]
                                | Some cst ->
                                   LBLOCK [INT i; STR ": "; cst#toPretty; NL]) rs.matrix)
		   ); 
	    NL]
  
let getRank rs f =
  try
    match rs.factor_to_rank#get f with
    | None -> raise (CHFailure (STR "Internal error in Gauss algorithm #1"))
    | Some r -> r#toInt
  with
  | CHFailure p ->
     raise (CHFailure (LBLOCK [ STR "Error in getRank: " ; p ]))
    
let getPivot rs eq =
  let ranks = List.map (getRank rs) eq#getFactors in
  let r0 = match ranks with
    | [] -> raise (CHFailure (STR "Internal error in Gauss algorithm #2"))
    | r :: _ -> r
  in
  List.fold_left (fun a r -> if r < a then r else a) r0 ranks
  
let rec add_cst_r rs eq =
  if eq#isContradiction then
    raise Contradiction
  else if eq#isTrivial then
    ()
  else
    let pivot_rank = getPivot rs eq in
    let pivot_factor = rs.factors_order.(pivot_rank) in
    eq#normalize ?pivot:(Some pivot_factor) ();
    match rs.matrix.(pivot_rank) with
    | None -> 
       rs.matrix.(pivot_rank) <- Some eq
    | Some eq' ->
       let c = eq#getCoefficient pivot_factor in
       let c' = eq'#getCoefficient pivot_factor in
       let eq'' = eq'#affineCombination c c'#neg eq in
       add_cst_r rs eq''
       
let back_propagation_r rs =
  for pivot_r = (Array.length rs.matrix) - 1 downto 0 do
    match rs.matrix.(pivot_r) with
    | None -> ()
    | Some pivot_eq ->
       let pivot = rs.factors_order.(pivot_r) in
       let c = pivot_eq#getCoefficient pivot in
       for r = pivot_r - 1 downto 0 do
	 match rs.matrix.(r) with
	 | Some eq' ->
	    let c' = eq'#getCoefficient pivot in
	    if c'#equal numerical_zero then
	      ()
	    else
	      let eq'' = eq'#affineCombination c c'#neg pivot_eq in
	      begin
		eq''#normalize ?pivot:(Some rs.factors_order.(r)) ();
		rs.matrix.(r) <- Some eq''
	      end
	 | None ->
	    ()
       done
  done
  
let rec filter_constraints max_variable_set include_tmps csts =
  match csts with
  | [] -> []
  | cst :: l ->
     try
       let _ =
         if max_variable_set#isEmpty then
	   ()
	 else
	   let vars = cst#getVariablesList in
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
       cst :: (filter_constraints max_variable_set include_tmps l)
     with Found -> filter_constraints max_variable_set include_tmps l
	         
let add_csts_r max_variable_set include_tmps rs csts =
  try 
    List.iter (add_cst_r rs) (filter_constraints max_variable_set include_tmps csts)
  with Contradiction -> rs.bottom <- true
                      
let extract_csts_r rs =
  List.fold_left (fun l cst ->
      match cst with None -> l | Some eq -> eq :: l) [] (Array.to_list rs.matrix)
  
let join_r max_variable_set include_tmps rs1 rs2 =
  let csts1 = extract_csts_r rs1 in
  let csts2 = extract_csts_r rs2 in
  let factors_order = rs1.factors_order in
  let nfactors = Array.length factors_order in
  let factors' = new FactorCollections.set_t in
  let factors_order' = Array.make (2 * nfactors + 1) dummy_factor in
  let factor_to_rank' = new FactorCollections.table_t in
  let _ =
    for i = 0 to nfactors - 1 do
      let f = factors_order.(i) in
      let tf = f#tag "t" in
      factors_order'.(i) <- tf;
      factor_to_rank'#set tf (mkNumerical i);
      factors_order'.(i + nfactors + 1) <- f;
      factor_to_rank'#set f (mkNumerical (i + nfactors + 1));
      factors'#addList [f; tf]
    done
  in
  let tcst = dummy_factor#tag "t" in
  let _ = factors_order'.(nfactors) <- tcst in
  let _ = factor_to_rank'#set tcst (mkNumerical nfactors) in
  let _ = factors'#add tcst in    
  let join = {
      bottom = false;
      factors = factors';
      factors_order = factors_order';
      factor_to_rank = factor_to_rank';
      matrix = Array.make (2 * nfactors + 1) None
    }
  in
  let t_star cst =
    let f_l = cst#getFactorsList in
    let f_l' = List.map (fun (c, f) -> (c, f#tag "t")) f_l in
    let f_l'' = (cst#getConstant#neg, tcst) :: f_l' in
    new numerical_constraint_t ~factors:f_l'' ~constant:numerical_zero ~kind:LINEAR_EQ
  in
  let one_minus_t_star cst =
    let f_l = cst#getFactorsList in
    let f_l_t = List.map (fun (c, f) -> (c#neg, f#tag "t")) f_l in
    let f_l_t' = (cst#getConstant, tcst) :: f_l_t in
    new numerical_constraint_t
        ~factors:(f_l @ f_l_t')
        ~constant:cst#getConstant
        ~kind:LINEAR_EQ
  in
  let csts1' = List.map t_star csts1 in
  let csts2' = List.map one_minus_t_star csts2 in
  let _ = add_csts_r max_variable_set include_tmps join (csts1' @ csts2') in
  let matrix' = Array.make nfactors None in
  let _ = Array.blit join.matrix (nfactors + 1) matrix' 0 nfactors in
  {
    bottom = false;
    factors = rs1.factors;
    factors_order = rs1.factors_order;
    factor_to_rank = rs1.factor_to_rank;
    matrix = matrix';
  }
  
let equal_r rs1 rs2 =
  let _ = back_propagation_r rs1 in
  let _ = back_propagation_r rs2 in
  rs1.factors#equal rs2.factors &&
    try
      for i = 0 to rs1.factors#size - 1 do
	match (rs1.matrix.(i), rs2.matrix.(i)) with
	| (None, None) -> ()
	| (Some eq1, Some eq2) when eq1#equal eq2 -> ()
	| _ -> raise Found
      done;
      true
    with Found -> false
                
let remove_factors_r max_variable_set include_tmps rs fs =
  let factors_to_remove = new FactorCollections.set_t in
  let _ = factors_to_remove#addList fs in
  if rs.factors#size = 0 || factors_to_remove#size = 0 then
    rs
  else
    let first_to_keep =
      ref (
	  try
	    for i = 0 to rs.factors#size - 1 do
	      if factors_to_remove#has rs.factors_order.(i) then 
	        () 
	      else
	        raise (Got_integer i)
	    done;
	    rs.factors#size
	  with Got_integer i -> i
        )
    in
    let factors_order' = Array.copy rs.factors_order in
    let _ =
      for i = !first_to_keep + 1 to rs.factors#size - 1 do
	if factors_to_remove#has factors_order'.(i) then
	  let tmp = factors_order'.(!first_to_keep) in
	  factors_order'.(!first_to_keep) <- factors_order'.(i);
	  factors_order'.(i) <- tmp;
	  first_to_keep := !first_to_keep + 1
      done
    in
    let factor_to_rank' = new FactorCollections.table_t in
    let _ =
      for i = 0 to (Array.length factors_order') - 1 do
	factor_to_rank'#set factors_order'.(i) (mkNumerical i)
      done
    in
    let rs' = {
        bottom = false;
	factors = rs.factors;
	factors_order = factors_order';
	factor_to_rank = factor_to_rank';
	matrix = Array.make rs.factors#size None;
      }
    in
    let csts = extract_csts_r rs in
    let _ = add_csts_r max_variable_set include_tmps rs' csts in
    let reduced_factors = rs.factors#diff factors_to_remove in
    let reduced_factors_order = Array.make reduced_factors#size dummy_factor in
    let _ = Array.blit
              factors_order'
              !first_to_keep
              reduced_factors_order
              0
              reduced_factors#size in
    let reduced_factor_to_rank = new FactorCollections.table_t in
    let _ = for i = 0 to (Array.length reduced_factors_order) - 1 do
	      reduced_factor_to_rank#set reduced_factors_order.(i) (mkNumerical i)
            done
    in
    let reduced_matrix = Array.make reduced_factors#size None in
    let _ = Array.blit
              rs'.matrix
              !first_to_keep
              reduced_matrix
              0
              reduced_factors#size in
    {
      bottom = false;
      factors = reduced_factors;
      factors_order = reduced_factors_order;
      factor_to_rank = reduced_factor_to_rank;
      matrix = reduced_matrix;
    }
    
let relax_factor_r rs f =
  let rec find_first r =
    if r < 0 then
      None
    else
      match rs.matrix.(r) with
      | None -> find_first (r - 1)
      | Some eq ->
	 if (eq#getCoefficient f)#equal numerical_zero then
	   find_first (r - 1)
	 else
	   Some (r, eq)
  in
  let rank = getRank rs f in
  match find_first rank with
  | None -> 
     ()
  | Some (r, eq) ->
     let c = eq#getCoefficient f in
     begin
       for i = r - 1 downto 0 do
	 match rs.matrix.(i) with
	 | None -> ()
	 | Some eq' ->
	    let c' = eq'#getCoefficient f in
	    if c'#equal numerical_zero then
	      ()
	    else
	      let eq'' = eq'#affineCombination c c'#neg eq in
	      eq''#normalize ?pivot:(Some rs.factors_order.(i)) ();
	      rs.matrix.(i) <- Some eq''
       done;
       rs.matrix.(r) <- None
     end
     
class linear_equalities_domain_no_arrays_t: domain_int =
object (self: 'a)
     
  inherit ['a] domain_downlink_t
        
  val bottom = false
             
  val factors = new FactorCollections.set_t
              
  val factors_order: numerical_factor_t array = Array.make 0 dummy_factor
                                              
  val factor_to_rank: numerical_t FactorCollections.table_t = new FactorCollections.table_t
                                                            
  val matrix: numerical_constraint_t option array = Array.make 0 None
                                                  
  val max_variable_set: VariableCollections.set_t = new VariableCollections.set_t
                                                  
  val include_tmps: bool = true
                         
  method isRelational = true
                      
  method mkBottom =
    if bottom then
      {< >}
    else
      {< 
	bottom = true; 
	factors = new FactorCollections.set_t; 
	factors_order = Array.make 0 dummy_factor;
	factor_to_rank = new FactorCollections.table_t;
	matrix = Array.make 0 None
      >}
    
  method mkEmpty =
    {<
      bottom = false; 
      factors = new FactorCollections.set_t; 
      factors_order = Array.make 0 dummy_factor;
      factor_to_rank = new FactorCollections.table_t;
      matrix = Array.make 0 None
    >}
    
  method private reify (reflection: reflected_structure_t) =
    if reflection.bottom then
      self#mkBottom
    else
      {<
	bottom = reflection.bottom;
	factors = reflection.factors;
	factors_order = reflection.factors_order;
	factor_to_rank = reflection.factor_to_rank;
	matrix = reflection.matrix
      >}
    
  method private reflect clone () =
    if clone then
      {
	bottom = bottom;
	factors = factors#clone;
	factors_order = Array.copy factors_order;
	factor_to_rank = factor_to_rank#clone;
	matrix = Array.copy matrix;
      }
    else
      {
	bottom = bottom;
	factors = factors;
	factors_order = factors_order;
	factor_to_rank = factor_to_rank;
	matrix = matrix;
      }
    
  method private extendAndReflect clone (vars: variable_t list) =
    match vars with
    | [] -> 
       self#reflect clone ()
    | _ -> 
       let trivial = self#reify (reflect_trivial vars) in
       let (self_r, _) = self#cofiberedReflection trivial in
       self_r
       
  method private cofiberedReflection (o: 'a) =
    (* self and o are not bottom *)
    let o_refl = self#reflectOther o in
    let matrix' = Array.make o_refl.factors#size None in
    let _ = Array.blit matrix 0 matrix' 0 factors#size in
    let self_refl = {
        bottom = bottom;
        factors = o_refl.factors;
        factors_order = o_refl.factors_order;
        factor_to_rank = o_refl.factor_to_rank;
        matrix = matrix';
      }
    in
    (self_refl, o_refl)
    
  method private reflectOther (o: 'a) =
    if o#isBottom then
      reflectBottom ()
    else
      let obs = o#observer in
      let other_factors = FactorCollections.set_of_list obs#getObservedFactors in
      let other_constraints = obs#getNumericalConstraints ~variables:None () in
      let (factors', factors_order', factor_to_rank') = 
	if other_factors#subset factors then
	  (factors, factors_order, factor_to_rank)
	else
	  let diff = other_factors#diff factors in
	  let factors' = factors#union diff in
	  let factors_order' = Array.make factors'#size dummy_factor in
	  let _ = Array.blit factors_order 0 factors_order' 0 factors#size in
	  let factor_to_rank' = factor_to_rank#clone in
	  let _ =
            diff#fold (fun r f -> 
		let _ = factor_to_rank'#set f (mkNumerical r) in
		let _ = factors_order'.(r) <- f in
		r + 1)
	              factors#size
	  in
	  (factors', factors_order', factor_to_rank')
      in
      let matrix' = Array.make factors'#size None in
      let rs = {
	  bottom = false;
	  factors = factors';
	  factors_order = factors_order';
	  factor_to_rank = factor_to_rank';
	  matrix = matrix';
        }
      in
      let _ = add_csts_r max_variable_set include_tmps rs other_constraints in
      rs
      
  method observer =
    object
      inherit domain_observer_t
            
      method! getObservedFactors = factors#toList
                                
      method! getObservedVariables = List.map (fun f -> f#getVariable) factors#toList
                                  
      method! getNumericalConstraints ~(variables: variable_t list option) () =
        let get_csts mat =
	  Array.fold_right (fun c a -> match c with Some cst -> cst :: a | None -> a) mat []
        in
	match variables with
	| None -> 
	   let self_r = self#reflect false () in
	   let _ = back_propagation_r self_r in
	   get_csts self_r.matrix
	| Some vars -> 
	   let self_r = self#reflect true () in
	   let factors_to_keep = new FactorCollections.set_t in
	   let _ = factors_to_keep#addList (List.map (fun v -> new numerical_factor_t v) vars) in
	   let factors_to_remove = self_r.factors#diff factors_to_keep in
	   let self_r' =
             remove_factors_r
               max_variable_set
               include_tmps
               self_r
               factors_to_remove#toList in
	   let _ = back_propagation_r self_r' in
	   get_csts self_r'.matrix
    end
    
  method toPretty =
    if bottom then
      STR "_|_"
    else
      LBLOCK [STR "{"; NL;
	      INDENT (2, LBLOCK (List.map
                                   (fun c -> LBLOCK [c#toPretty; NL])
                                   (self#observer#getNumericalConstraints ~variables:None ())));
	      STR "}"]
    
  method isBottom = bottom
                  
  method equal (dom: 'a) =
    if bottom then
      dom#isBottom
    else if dom#isBottom then
      self#isBottom
    else
      let (self_r, dom_r) = self#cofiberedReflection dom in
      equal_r self_r dom_r
      
  method leq ?(variables: variable_t list option) (dom: 'a) =
    if bottom then
      true
    else if dom#isBottom then 
      false
    else
      let i = self#meet dom in
      i#equal self
      
  method meet ?(variables: variable_t list option) (dom: 'a) =
    if bottom then
      self#mkBottom
    else if dom#isBottom then
      self#mkBottom
    else
      let (self_r, dom_r) = self#cofiberedReflection dom in
      let _ = add_csts_r max_variable_set include_tmps self_r (extract_csts_r dom_r) in
      if self_r.bottom then
	self#mkBottom
      else
	self#reify self_r
      
  method join ?(variables: variable_t list option) (dom: 'a) =
    if bottom then
      dom
    else if dom#isBottom then
      {< >}
    else
      let (self_r, dom_r) = self#cofiberedReflection dom in
      self#reify (join_r max_variable_set include_tmps self_r dom_r)
      
  method narrowing = self#meet
                   
  method projectOut (l:variable_t list) = self#analyzeFwd (ABSTRACT_VARS l)
                                        
  method widening ?(kind: string option) ?(variables: variable_t list option) (o: 'a) =
    self#join o
    
  method special (cmd: string) (args: domain_cmd_arg_t list) =
    match cmd with
    | "set_max_variable_set" ->
       let vars = new VariableCollections.set_t in
       let _ =
         List.iter (fun arg ->
             match arg with VAR_DOM_ARG v -> vars#add v | _ -> ()) args in
       {< max_variable_set = vars >}
    | "expand_max_variable_set" ->
       let vars = max_variable_set#clone in
       let _ =
         List.iter (fun arg ->
             match arg with VAR_DOM_ARG v -> vars#add v | _ -> ()) args in
       {< max_variable_set = vars >}
    | "include_tmps" -> {< include_tmps = true >}
    | "exclude_tmps" -> {< include_tmps = false >}
    | _ -> raise (CHFailure (LBLOCK [STR "Linear Equality Domain: unrecognized command '";
                                     STR cmd; STR "'"]))
	 
  method getNonRelationalValue v =
    try
      let f = new numerical_factor_t v in
      match factor_to_rank#get f with
      | None -> topNonRelationalDomainValue
      | Some r ->
	 begin
	   match matrix.(r#toInt) with
	   | None -> topNonRelationalDomainValue
	   | Some eq ->
	      begin
		match eq#getFactors with
		| [_] -> mkNumericalConstantValue (mkNumericalConstant eq#getConstant)
		| _ -> topNonRelationalDomainValue
	      end
	 end
    with
    | CHFailure p ->
       raise (CHFailure (LBLOCK [ STR "Error in getNonRelationalValue v: " ; p ]))
      
  method importNumericalConstraints (csts: numerical_constraint_t list) =
    let csts' = List.filter (fun cst -> cst#getKind = LINEAR_EQ) csts in
    let csts_variables = new VariableCollections.set_t in
    let _ = List.iter (fun cst -> csts_variables#addSet cst#getVariables) csts' in
    let self_r = self#extendAndReflect true csts_variables#toList in      
    let _ = add_csts_r max_variable_set include_tmps self_r csts' in      
    self#reify self_r
    
  method importNonRelationalValues ?(refine = true) l =
    let factors' = new FactorCollections.set_t in
    let _ = List.iter (fun (v, _) -> factors'#add (new numerical_factor_t v)) l in
    let factors_order' = Array.make factors'#size dummy_factor in
    let factor_to_rank' = new FactorCollections.table_t in
    let _ =
      factors'#fold (fun r f -> 
	  begin
	    factors_order'.(r) <- f;
	    factor_to_rank'#set f (mkNumerical r);
	    r + 1
	  end) 0 
    in
    let rs' = {
        bottom = false;
	factors = factors';
	factors_order = factors_order';
	factor_to_rank = factor_to_rank';
	matrix = Array.make factors'#size None;
      }
    in
    let _ =
      add_csts_r
        max_variable_set
        include_tmps
        rs'
        (List.fold_left (fun csts (v, c) -> 
	     match c#getValue with
	     | NUM_CONSTANT_VAL c ->
		begin
		  match c#getCst with
		  | NUM_CST n -> 
		     (new numerical_constraint_t
                          ~factors:[(numerical_one, new numerical_factor_t v)]
                          ~constant:n ~kind:LINEAR_EQ) :: csts
		  | _ -> csts
		end
	     | _ -> csts
	   ) [] l) 
    in
    let to_import = self#reify rs' in
    if refine then
      self#meet to_import
    else
      let self_r = self#reflect true () in
      let _ = factors'#iter (fun f -> relax_factor_r self_r f) in
      (self#reify self_r)#meet to_import
      
  method private analyzeBwd' clone (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      match cmd with
      | ASSERT e ->
	 self#mkEmpty#analyzeFwd (ASSERT (negate_bool_exp e))
      | _ ->
	 self#mkBottom
    else
      match cmd with
      | ABSTRACT_VARS l ->
	 let self_r = self#reflect clone () in	
	 let factors = List.map (fun v -> new numerical_factor_t v) l in
	 let self_r' = remove_factors_r max_variable_set include_tmps self_r factors in
	 self#reify self_r'
      | ASSIGN_NUM (v, NUM n) ->
	 let self_r = self#extendAndReflect clone [v] in
	 let v_f = new numerical_factor_t v in
	 let _ = relax_factor_r self_r v_f in
	 self#reify self_r
      | ASSIGN_NUM (v, NUM_VAR w) ->
	 if v#equal w then
	   {< >}
	 else
	   let self_r = self#extendAndReflect clone [v; w] in
	   let v_f = new numerical_factor_t v in
	   let w_f = new numerical_factor_t w in
	   let eq =
             new numerical_constraint_t
               ~factors:[(numerical_one, v_f); (numerical_one#neg, w_f)]
               ~constant:numerical_zero
               ~kind:LINEAR_EQ in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	   let _ = relax_factor_r self_r v_f in
	   self#reify self_r
      | ASSIGN_NUM (v, PLUS (x, y)) ->
	 let self_r = self#extendAndReflect clone [v; x; y] in
	 let v_f = new numerical_factor_t v in
	 if (v#equal x) || (v#equal y) then
	   let _ = relax_factor_r self_r v_f in
	   self#reify self_r
	 else
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq = 
	     if x#equal y then		  
	       new numerical_constraint_t
                   ~factors:[(numerical_one, v_f); ((mkNumerical 2)#neg, x_f)]
                   ~constant:numerical_zero
                   ~kind:LINEAR_EQ
	     else
	       new numerical_constraint_t
                 ~factors:[(numerical_one, v_f);
                           (numerical_one#neg, x_f);
                           (numerical_one#neg, y_f)]
                 ~constant:numerical_zero
                 ~kind:LINEAR_EQ
	   in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	   let _ = relax_factor_r self_r v_f in
	   self#reify self_r		  
      | ASSIGN_NUM (v, MINUS (x, y)) ->
	 let self_r = self#extendAndReflect clone [v; x; y] in
	 let v_f = new numerical_factor_t v in
	 if (v#equal x) || (v#equal y) || (x#equal y) then
	   let _ = relax_factor_r self_r v_f in
	   self#reify self_r
	 else
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq =
             new numerical_constraint_t
               ~factors:[(numerical_one, v_f);
                         (numerical_one#neg, x_f);
                         (numerical_one, y_f)]
               ~constant:numerical_zero
               ~kind:LINEAR_EQ in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	   let _ = relax_factor_r self_r v_f in
	   self#reify self_r
      | ASSIGN_NUM (v, MULT (_, _))
	| ASSIGN_NUM (v, DIV (_, _))
	| READ_NUM_ELT (v, _, _) ->
	 let self_r = self#extendAndReflect clone [v] in
	 let v_f = new numerical_factor_t v in
	 let _ = relax_factor_r self_r v_f in
	 self#reify self_r
      | INCREMENT (v, n) ->
	 self#analyzeFwd' clone (INCREMENT (v, n#neg))
      | ASSERT TRUE ->
	 {< >}
      | ASSERT FALSE ->
	 self#mkBottom
      | ASSERT (EQ (x, y)) ->
	 self#analyzeFwd' clone cmd
      | _ ->
	 {< >}
        
  method private analyzeFwd' clone (cmd: (code_int, cfg_int) command_t) =
    if bottom then
      self#mkBottom
    else
      match cmd with
      | ABSTRACT_VARS l ->
	 let self_r = self#reflect clone () in	
	 let factors = List.map (fun v -> new numerical_factor_t v) l in
	 let self_r' = remove_factors_r max_variable_set include_tmps self_r factors in
	 self#reify self_r'
      | ASSIGN_NUM (v, NUM n) ->
	 let self_r = self#extendAndReflect clone [v] in	
	 let v_f = new numerical_factor_t v in
	 let _ = relax_factor_r self_r v_f in
	 let eq =
           new numerical_constraint_t
             ~factors:[(numerical_one, v_f)] ~constant:n ~kind:LINEAR_EQ in
	 let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	 self#reify self_r
      | ASSIGN_NUM (v, NUM_VAR w) ->
	 if v#equal w then
	   {< >}
	 else
	   let self_r = self#extendAndReflect clone [v; w] in
	   let v_f = new numerical_factor_t v in
	   let w_f = new numerical_factor_t w in
	   let _ = relax_factor_r self_r v_f in
	   let eq =
             new numerical_constraint_t
               ~factors:[(numerical_one, v_f); (numerical_one#neg, w_f)]
               ~constant:numerical_zero
               ~kind:LINEAR_EQ in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	   self#reify self_r
      | ASSIGN_NUM (v, PLUS (x, y)) ->
	 let self_r = self#extendAndReflect clone [v; x; y; dummy_variable] in
	 let v_f = new numerical_factor_t v in
	 let x_f = new numerical_factor_t x in
	 let y_f = new numerical_factor_t y in
	 let eq = 
	   if x#equal y then
	     new numerical_constraint_t
                 ~factors:[(numerical_one, dummy_factor); ((mkNumerical 2)#neg, x_f)]
                 ~constant:numerical_zero
                 ~kind:LINEAR_EQ
	   else
	     new numerical_constraint_t
               ~factors:[(numerical_one, dummy_factor);
                         (numerical_one#neg, x_f);
                         (numerical_one#neg, y_f)]
               ~constant:numerical_zero
               ~kind:LINEAR_EQ
	 in
	 let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	 let _ = relax_factor_r self_r v_f in
	 let eq' =
           new numerical_constraint_t
             ~factors:[(numerical_one, v_f); (numerical_one#neg, dummy_factor)]
             ~constant:numerical_zero
             ~kind:LINEAR_EQ in
	 let _ = add_csts_r max_variable_set include_tmps self_r [eq'] in
	 let _ = relax_factor_r self_r dummy_factor in
	 self#reify self_r
      | ASSIGN_NUM (v, MINUS (x, y)) ->
	 let self_r = self#extendAndReflect clone [v; x; y; dummy_variable] in
	 if x#equal y then
	   self#analyzeFwd' clone (ASSIGN_NUM (v, NUM numerical_zero))
	 else
	   let v_f = new numerical_factor_t v in
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq =
             new numerical_constraint_t
               ~factors:[(numerical_one, dummy_factor);
                         (numerical_one#neg, x_f);
                         (numerical_one, y_f)]
               ~constant:numerical_zero
               ~kind:LINEAR_EQ in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	   let _ = relax_factor_r self_r v_f in
	   let eq' =
             new numerical_constraint_t
               ~factors:[(numerical_one, v_f); (numerical_one#neg, dummy_factor)]
               ~constant:numerical_zero
               ~kind:LINEAR_EQ in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq'] in
	   let _ = relax_factor_r self_r dummy_factor in
	   self#reify self_r
      | ASSIGN_NUM (v, MULT (_, _))
	| ASSIGN_NUM (v, DIV (_, _))
	| READ_NUM_ELT (v, _, _) ->
	 let self_r = self#extendAndReflect clone [v] in
	 let v_f = new numerical_factor_t v in
	 let _ = relax_factor_r self_r v_f in
	 self#reify self_r
      | INCREMENT (v, n) ->
	 let self_r = self#extendAndReflect clone [v; dummy_variable] in
	 if n#equal numerical_zero then
	   {< >}
	 else
	   let v_f = new numerical_factor_t v in
	   let eq =
             new numerical_constraint_t
               ~factors:[(numerical_one, dummy_factor); (numerical_one#neg, v_f)]
               ~constant:n
               ~kind:LINEAR_EQ in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	   let _ = relax_factor_r self_r v_f in
	   let eq' =
             new numerical_constraint_t
               ~factors:[(numerical_one, v_f); (numerical_one#neg, dummy_factor)]
               ~constant:numerical_zero
               ~kind:LINEAR_EQ in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq'] in
	   let _ = relax_factor_r self_r dummy_factor in
	   self#reify self_r
      | ASSERT TRUE ->
	 {< >}
      | ASSERT FALSE ->
	 self#mkBottom
      | ASSERT (EQ (x, y)) ->
	 if x#equal y then
	   {< >}
	 else
	   let self_r = self#extendAndReflect clone [x; y] in
	   let x_f = new numerical_factor_t x in
	   let y_f = new numerical_factor_t y in
	   let eq =
             new numerical_constraint_t
               ~factors:[(numerical_one, x_f); (numerical_one#neg, y_f)]
               ~constant:numerical_zero
               ~kind:LINEAR_EQ in
	   let _ = add_csts_r max_variable_set include_tmps self_r [eq] in
	   self#reify self_r
      | _ ->
	 {< >}
        
  method analyzeFwd = self#analyzeFwd' true
                    
  method analyzeBwd = self#analyzeBwd' true
                    
  method analyzeFwdInTransaction = self#analyzeFwd' false
                                 
  method analyzeBwdInTransaction = self#analyzeBwd' false
                                 
  method clone = self#reify (self#reflect true ())
               
  method analyzeOperation
           ~(domain_name: string)
           ~(fwd_direction: bool)
           ~(operation: operation_t): 'a =
    raise (CHFailure (LBLOCK [STR "Domain "; STR domain_name;
                              STR " does not implement operation ";
                              operation.op_name#toPretty]))

end
  

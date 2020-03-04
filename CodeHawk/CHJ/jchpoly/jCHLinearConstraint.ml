(* =============================================================================
   CodeHawk Java Analyzer
   Author: Anca Browne
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC

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

open Big_int_Z

(* chlib *)
open CHBounds
open CHIntervals
open CHLanguage
open CHNumerical
open CHPretty
open CHUtils

(* chutil *)
open CHPrettyUtil

(* jchlib *)
open JCHBasicTypes
open JCHBasicTypesAPI

(* jchpre *)
open JCHPreAPI

(* jchsys *)
open JCHSystemUtils
open JCHPrintUtils

(* jchpoly *)
open JCHNumericUtils

let dbg = ref false

let params = JCHAnalysisUtils.numeric_params 

(* The ineq is >= *) 
(* sum of a * v + cont = or >= 0 where pairs is a list (ind, a) *)
class linear_constraint_t iseq ps cnst = 
  object (self: 'a)
    val is_eq = iseq 
    val pairs = ref []
    val const = ref zero_big_int

    initializer 
      let (ps', cnst') = 
	if is_eq && (List.length ps) > 0 then
	  let (_, coeff) = List.hd ps in
	  if ge_big_int coeff zero_big_int then (ps, cnst)
	  else (List.map (fun (i, c) -> (i, minus_big_int c)) ps, minus_big_int cnst)
	else (ps, cnst) in
      let compare_pairs (i1, n1) (i2, n2) = compare i1 i2 in
      pairs := List.sort compare_pairs ps' ;
      const := cnst'

    method is_equality = is_eq

    method compare (a: 'a) = 
      let (apairs, aconst) = a#get_pairs_const in
      match (is_eq, a#is_equality) with
      |	(true, false) -> 1
      |	(false, true) -> -1
      |	 _ -> 
	  let rec compare_pairs ps1 ps2 = 
	    match (ps1, ps2) with 
	    | ([], []) -> 
		if eq_big_int !const aconst then 0
		else if gt_big_int !const aconst then 1
		else -1
	    | ([], _) -> -1
	    | (_, []) -> 1
	    | ((ind1, coeff1) :: rest_ps1, (ind2, coeff2) :: rest_ps2) -> 
		let c = compare ind1 ind2 in
		if c = 0 then 
		  if eq_big_int coeff1 coeff2 then compare_pairs rest_ps1 rest_ps2
		  else if gt_big_int coeff1 coeff2 then 1
		  else -1
		else c in
	  compare_pairs !pairs apairs

    method is_const_equality = 
      is_eq && (List.length !pairs = 1)

    method is_interval = 
      List.length !pairs = 1

    method is_1_geq_0 = 
      not is_eq && !pairs = [] && (eq_big_int !const unit_big_int)

    method is_0_geq_0 = 
      not is_eq && !pairs = [] && (eq_big_int !const zero_big_int)

    method get_pairs_const = (!pairs, !const) 

    method is_const = !pairs = []

    method is_small =
      if JCHTypeUtils.integer_interval#contains (new numerical_t !const) then
	List.for_all (fun (_, n) ->
            JCHTypeUtils.integer_interval#contains (new numerical_t n)) !pairs
      else false

    method number_pairs = List.length !pairs 

    method has_index ind = 
      List.exists (fun (i, _) -> i = ind) !pairs 

    method replace_consts ls = 
      let rest_pairs = ref [] in
      let new_const = ref !const in
      let check (ind, coeff) = 
	match List.partition (fun (i, c) -> i = ind) ls with
	|  ((_, cst) :: _, _) -> 
	    new_const := add_big_int !new_const (mult_big_int coeff cst)
	| _ -> rest_pairs := (ind, coeff) :: !rest_pairs in
      List.iter check !pairs ;
      {< pairs = rest_pairs ; const = new_const >}

    method remap map = 
      let new_pairs = List.map (fun (i, c) -> (List.assoc i map, c)) !pairs in
      new linear_constraint_t is_eq new_pairs !const

    method to_array size = 
      let a = Array.make size zero_big_int in
      a.(pred size) <- !const ;
      let set_pair (ind, c) = 
	a.(ind) <- c in
      List.iter set_pair !pairs ;
      (is_eq, a)

    method get_used_indices = List.map fst !pairs

    method get_max_and_nr_coeffs = 
      let max = ref !const in
      let add_pair (int, c) = 
	let abs_c = abs_big_int c in
	if gt_big_int abs_c !max then max := abs_c in
      List.iter add_pair !pairs ;
      (!max, List.length !pairs)

    method get_v_interval = 
      match !pairs with 
      |	[(i, coeff)] -> 
	  let int = 
	    if is_eq then
              mkSingletonInterval (mkNumerical_big !const)#neg
	    else
              new interval_t
                  (bound_of_num (mkNumerical_big !const)#neg) plus_inf_bound in
	  let coeff_int = mkSingletonInterval (mkNumerical_big coeff) in
	  Some (i, int#div coeff_int)
      |	_ ->  None

    (* Assumes is eq *)

    method private to_jterm
                     (map: (int * int) list)
                     (lc_pairs: (int * int) list)
                     (length_pairs: (int * int) list)
	             (aux_map: (int * string) list)
                     (aux_length_map: (int * string) list):jterm_t = 
      let mk_sum_op (i, c) = 
	let v = 
	  try (* v is an argument or return *)
	    let arg_ind = List.assoc i map in 
	    JLocalVar arg_ind 
	  with _ -> (* v is a loop counter *)
	    try
	      JLoopCounter (List.assoc i lc_pairs) 
	    with _ -> (* v is a length of an argument or return *)
	      try
		let array_ind = List.assoc i length_pairs in
		JSize (JLocalVar array_ind) 
	      with _ -> (* v is an auxiliary var *)
		try
		  let name = List.assoc i aux_map in
		  JAuxiliaryVar name
		with _ ->
		  let name = List.assoc i aux_length_map in
		  JSize (JAuxiliaryVar name) in
	let coeff = JConstant (mkNumerical_big c) in
	if eq_big_int c unit_big_int then
          v
	else
          JArithmeticExpr (JTimes, coeff, v) in
      let exprs = List.map mk_sum_op !pairs in
      let add_product expr_opt p = 
	match expr_opt with 
	| Some expr -> Some (JArithmeticExpr (JPlus, p, expr))
	| _ -> Some p in
      let expr = 
	let e = Option.get (List.fold_left add_product None exprs) in
	if eq_big_int !const zero_big_int then
          e
	else
          JArithmeticExpr (JPlus, e, JConstant (mkNumerical_big !const)) in
      expr
      
    method to_relational_expr
             (map: (int * int) list)
             (lc_pairs:(int * int) list)
             (length_pairs:(int * int) list)
	     (aux_map:(int * string) list)
             (aux_length_map:(int * string) list) =
      let expr = self#to_jterm map lc_pairs length_pairs aux_map aux_length_map in
      if is_eq then 
	(JEquals, expr, JConstant numerical_zero)
      else
	(JGreaterEqual, expr, JConstant numerical_zero)

    method to_pre_predicate
             (map:(int * int) list)
             (lc_pairs:(int * int) list)
             (length_pairs:(int * int) list)
	     (aux_map:(int * string) list)
             (aux_length_map:(int * string) list) =
      PreRelationalExpr
        (self#to_relational_expr map lc_pairs length_pairs aux_map aux_length_map)

    method to_post_predicate
             (map:(int * int) list)
             (lc_pairs:(int * int) list)
             (length_pairs:(int * int) list)
	     (aux_map:(int * string) list)
             (aux_length_map:(int * string) list) =
      PostRelationalExpr
        (self#to_relational_expr map lc_pairs length_pairs aux_map aux_length_map)

    method to_string = 
      let rec add_pair first str (pairs: (int * big_int) list) = 
	match pairs with 
	| (ind, c) :: rest_pairs -> 
	   if eq_big_int c zero_big_int then
             add_pair first str rest_pairs
	    else if first then 
	     add_pair
               false
               ((string_of_big_int c) ^ "v_" ^ (string_of_int ind))
               rest_pairs
	    else if gt_big_int c zero_big_int then 
	     add_pair
               false
               (str ^ " + " ^ (string_of_big_int c) ^ "v_" ^ (string_of_int ind))
               rest_pairs
	    else 
	      add_pair
                false
                (str
                 ^ " - "
                 ^ (string_of_big_int (minus_big_int c))
                 ^ "v_"
                 ^ (string_of_int ind))
                rest_pairs
	| [] -> str in
      let expr_str = 
	let str = add_pair true "" !pairs in
	if eq_big_int !const zero_big_int then
          str
	else if gt_big_int !const zero_big_int then 
	  str ^ " + " ^ (string_of_big_int !const)
	else 
	  str ^ " - " ^ (string_of_big_int (minus_big_int !const)) in
      if is_eq then
        expr_str ^ " = 0"
      else
        expr_str ^ " >= 0" 

    method to_pretty (vars: variable_t array) = 
      let pp = ref [] in
      let rec add_pair first (pairs: (int * big_int) list) = 
	match pairs with 
	| (ind, c) :: rest_pairs ->
	    let v = vars.(ind) in
	    if eq_big_int c zero_big_int then
              add_pair first rest_pairs
	    else if first then 
	      begin
		if eq_big_int c unit_big_int then
                  pp := v#toPretty :: !pp 
		else if eq_big_int c (minus_big_int unit_big_int) then
                  pp := v#toPretty :: (STR "-") :: !pp 
		else
                  pp := v#toPretty :: (STR (string_of_big_int c)) :: !pp ;
		add_pair false rest_pairs
	      end
	    else if gt_big_int c zero_big_int then 
	      begin
		if eq_big_int c unit_big_int then
                  pp := v#toPretty :: (STR " + ") :: !pp 
		else
                  pp := v#toPretty :: (STR (" + " ^ (string_of_big_int c) ^ "")) :: !pp ;
		add_pair false rest_pairs
	      end
	    else 
	      begin
		if eq_big_int c (minus_big_int unit_big_int) then
                  pp := v#toPretty :: (STR " - ") :: !pp 
		else
                  pp :=
                    v#toPretty
                    :: (STR (" - " ^ (string_of_big_int (minus_big_int c)) ^ "")) :: !pp ;
		add_pair false rest_pairs
	      end
	| [] -> pp in
      let pp = add_pair true !pairs in
      (if eq_big_int !const zero_big_int then
         ()
      else if gt_big_int !const zero_big_int then 
	pp := (STR (" + " ^ (string_of_big_int !const))) :: !pp
      else 
	pp := (STR (" - " ^ (string_of_big_int (minus_big_int !const)))) :: !pp ) ;
      (if is_eq then
         pp := (STR " = 0") :: !pp
       else
         pp := (STR " >= 0") :: !pp) ;
      LBLOCK (List.rev !pp)

    method toPretty =
      LBLOCK [STR (self#to_string)] 
  end

let mk_arg_constraint_from_rel_expr
      (name_to_index:(string * int) list)
      (index_to_types:(int * value_type_t list) list)
      (rel_expr:relational_expr_t) = 
   let rec add_to_pairs (pairs, const, is_float) coeff expr = 
     match expr with
     (* TBA: JPower (t,n), JUninterpreted (name,terms) ?? *)
    | JArithmeticExpr (JPlus, e1, e2) ->
       let (pairs1, const1, is_float1) =
         add_to_pairs (pairs, const, is_float) coeff e1 in
	add_to_pairs (pairs1, const1, is_float1) coeff e2 
    | JArithmeticExpr (JMinus, e1, e2) ->
       let (pairs1, const1, is_float1) =
         add_to_pairs (pairs, const, is_float) coeff e1 in
	add_to_pairs (pairs1, const1, is_float1) (minus_big_int coeff) e2
    | JArithmeticExpr (JTimes, JConstant num, e2) ->
	add_to_pairs (pairs, const, is_float) (mult_big_int coeff num#getNum) e2
    | JLocalVar (-1) -> 
	let index = List.assoc "return" name_to_index in
	let is_float = JCHTypeUtils.can_be_float (List.assoc index index_to_types) in
	((index, coeff) :: pairs, const, is_float)
    | JLocalVar i -> 
	let index = List.assoc ("arg" ^ (string_of_int i)) name_to_index in
	let is_float = JCHTypeUtils.can_be_float (List.assoc index index_to_types) in
	((index, coeff) :: pairs, const, is_float)
    | JConstant num -> 
	(pairs, add_big_int const (mult_big_int coeff num#getNum), false)
    | JBoolConstant true -> 
	(pairs, add_big_int const (mult_big_int coeff unit_big_int), false)
    | JBoolConstant false -> 
	(pairs, add_big_int const (mult_big_int coeff zero_big_int), false)
    | JSize (JLocalVar (-1)) -> 
	((List.assoc "length_return" name_to_index, coeff) :: pairs, const, false)
    | JSize (JLocalVar i) -> 
       ((List.assoc
           ("length_arg" ^ (string_of_int i))
           name_to_index, coeff) :: pairs, const, false)
    | JAuxiliaryVar name ->
	((List.assoc name name_to_index, coeff) :: pairs, const, false)
    | _ -> 
	raise Exit in

  let rec make_constr (re:relational_expr_t) = 
    match re with
    | (JEquals, term1, term2) -> 
       let (pairs1, const1, is_float1) =
         add_to_pairs ([], zero_big_int, false) unit_big_int term1 in
       let (pairs, const, is_float)  =
         add_to_pairs (pairs1, const1, is_float1) (minus_big_int unit_big_int) term2 in
	new linear_constraint_t true pairs const 
    | (JLessThan, term1, term2) -> 
	make_constr (JGreaterThan, term2, term1)
    | (JLessEqual, term1, term2) -> 
	make_constr (JGreaterEqual, term2, term1)
    | (JGreaterThan, term1, term2) -> 
       let (pairs1, const1, is_float1) =
         add_to_pairs ([], zero_big_int, false) unit_big_int term1 in
       let (pairs, const, is_float)  =
         add_to_pairs (pairs1, const1, is_float1) (minus_big_int unit_big_int) term2 in
	if is_float then 
	  new linear_constraint_t false pairs const 
	else 
	  new linear_constraint_t false pairs (sub_big_int const unit_big_int)
	
    | (JGreaterEqual, term1, term2) -> 
       let (pairs1, const1, is_float1) =
         add_to_pairs ([], zero_big_int, false) unit_big_int term1 in
       let (pairs, const, is_float)  =
         add_to_pairs (pairs1, const1, is_float1) (minus_big_int unit_big_int) term2 in
	new linear_constraint_t false pairs const 
    | _ -> raise Exit in
  make_constr rel_expr

let mk_arg_constraint_from_post_predicate
      (name_to_index:(string * int) list)
      (index_to_types:(int * value_type_t list) list)
      (post:postcondition_predicate_t) = 
  match post with 
  | PostRelationalExpr (op, term1, term2) -> 
     mk_arg_constraint_from_rel_expr
       name_to_index index_to_types (op, term1, term2) 
  | PostWrapped term -> 
     mk_arg_constraint_from_rel_expr
       name_to_index index_to_types (JEquals, JLocalVar (-1), term)
  | PostUnwrapped -> 
     mk_arg_constraint_from_rel_expr
       name_to_index index_to_types (JEquals, JLocalVar (-1), JLocalVar 0)
  | _ -> raise Exit    

let mk_constraints_from_interval
      (only_small:bool) (ind:int) (interval:interval_t) = 
  let constrs = ref [] in
  let is_eq = Option.is_some interval#singleton in
  begin
    match interval#getMin#getBound with 
    | NUMBER min -> 
	let c = min#neg#getNum in
	if not only_small
           || JCHAnalysisUtils.numeric_params#is_good_coefficient c then 
	  constrs := [new linear_constraint_t is_eq [(ind, unit_big_int)] c] 
    | _ -> () 
  end ;
  if not is_eq then 
    begin
      match interval#getMax#getBound with 
      | NUMBER max -> 
	  let c = max#getNum in
	  if not only_small
             || JCHAnalysisUtils.numeric_params#is_good_coefficient c then 
	    constrs :=
              (new linear_constraint_t
                   false [(ind, minus_big_int unit_big_int)] c) :: !constrs
      | _ -> () 
    end ;
  !constrs

let linear_constraint_of_array (is_eq:bool) (a:big_int array) = 
  let ncols = Array.length a in
  let nvars = pred ncols in
  let const = a.(nvars) in
  let pairs = ref [] in
  let add_pair i c = 
    if i <> nvars && not (eq_big_int c zero_big_int) then 
      pairs := (i, c) :: !pairs in
  Array.iteri add_pair a ;
  new linear_constraint_t is_eq !pairs const 

let linear_constraints_of_matrix (is_eq:bool) (m:big_int array array) = 
  let constrs = ref [] in
  for i = 0 to pred (Array.length m) do
    constrs := (linear_constraint_of_array is_eq m.(i)) :: !constrs
  done ;
  !constrs

let linear_constraints_to_matrices
      (nvars:int) (constrs:linear_constraint_t list) =
  let size = nvars + 1 in
  let (eq_constrs, ineq_constrs) = 
    let (eq_cs, ineq_cs) = 
      List.partition fst (List.map (fun c -> c#to_array size) constrs) in
    (List.map snd eq_cs, List.map snd ineq_cs) in
  let eq_nrows = List.length eq_constrs in
  let ineq_nrows = List.length ineq_constrs in
  let eq_m = Array.make_matrix eq_nrows size zero_big_int in
  let ineq_m = Array.make_matrix ineq_nrows size zero_big_int in
  let rec add_constrs m col constrs = 
    match constrs with 
    | constr :: rest_constrs -> 
	m.(col) <- constr ;
	add_constrs m (succ col) rest_constrs
    | _ -> () in
  begin
    add_constrs eq_m 0 eq_constrs ;
    add_constrs ineq_m 0 ineq_constrs ;
    (eq_m, ineq_m)
  end
